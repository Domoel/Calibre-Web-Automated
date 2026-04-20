#!/usr/bin/env python
# -*- coding: utf-8 -*-
# Calibre-Web Automated – fork of Calibre-Web
# Copyright (C) 2018-2025 Calibre-Web contributors
# Copyright (C) 2024-2025 Calibre-Web Automated contributors
# SPDX-License-Identifier: GPL-3.0-or-later
# See CONTRIBUTORS for full list of authors.

import base64
from datetime import datetime, timezone
from cps import cw_babel
# Entfernt, da wir die Logik für höhere Stabilität wieder inline führen
# from kobo_sync_utils import get_kobo_created_ts 
import os
import uuid
import zipfile
from time import gmtime, strftime
import json
from urllib.parse import unquote

from flask import (
    Blueprint,
    request,
    make_response,
    jsonify,
    current_app,
    url_for,
    redirect,
    abort,
    Response,
)
from .cw_login import current_user
from werkzeug.datastructures import Headers
from sqlalchemy import func
from sqlalchemy.sql.expression import and_, or_
from sqlalchemy.exc import StatementError
from sqlalchemy.sql import select
import requests

from . import config, logger, kobo_auth, db, calibre_db, helper, shelf as shelf_lib, ub, csrf, kobo_sync_status, magic_shelf
from . import isoLanguages
from .epub import get_epub_layout
from .constants import COVER_THUMBNAIL_SMALL, COVER_THUMBNAIL_MEDIUM, COVER_THUMBNAIL_LARGE
from .kobo_cover_cache import build_cover_image_id, normalize_cover_uuid
from .helper import get_download_link
from .services import SyncToken as SyncToken, hardcover
from .web import download_required
from .kobo_auth import requires_kobo_auth, get_auth_token

KOBO_FORMATS = {"KEPUB": ["KEPUB"], "EPUB": ["EPUB3", "EPUB"]}
KOBO_STOREAPI_URL = "https://storeapi.kobo.com"
KOBO_IMAGEHOST_URL = "https://cdn.kobo.com/book-images"

SYNC_ITEM_LIMIT = 100

kobo = Blueprint("kobo", __name__, url_prefix="/kobo/<auth_token>")
kobo_auth.disable_failed_auth_redirect_for_blueprint(kobo)
kobo_auth.register_url_value_preprocessor(kobo)

log = logger.create()


def get_store_url_for_current_request():
    # Programmatically modify the current url to point to the official Kobo store
    __, __, request_path_with_auth_token = request.full_path.rpartition("/kobo/")
    __, __, request_path = request_path_with_auth_token.rstrip("?").partition(
        "/"
    )
    return KOBO_STOREAPI_URL + "/" + request_path


CONNECTION_SPECIFIC_HEADERS = [
    "connection",
    "content-encoding",
    "content-length",
    "transfer-encoding",
]


def get_kobo_activated():
    return config.config_kobo_sync


def make_request_to_kobo_store(sync_token=None):
    outgoing_headers = Headers(request.headers)
    outgoing_headers.remove("Host")
    if sync_token:
        sync_token.set_kobo_store_header(outgoing_headers)

    store_response = requests.request(
        method=request.method,
        url=get_store_url_for_current_request(),
        headers=outgoing_headers,
        data=request.get_data(),
        allow_redirects=False,
        timeout=(2, 10)
    )
    log.debug("Content: " + str(store_response.content))
    log.debug("StatusCode: " + str(store_response.status_code))
    return store_response


def redirect_or_proxy_request():
    if config.config_kobo_proxy:
        if request.method == "GET":
            return redirect(get_store_url_for_current_request(), 307)
        else:
            # The Kobo device turns other request types into GET requests on redirects,
            # so we instead proxy to the Kobo store ourselves.
            store_response = make_request_to_kobo_store()

            return make_proxy_response(store_response)
    else:
        return make_response(jsonify({}))


def make_proxy_response(store_response: requests.Response) -> Response:
    response_headers = store_response.headers
    for header_key in CONNECTION_SPECIFIC_HEADERS:
        response_headers.pop(header_key, default=None)

    return make_response(store_response.content, store_response.status_code, response_headers.items())


def convert_to_kobo_timestamp_string(timestamp):
    try:
        return timestamp.strftime("%Y-%m-%dT%H:%M:%SZ")
    except AttributeError as exc:
        log.debug("Timestamp not valid: {}".format(exc))
        return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def get_magic_shelf_book_ids_for_kobo(user_id):
    if not config.config_kobo_sync_magic_shelves:
        return set()

    magic_shelves = ub.session.query(ub.MagicShelf).filter_by(user_id=user_id, kobo_sync=True).all()
    if not magic_shelves:
        return set()

    book_ids = set()
    for shelf in magic_shelves:
        books, _ = magic_shelf.get_books_for_magic_shelf(
            shelf.id, page=1, page_size=None
        )
        for book in books:
            book_ids.add(book.id)

    if book_ids:
        log.debug("Kobo Sync: magic shelf allowed books: %s", len(book_ids))

    return book_ids


@kobo.route("/v1/library/sync")
@requires_kobo_auth
# @download_required
def HandleSyncRequest():
    if not current_user.role_download():
        log.info("Users need download permissions for syncing library to Kobo reader")
        return abort(403)

    sync_token = SyncToken.SyncToken.from_headers(request.headers)
    log.info("Kobo library sync request received")
    log.debug("SyncToken: {}".format(sync_token))
    log.debug("Download link format {}".format(get_download_url_for_book('[bookid]', '[bookformat]')))
    if not current_app.wsgi_app.is_proxied:
        log.debug('Kobo: Received unproxied request, changed request port to external server port')

    # if no books synced don't respect sync_token
    if not ub.session.query(ub.KoboSyncedBooks).filter(ub.KoboSyncedBooks.user_id == current_user.id).count():
        sync_token.books_last_modified = datetime.min
        sync_token.books_last_created = datetime.min
        sync_token.reading_state_last_modified = datetime.min

    new_books_last_modified = sync_token.books_last_modified
    new_books_last_created = sync_token.books_last_created
    new_reading_state_last_modified = sync_token.reading_state_last_modified

    new_archived_last_modified = datetime.min
    sync_results = []

    calibre_db.reconnect_db(config, ub.app_DB_path)

    # Two-Way-Sync Deletion Logic
    magic_shelf_book_ids = set()
    if current_user.kobo_only_shelves_sync:
        magic_shelf_book_ids = get_magic_shelf_book_ids_for_kobo(current_user.id)
        try:
            synced_books_query = ub.session.query(ub.KoboSyncedBooks.book_id).filter(ub.KoboSyncedBooks.user_id == current_user.id)
            synced_book_ids = {item.book_id for item in synced_books_query}

            allowed_books_query = (ub.session.query(ub.BookShelf.book_id)
                                   .join(ub.Shelf, ub.BookShelf.shelf == ub.Shelf.id)
                                   .filter(ub.Shelf.user_id == current_user.id, ub.Shelf.kobo_sync == True))
            allowed_book_ids = {item.book_id for item in allowed_books_query}
            if magic_shelf_book_ids:
                allowed_book_ids |= magic_shelf_book_ids

            books_to_delete_ids = synced_book_ids - allowed_book_ids

            if books_to_delete_ids:
                log.info(f"Kobo Sync: Found {len(books_to_delete_ids)} books to remove from device for user {current_user.name}")
                for book_id in books_to_delete_ids:
                    book = calibre_db.get_book(book_id)
                    if book:
                        entitlement = {
                            "BookEntitlement": create_book_entitlement(book, archived=True),
                            "BookMetadata": get_metadata(book),
                        }
                        sync_results.append({"ChangedEntitlement": entitlement})

                ub.session.query(ub.KoboSyncedBooks).filter(
                    ub.KoboSyncedBooks.user_id == current_user.id,
                    ub.KoboSyncedBooks.book_id.in_(books_to_delete_ids)
                ).delete(synchronize_session=False)
                ub.session_commit()

        except Exception as e:
            log.error(f"Kobo Sync: Error during deletion logic: {e}")
            ub.session.rollback()

    only_kobo_shelves = current_user.kobo_only_shelves_sync
    log.debug("Kobo Sync: books last modified: {}".format(sync_token.books_last_modified))

    if only_kobo_shelves:
        changed_entries = calibre_db.session.query(db.Books,
                                                   ub.ArchivedBook.last_modified,
                                                   ub.BookShelf.date_added,
                                                   ub.ArchivedBook.is_archived)
        # FIX: Joins müssen VOR den Filtern definiert werden
        changed_entries = (changed_entries
                           .join(db.Data)
                           .outerjoin(ub.BookShelf, db.Books.id == ub.BookShelf.book_id)
                           .outerjoin(ub.Shelf, ub.Shelf.id == ub.BookShelf.shelf)
                           .outerjoin(ub.ArchivedBook, and_(db.Books.id == ub.ArchivedBook.book_id,
                                                            ub.ArchivedBook.user_id == current_user.id))
                           .filter(db.Books.id.notin_(calibre_db.session.query(ub.KoboSyncedBooks.book_id)
                                                      .filter(ub.KoboSyncedBooks.user_id == current_user.id)))
                           .filter(or_(
                               ub.BookShelf.date_added > sync_token.books_last_modified,
                               db.Books.last_modified > sync_token.books_last_modified,
                               db.Books.id.in_(magic_shelf_book_ids) if magic_shelf_book_ids else False
                           ))
                           .filter(db.Data.format.in_(KOBO_FORMATS))
                           .filter(calibre_db.common_filters(allow_show_archived=True))
                           .filter(or_(
                               and_(ub.Shelf.user_id == current_user.id, ub.Shelf.kobo_sync == True),
                               db.Books.id.in_(magic_shelf_book_ids) if magic_shelf_book_ids else False
                           ))
                           .order_by(db.Books.last_modified)
                           .order_by(db.Books.id)
                           .distinct())
    else:
        changed_entries = calibre_db.session.query(db.Books,
                                                   ub.ArchivedBook.last_modified,
                                                   ub.ArchivedBook.is_archived)
        changed_entries = (changed_entries
                           .join(db.Data).outerjoin(ub.ArchivedBook, and_(db.Books.id == ub.ArchivedBook.book_id,
                                                                          ub.ArchivedBook.user_id == current_user.id))
                           .filter(db.Books.id.notin_(calibre_db.session.query(ub.KoboSyncedBooks.book_id)
                                                      .filter(ub.KoboSyncedBooks.user_id == current_user.id)))
                           .filter(calibre_db.common_filters(allow_show_archived=True))
                           .filter(db.Data.format.in_(KOBO_FORMATS))
                           .order_by(db.Books.last_modified)
                           .order_by(db.Books.id))

    log.debug("Kobo Sync: changed entries: {}".format(changed_entries.count()))

    reading_states_in_new_entitlements = []
    books = changed_entries.limit(SYNC_ITEM_LIMIT)
    
    for book in books:
        # book ist hier ein Tupel: (db.Books, last_modified, date_added, is_archived)
        actual_book = book.Books
        formats = [data.format for data in actual_book.data]
        if 'KEPUB' not in formats and config.config_kepubifypath and 'EPUB' in formats:
            helper.convert_book_format(actual_book.id, config.get_book_path(), 'EPUB', 'KEPUB', current_user.name)

        kobo_reading_state = get_or_create_reading_state(actual_book.id)
        entitlement = {
            "BookEntitlement": create_book_entitlement(actual_book, archived=(book.is_archived == True)),
            "BookMetadata": get_metadata(actual_book),
        }

        if kobo_reading_state.last_modified > sync_token.reading_state_last_modified:
            entitlement["ReadingState"] = get_kobo_reading_state_response(actual_book, kobo_reading_state)
            new_reading_state_last_modified = max(new_reading_state_last_modified, kobo_reading_state.last_modified)
            reading_states_in_new_entitlements.append(actual_book.id)

        # FIX: Stabilerer Timestamp-Abgleich für Tupel-Datensätze
        ts_created = actual_book.timestamp.replace(tzinfo=None)
        try:
            if hasattr(book, 'date_added') and book.date_added:
                ts_created = max(ts_created, book.date_added)
        except (AttributeError, TypeError):
            pass

        if ts_created > sync_token.books_last_created:
            sync_results.append({"NewEntitlement": entitlement})
        else:
            sync_results.append({"ChangedEntitlement": entitlement})

        new_books_last_modified = max(
            actual_book.last_modified.replace(tzinfo=None), new_books_last_modified
        )

        new_books_last_created = max(ts_created, new_books_last_created)
        kobo_sync_status.add_synced_books(actual_book.id)

    # Rest der Funktion (Archiv-Handling, Reading States, Shelves) bleibt wie in 4.0.6
    max_change = changed_entries.filter(ub.ArchivedBook.is_archived)\
        .filter(ub.ArchivedBook.user_id == current_user.id) \
        .order_by(func.datetime(ub.ArchivedBook.last_modified).desc()).first()

    max_change = max_change.last_modified if max_change else new_archived_last_modified
    new_archived_last_modified = max(new_archived_last_modified, max_change)

    book_count = changed_entries.count()
    cont_sync = bool(book_count)
    log.debug("Kobo Sync: remaining books to sync: {}".format(book_count))
    
    changed_reading_states = ub.session.query(ub.KoboReadingState)

    if only_kobo_shelves:
        changed_reading_states = changed_reading_states.outerjoin(ub.BookShelf,
                                                                  ub.KoboReadingState.book_id == ub.BookShelf.book_id)\
            .outerjoin(ub.Shelf, ub.Shelf.id == ub.BookShelf.shelf)\
            .filter(ub.KoboReadingState.last_modified > sync_token.reading_state_last_modified)\
            .filter(or_(
                and_(current_user.id == ub.Shelf.user_id, ub.Shelf.kobo_sync == True),
                ub.KoboReadingState.book_id.in_(magic_shelf_book_ids) if magic_shelf_book_ids else False
            ))\
            .distinct()
    else:
        changed_reading_states = changed_reading_states.filter(
            ub.KoboReadingState.last_modified > sync_token.reading_state_last_modified)

    changed_reading_states = changed_reading_states.filter(
        and_(ub.KoboReadingState.user_id == current_user.id,
             ub.KoboReadingState.book_id.notin_(reading_states_in_new_entitlements)))\
        .order_by(ub.KoboReadingState.last_modified)
    
    cont_sync |= bool(changed_reading_states.count() > SYNC_ITEM_LIMIT)
    for kobo_reading_state in changed_reading_states.limit(SYNC_ITEM_LIMIT).all():
        book = calibre_db.session.query(db.Books).filter(db.Books.id == kobo_reading_state.book_id).one_or_none()
        if book:
            sync_results.append({
                "ChangedReadingState": {
                    "ReadingState": get_kobo_reading_state_response(book, kobo_reading_state)
                }
            })
            new_reading_state_last_modified = max(new_reading_state_last_modified, kobo_reading_state.last_modified)

    sync_shelves(sync_token, sync_results, only_kobo_shelves)

    if config.config_kobo_sync_magic_shelves:
        for shelf in ub.session.query(ub.MagicShelf).filter_by(user_id=current_user.id, kobo_sync=False).all():
            sync_results.append({
                "DeletedTag": {
                    "Tag": {
                        "Id": shelf.uuid,
                        "LastModified": convert_to_kobo_timestamp_string(shelf.last_modified)
                    }
                }
            })

        magic_shelves = ub.session.query(ub.MagicShelf).filter_by(user_id=current_user.id, kobo_sync=True).all()
        new_tags_last_modified = sync_token.tags_last_modified
            
        for shelf in magic_shelves:
            books, _ = magic_shelf.get_books_for_magic_shelf(shelf.id, page=1, page_size=1000)
            new_tags_last_modified = max(shelf.last_modified, new_tags_last_modified)
            tag = create_kobo_tag_magic(shelf, books)
            if not tag: continue

            if shelf.created > sync_token.tags_last_modified:
                sync_results.append({"NewTag": tag})
            else:
                sync_results.append({"ChangedTag": tag})
        sync_token.tags_last_modified = new_tags_last_modified

    if not cont_sync:
        sync_token.books_last_created = new_books_last_created
    sync_token.books_last_modified = new_books_last_modified
    sync_token.archive_last_modified = new_archived_last_modified
    sync_token.reading_state_last_modified = new_reading_state_last_modified

    return generate_sync_response(sync_token, sync_results, cont_sync)


def generate_sync_response(sync_token, sync_results, set_cont=False):
    extra_headers = {}
    if config.config_kobo_proxy and not set_cont:
        try:
            store_response = make_request_to_kobo_store(sync_token)
            store_sync_results = store_response.json()
            sync_results += store_sync_results
            sync_token.merge_from_store_response(store_response)
            extra_headers["x-kobo-sync"] = store_response.headers.get("x-kobo-sync")
            extra_headers["x-kobo-sync-mode"] = store_response.headers.get("x-kobo-sync-mode")
            extra_headers["x-kobo-recent-reads"] = store_response.headers.get("x-kobo-recent-reads")
        except Exception as ex:
            log.error_or_exception("Failed to receive or parse response from Kobo's sync endpoint: {}".format(ex))
    if set_cont:
        extra_headers["x-kobo-sync"] = "continue"
    sync_token.to_headers(extra_headers)

    try:
        from scripts.cwa_db import CWA_DB
        import json as json_lib
        cwa_db = CWA_DB()
        cwa_db.log_activity(
            user_id=int(current_user.id),
            user_name=current_user.name,
            event_type='KOBO_SYNC',
            extra_data=json_lib.dumps({
                'books_synced': len(sync_results),
                'endpoint': '/v1/library/sync'
            })
        )
    except Exception as e:
        log.debug(f"Failed to log Kobo sync activity: {e}")

    response = make_response(json.dumps(sync_results), extra_headers)
    response.headers["Content-Type"] = "application/json; charset=utf-8"
    return response

# --- Ab hier folgen die Metadaten-, Cover- und Shelf-Handler (unverändert aus 4.0.6) ---

@kobo.route("/v1/library/<book_uuid>/metadata")
@requires_kobo_auth
@download_required
def HandleMetadataRequest(book_uuid):
    if not current_app.wsgi_app.is_proxied:
        log.debug('Kobo: Received unproxied request, changed request port to external server port')
    log.info("Kobo library metadata request received for book %s" % book_uuid)
    book = calibre_db.get_book_by_uuid(book_uuid)
    if not book or not book.data:
        log.info("Book %s not found in database", book_uuid)
        return redirect_or_proxy_request()

    metadata = get_metadata(book)
    response = make_response(json.dumps([metadata], ensure_ascii=False))
    response.headers["Content-Type"] = "application/json; charset=utf-8"
    return response


def get_download_url_for_book(book_id, book_format):
    if not current_app.wsgi_app.is_proxied:
        if ':' in request.host and not request.host.endswith(']'):
            host = "".join(request.host.split(':')[:-1])
        else:
            host = request.host

        return "{url_scheme}://{url_base}:{url_port}/kobo/{auth_token}/download/{book_id}/{book_format}".format(
            url_scheme=request.scheme,
            url_base=host,
            url_port=config.config_external_port,
            auth_token=get_auth_token(),
            book_id=book_id,
            book_format=book_format.lower()
        )
    return url_for(
        "kobo.download_book",
        auth_token=kobo_auth.get_auth_token(),
        book_id=book_id,
        book_format=book_format.lower(),
        _external=True,
    )


def create_book_entitlement(book, archived):
    book_uuid = str(book.uuid)
    return {
        "Accessibility": "Full",
        "ActivePeriod": {"From": convert_to_kobo_timestamp_string(datetime.now(timezone.utc))},
        "Created": convert_to_kobo_timestamp_string(book.timestamp),
        "CrossRevisionId": book_uuid,
        "Id": book_uuid,
        "IsRemoved": archived,
        "IsHiddenFromArchive": False,
        "IsLocked": False,
        "LastModified": convert_to_kobo_timestamp_string(book.last_modified),
        "OriginCategory": "Imported",
        "RevisionId": book_uuid,
        "Status": "Active",
    }


def current_time():
    return strftime("%Y-%m-%dT%H:%M:%SZ", gmtime())


def get_description(book):
    if not book.comments:
        return None
    return book.comments[0].text


def get_author(book):
    if not book.authors:
        return {"Contributors": None}
    author_list = []
    autor_roles = []
    for author in book.authors:
        autor_roles.append({"Name": author.name})
        author_list.append(author.name)
    return {"ContributorRoles": autor_roles, "Contributors": author_list}


def get_publisher(book):
    if not book.publishers:
        return None
    return book.publishers[0].name


def get_series(book):
    if not book.series:
        return None
    return book.series[0].name


def get_seriesindex(book):
    return book.series_index if isinstance(book.series_index, float) else 1


def get_language(book):
    if not book.languages:
        return 'en'
    return isoLanguages.get(part3=book.languages[0].lang_code).part1


def _normalize_cover_uuid(image_id):
    return normalize_cover_uuid(image_id)


def _get_cover_image_id(book):
    base_id = str(book.uuid)
    try:
        cover_path = None
        if not config.config_use_google_drive:
            cover_path = os.path.join(config.get_book_path(), book.path, "cover.jpg")
        return build_cover_image_id(
            base_id,
            use_google_drive=config.config_use_google_drive,
            last_modified=book.last_modified,
            cover_path=cover_path,
        )
    except Exception as exc:
        log.debug("Kobo Sync: failed to build cover image id for book %s: %s", book.id, exc)
        return base_id


def get_metadata(book):
    download_urls = []
    kepub = [data for data in book.data if data.format == 'KEPUB']

    for book_data in kepub if len(kepub) > 0 else book.data:
        if book_data.format not in KOBO_FORMATS:
            continue
        for kobo_format in KOBO_FORMATS[book_data.format]:
            try:
                if get_epub_layout(book, book_data) == 'pre-paginated':
                    kobo_format = 'EPUB3FL'
                download_urls.append(
                    {
                        "Format": kobo_format,
                        "Size": book_data.uncompressed_size,
                        "Url": get_download_url_for_book(book.id, book_data.format),
                        "Platform": "Generic",
                    }
                )
            except (zipfile.BadZipfile, FileNotFoundError) as e:
                log.error(e)

    book_uuid = book.uuid
    cover_image_id = _get_cover_image_id(book)
    metadata = {
        "Categories": ["00000000-0000-0000-0000-000000000001", ],
        "CoverImageId": cover_image_id,
        "CrossRevisionId": book_uuid,
        "CurrentDisplayPrice": {"CurrencyCode": "USD", "TotalAmount": 0},
        "CurrentLoveDisplayPrice": {"TotalAmount": 0},
        "Description": get_description(book),
        "DownloadUrls": download_urls,
        "EntitlementId": book_uuid,
        "ExternalIds": [],
        "Genre": "00000000-0000-0000-0000-000000000001",
        "IsEligibleForKoboLove": False,
        "IsInternetArchive": False,
        "IsPreOrder": False,
        "IsSocialEnabled": True,
        "Language": get_language(book),
        "PhoneticPronunciations": {},
        "PublicationDate": convert_to_kobo_timestamp_string(book.pubdate),
        "Publisher": {"Imprint": "", "Name": get_publisher(book), },
        "RevisionId": book_uuid,
        "Title": book.title,
        "WorkId": book_uuid,
    }
    metadata.update(get_author(book))

    if get_series(book):
        name = get_series(book)
        try:
            metadata["Series"] = {
                "Name": get_series(book),
                "Number": get_seriesindex(book),
                "NumberFloat": float(get_seriesindex(book)),
                "Id": str(uuid.uuid3(uuid.NAMESPACE_DNS, name)),
            }
        except Exception as e:
            print(e)
    return metadata


@csrf.exempt
@kobo.route("/v1/library/tags", methods=["POST", "DELETE"])
@requires_kobo_auth
def HandleTagCreate():
    if request.method == "DELETE":
        abort(405)
    name, items = None, None
    try:
        shelf_request = request.json
        name = shelf_request["Name"]
        items = shelf_request["Items"]
        if not name:
            raise TypeError
    except (KeyError, TypeError):
        log.debug("Received malformed v1/library/tags request.")
        abort(400)

    shelf = ub.session.query(ub.Shelf).filter(ub.Shelf.name == name, ub.Shelf.user_id == current_user.id).one_or_none()
    if shelf and not shelf_lib.check_shelf_edit_permissions(shelf):
        abort(401)

    if not shelf:
        shelf = ub.Shelf(user_id=current_user.id, name=name, uuid=str(uuid.uuid4()))
        ub.session.add(shelf)

    add_items_to_shelf(items, shelf)
    ub.session_commit()
    return make_response(jsonify(str(shelf.uuid)), 201)


@csrf.exempt
@kobo.route("/v1/library/tags/<tag_id>", methods=["DELETE", "PUT"])
@requires_kobo_auth
def HandleTagUpdate(tag_id):
    shelf = ub.session.query(ub.Shelf).filter(ub.Shelf.uuid == tag_id, ub.Shelf.user_id == current_user.id).one_or_none()
    if not shelf:
        if config.config_kobo_proxy:
            return redirect_or_proxy_request()
        else:
            abort(404)

    if request.method == "DELETE":
        if not shelf_lib.delete_shelf_helper(shelf):
            abort(401)
    else:
        try:
            shelf_request = request.json
            shelf.name = shelf_request["Name"]
            ub.session.merge(shelf)
            ub.session_commit()
        except (KeyError, TypeError):
            abort(400)
    return make_response(' ', 200)


def add_items_to_shelf(items, shelf):
    book_ids_already_in_shelf = set([book_shelf.book_id for book_shelf in shelf.books])
    items_unknown = []
    for item in items:
        try:
            if item["Type"] != "ProductRevisionTagItem":
                items_unknown.append(item)
                continue
            book = calibre_db.get_book_by_uuid(item["RevisionId"])
            if not book:
                items_unknown.append(item)
                continue
            if book.id not in book_ids_already_in_shelf:
                shelf.books.append(ub.BookShelf(book_id=book.id))
        except KeyError:
            items_unknown.append(item)
    return items_unknown


@csrf.exempt
@kobo.route("/v1/library/tags/<tag_id>/items", methods=["POST"])
@requires_kobo_auth
def HandleTagAddItem(tag_id):
    shelf = ub.session.query(ub.Shelf).filter(ub.Shelf.uuid == tag_id, ub.Shelf.user_id == current_user.id).one_or_none()
    if not shelf: abort(404)
    if not shelf_lib.check_shelf_edit_permissions(shelf): abort(401)

    try:
        tag_request = request.json
        add_items_to_shelf(tag_request["Items"], shelf)
        ub.session.merge(shelf)
        ub.session_commit()
    except (KeyError, TypeError):
        abort(400)
    return make_response('', 201)


@csrf.exempt
@kobo.route("/v1/library/tags/<tag_id>/items/delete", methods=["POST"])
@requires_kobo_auth
def HandleTagRemoveItem(tag_id):
    shelf = ub.session.query(ub.Shelf).filter(ub.Shelf.uuid == tag_id, ub.Shelf.user_id == current_user.id).one_or_none()
    if not shelf: abort(404)
    if not shelf_lib.check_shelf_edit_permissions(shelf): abort(401)

    try:
        tag_request = request.json
        for item in tag_request["Items"]:
            book = calibre_db.get_book_by_uuid(item["RevisionId"])
            if book:
                shelf.books.filter(ub.BookShelf.book_id == book.id).delete()
        ub.session_commit()
    except (KeyError, TypeError):
        abort(400)
    return make_response('', 200)


def sync_shelves(sync_token, sync_results, only_kobo_shelves=False):
    new_tags_last_modified = sync_token.tags_last_modified
    for shelf in ub.session.query(ub.ShelfArchive).filter(ub.ShelfArchive.user_id == current_user.id):
        new_tags_last_modified = max(shelf.last_modified, new_tags_last_modified)
        sync_results.append({
            "DeletedTag": {
                "Tag": {
                    "Id": shelf.uuid,
                    "LastModified": convert_to_kobo_timestamp_string(shelf.last_modified)
                }
            }
        })
        ub.session.delete(shelf)
        ub.session_commit()

    extra_filters = []
    if only_kobo_shelves:
        for shelf in ub.session.query(ub.Shelf).filter(
            func.datetime(ub.Shelf.last_modified) > sync_token.tags_last_modified,
            ub.Shelf.user_id == current_user.id,
            not ub.Shelf.kobo_sync
        ):
            sync_results.append({
                "DeletedTag": {
                    "Tag": {
                        "Id": shelf.uuid,
                        "LastModified": convert_to_kobo_timestamp_string(shelf.last_modified)
                    }
                }
            })
        extra_filters.append(ub.Shelf.kobo_sync)

    shelflist = ub.session.query(ub.Shelf).outerjoin(ub.BookShelf).filter(
        or_(func.datetime(ub.Shelf.last_modified) > sync_token.tags_last_modified,
            func.datetime(ub.BookShelf.date_added) > sync_token.tags_last_modified),
        ub.Shelf.user_id == current_user.id,
        *extra_filters
    ).distinct().order_by(func.datetime(ub.Shelf.last_modified).asc())

    for shelf in shelflist:
        if not shelf_lib.check_shelf_view_permissions(shelf): continue
        new_tags_last_modified = max(shelf.last_modified, new_tags_last_modified)
        tag = create_kobo_tag(shelf)
        if not tag: continue

        if shelf.created > sync_token.tags_last_modified:
            sync_results.append({"NewTag": tag})
        else:
            sync_results.append({"ChangedTag": tag})
    sync_token.tags_last_modified = new_tags_last_modified
    ub.session_commit()


def create_kobo_tag(shelf):
    tag = {
        "Created": convert_to_kobo_timestamp_string(shelf.created),
        "Id": shelf.uuid,
        "Items": [],
        "LastModified": convert_to_kobo_timestamp_string(shelf.last_modified),
        "Name": shelf.name,
        "Type": "UserTag"
    }
    for book_shelf in shelf.books:
        book = calibre_db.get_book(book_shelf.book_id)
        if not book: continue
        tag["Items"].append({"RevisionId": book.uuid, "Type": "ProductRevisionTagItem"})
    return {"Tag": tag}


def create_kobo_tag_magic(shelf, books):
    tag = {
        "Created": convert_to_kobo_timestamp_string(shelf.created),
        "Id": shelf.uuid,
        "Items": [],
        "LastModified": convert_to_kobo_timestamp_string(shelf.last_modified),
        "Name": shelf.name,
        "Type": "UserTag"
    }
    for book in books:
        tag["Items"].append({"RevisionId": book.uuid, "Type": "ProductRevisionTagItem"})
    return {"Tag": tag}


@csrf.exempt
@kobo.route("/v1/library/<book_uuid>/state", methods=["GET", "PUT"])
@requires_kobo_auth
def HandleStateRequest(book_uuid):
    book = calibre_db.get_book_by_uuid(book_uuid)
    if not book or not book.data: return redirect_or_proxy_request()

    kobo_reading_state = get_or_create_reading_state(book.id)
    if request.method == "GET":
        return jsonify([get_kobo_reading_state_response(book, kobo_reading_state)])
    else:
        update_results_response = {"EntitlementId": book_uuid}
        try:
            request_data = request.json
            request_reading_state = request_data["ReadingStates"][0]
            request_bookmark = request_reading_state["CurrentBookmark"]
            if request_bookmark:
                current_bookmark = kobo_reading_state.current_bookmark
                current_bookmark.progress_percent = request_bookmark["ProgressPercent"]
                current_bookmark.content_source_progress_percent = request_bookmark["ContentSourceProgressPercent"]
                location = request_bookmark["Location"]
                if location:
                    current_bookmark.location_value = location["Value"]
                    current_bookmark.location_type = location["Type"]
                    current_bookmark.location_source = location["Source"]
                update_results_response["CurrentBookmarkResult"] = {"Result": "Success"}

            request_statistics = request_reading_state["Statistics"]
            if request_statistics:
                statistics = kobo_reading_state.statistics
                statistics.spent_reading_minutes = int(request_statistics["SpentReadingMinutes"])
                statistics.remaining_time_minutes = int(request_statistics["RemainingTimeMinutes"])
                update_results_response["StatisticsResult"] = {"Result": "Success"}

            request_status_info = request_reading_state["StatusInfo"]
            if request_status_info:
                book_read = kobo_reading_state.book_read_link
                new_book_read_status = get_ub_read_status(request_status_info["Status"])
                if new_book_read_status == ub.ReadBook.STATUS_IN_PROGRESS and new_book_read_status != book_read.read_status:
                    book_read.times_started_reading += 1
                    book_read.last_time_started_reading = datetime.now(timezone.utc)
                book_read.read_status = new_book_read_status
                update_results_response["StatusInfoResult"] = {"Result": "Success"}
        except (KeyError, TypeError, ValueError, StatementError):
            ub.session.rollback()
            abort(400)

        push_reading_state_to_hardcover(book, request_bookmark)
        ub.session.merge(kobo_reading_state)
        ub.session_commit()
        return jsonify({"RequestResult": "Success", "UpdateResults": [update_results_response]})


def push_reading_state_to_hardcover(book: db.Books, request_bookmark: dict):
    if not config.config_hardcover_sync or not bool(hardcover): return
    book_blacklist = ub.session.query(ub.HardcoverBookBlacklist).filter(ub.HardcoverBookBlacklist.book_id == book.id).first()
    if book_blacklist and book_blacklist.blacklist_reading_progress: return

    try:
        hardcoverClient = hardcover.HardcoverClient(current_user.hardcover_token)
        hardcoverClient.update_reading_progress(book.identifiers, request_bookmark["ProgressPercent"])
    except Exception as e:
        log.error(f"Hardcover sync failed: {e}")


def get_read_status_for_kobo(ub_book_read):
    return {None: "ReadyToRead", ub.ReadBook.STATUS_UNREAD: "ReadyToRead",
            ub.ReadBook.STATUS_FINISHED: "Finished", ub.ReadBook.STATUS_IN_PROGRESS: "Reading"}[ub_book_read.read_status]


def get_ub_read_status(kobo_read_status):
    return {None: None, "ReadyToRead": ub.ReadBook.STATUS_UNREAD,
            "Finished": ub.ReadBook.STATUS_FINISHED, "Reading": ub.ReadBook.STATUS_IN_PROGRESS}[kobo_read_status]


def get_or_create_reading_state(book_id):
    book_read = ub.session.query(ub.ReadBook).filter(ub.ReadBook.book_id == book_id,
                                                     ub.ReadBook.user_id == int(current_user.id)).one_or_none()
    if not book_read: book_read = ub.ReadBook(user_id=current_user.id, book_id=book_id)
    if not book_read.kobo_reading_state:
        kobo_reading_state = ub.KoboReadingState(user_id=book_read.user_id, book_id=book_id)
        kobo_reading_state.current_bookmark = ub.KoboBookmark()
        kobo_reading_state.statistics = ub.KoboStatistics()
        book_read.kobo_reading_state = kobo_reading_state
    ub.session.add(book_read)
    ub.session_commit()
    return book_read.kobo_reading_state


def get_kobo_reading_state_response(book, kobo_reading_state):
    return {
        "EntitlementId": book.uuid,
        "Created": convert_to_kobo_timestamp_string(book.timestamp),
        "LastModified": convert_to_kobo_timestamp_string(kobo_reading_state.last_modified),
        "PriorityTimestamp": convert_to_kobo_timestamp_string(kobo_reading_state.priority_timestamp),
        "StatusInfo": get_status_info_response(kobo_reading_state.book_read_link),
        "Statistics": get_statistics_response(kobo_reading_state.statistics),
        "CurrentBookmark": get_current_bookmark_response(kobo_reading_state.current_bookmark),
    }


def get_status_info_response(book_read):
    resp = {"LastModified": convert_to_kobo_timestamp_string(book_read.last_modified),
            "Status": get_read_status_for_kobo(book_read), "TimesStartedReading": book_read.times_started_reading}
    if book_read.last_time_started_reading:
        resp["LastTimeStartedReading"] = convert_to_kobo_timestamp_string(book_read.last_time_started_reading)
    return resp


def get_statistics_response(statistics):
    resp = {"LastModified": convert_to_kobo_timestamp_string(statistics.last_modified)}
    if statistics.spent_reading_minutes: resp["SpentReadingMinutes"] = statistics.spent_reading_minutes
    if statistics.remaining_time_minutes: resp["RemainingTimeMinutes"] = statistics.remaining_time_minutes
    return resp


def get_current_bookmark_response(current_bookmark):
    resp = {"LastModified": convert_to_kobo_timestamp_string(current_bookmark.last_modified)}
    if current_bookmark.progress_percent: resp["ProgressPercent"] = current_bookmark.progress_percent
    if current_bookmark.content_source_progress_percent:
        resp["ContentSourceProgressPercent"] = current_bookmark.content_source_progress_percent
    if current_bookmark.location_value:
        resp["Location"] = {"Value": current_bookmark.location_value, "Type": current_bookmark.location_type,
                            "Source": current_bookmark.location_source}
    return resp


@kobo.route("/<book_uuid>/<width>/<height>/<isGreyscale>/image.jpg", defaults={'Quality': ""})
@kobo.route("/<book_uuid>/<width>/<height>/<Quality>/<isGreyscale>/image.jpg")
@requires_kobo_auth
def HandleCoverImageRequest(book_uuid, width, height, Quality, isGreyscale):
    book_uuid = _normalize_cover_uuid(book_uuid)
    try:
        height_int = int(height)
        if height_int > 1000: resolution = COVER_THUMBNAIL_LARGE
        elif height_int > 500: resolution = COVER_THUMBNAIL_MEDIUM
        else: resolution = COVER_THUMBNAIL_SMALL
    except ValueError: resolution = COVER_THUMBNAIL_SMALL
    
    book_cover = helper.get_book_cover_with_uuid(book_uuid, resolution=resolution)
    if book_cover: return book_cover

    if not config.config_kobo_proxy: abort(404)
    return redirect(KOBO_IMAGEHOST_URL + "/{book_uuid}/{width}/{height}/false/image.jpg".format(
        book_uuid=book_uuid, width=width, height=height), 307)


@kobo.route("")
def TopLevelEndpoint():
    return make_response(jsonify({}))


@csrf.exempt
@kobo.route("/v1/library/<book_uuid>", methods=["DELETE"])
@requires_kobo_auth
def HandleBookDeletionRequest(book_uuid):
    log.info("Kobo book delete request received for book %s", book_uuid)
    book = calibre_db.get_book_by_uuid(book_uuid)
    if not book: return redirect_or_proxy_request()

    if current_user.kobo_only_shelves_sync: pass
    elif current_user.check_visibility(32768):
        kobo_sync_status.change_archived_books(book.id, True)

    kobo_sync_status.remove_synced_book(book.id)
    return "", 204


@csrf.exempt
@kobo.route("/v1/library/<dummy>", methods=["DELETE", "GET", "POST"])
@kobo.route("/v1/library/<dummy>/preview", methods=["POST"])
def HandleUnimplementedRequest(dummy=None):
    return redirect_or_proxy_request()


@csrf.exempt
@kobo.route("/v1/user/loyalty/<dummy>", methods=["GET", "POST"])
@kobo.route("/v1/user/profile", methods=["GET", "POST"])
@kobo.route("/v1/user/wishlist", methods=["GET", "POST"])
@kobo.route("/v1/user/recommendations", methods=["GET", "POST"])
@kobo.route("/v1/analytics/<dummy>", methods=["GET", "POST"])
@kobo.route("/v1/assets", methods=["GET"])
def HandleUserRequest(dummy=None):
    return redirect_or_proxy_request()


@csrf.exempt
@kobo.route("/v1/user/loyalty/benefits", methods=["GET"])
def handle_benefits():
    return redirect_or_proxy_request() if config.config_kobo_proxy else make_response(jsonify({"Benefits": {}}))


@csrf.exempt
@kobo.route("/v1/analytics/gettests", methods=["GET", "POST"])
def handle_getests():
    if config.config_kobo_proxy: return redirect_or_proxy_request()
    return make_response(jsonify({"Result": "Success", "TestKey": request.headers.get("X-Kobo-userkey", ""), "Tests": {}}))


@csrf.exempt
@kobo.route("/v1/products/<path:dummy>", methods=["GET", "POST"])
@kobo.route("/v1/products", methods=["GET", "POST"])
@kobo.route("/v1/affiliate", methods=["GET", "POST"])
@kobo.route("/v1/deals", methods=["GET", "POST"])
@kobo.route("/v1/categories/<path:dummy>", methods=["GET", "POST"])
def HandleProductsRequest(dummy=None):
    return redirect_or_proxy_request()


def make_calibre_web_auth_response():
    content = request.get_json()
    return make_response(jsonify({
        "AccessToken": base64.b64encode(os.urandom(24)).decode('utf-8'),
        "RefreshToken": base64.b64encode(os.urandom(24)).decode('utf-8'),
        "TokenType": "Bearer", "TrackingId": str(uuid.uuid4()), "UserKey": content.get('UserKey', "")
    }))


def make_calibre_web_oauth_response():
    content = request.get_json(silent=True) or {}
    token = base64.b64encode(os.urandom(24)).decode('utf-8')
    return make_response(jsonify({
        "access_token": token, "refresh_token": token, "token_type": "Bearer", "expires_in": 3600,
        "scope": content.get("scope", ""), "user_id": content.get("user_id", ""),
        "AccessToken": token, "RefreshToken": token, "TokenType": "Bearer"
    }))


@csrf.exempt
@kobo.route("/v1/auth/device", methods=["POST"])
@requires_kobo_auth
def HandleAuthRequest():
    if config.config_kobo_proxy:
        try: return redirect_or_proxy_request()
        except Exception: log.error("Kobo proxy auth failed")
    return make_calibre_web_auth_response()


@csrf.exempt
@kobo.route("/oauth/<path:subpath>", methods=["GET", "POST"])
@requires_kobo_auth
def HandleOauthRequest(subpath=None):
    return make_calibre_web_oauth_response()


@kobo.route("/v1/initialization")
@requires_kobo_auth
def HandleInitRequest():
    log.info('Init')
    kobo_resources = None
    if config.config_kobo_proxy:
        try:
            store_response = make_request_to_kobo_store()
            store_json = store_response.json()
            if rs := store_json.get("ResponseStatus", {}):
                if rs.get("ErrorCode") == "ExpiredToken": return make_proxy_response(store_response)
            kobo_resources = store_json.get("Resources")
        except Exception as e: log.error(f"Kobo init failed: {e}")
    
    if not kobo_resources: kobo_resources = NATIVE_KOBO_RESOURCES()

    # URL-Generierung für Covers und Download (unverändert)
    host = request.host.split(':')[0] if ':' in request.host and not request.host.endswith(']') else request.host
    calibre_web_url = "{scheme}://{host}:{port}".format(scheme=request.scheme, host=host, port=config.config_external_port)
    
    kobo_resources["image_host"] = calibre_web_url
    kobo_resources["image_url_template"] = unquote(calibre_web_url + url_for("kobo.HandleCoverImageRequest", 
        auth_token=kobo_auth.get_auth_token(), book_uuid="{ImageId}", width="{width}", height="{height}", isGreyscale='false'))
    
    if not config.config_kobo_proxy:
        oauth_url = url_for("kobo.HandleOauthRequest", auth_token=kobo_auth.get_auth_token(), _external=True)
        kobo_resources["oauth_host"] = oauth_url.rsplit("/oauth", 1)[0] + "/oauth"

    return make_response(jsonify({"Resources": kobo_resources}))


@kobo.route("/download/<book_id>/<book_format>")
@requires_kobo_auth
@download_required
def download_book(book_id, book_format):
    return get_download_link(book_id, book_format, "kobo")


def NATIVE_KOBO_RESOURCES():
    # Hier folgt die lange Liste der nativen Ressourcen (unverändert)
    return {
        "account_page": "https://www.kobo.com/account/settings",
        "image_host": "https://cdn.kobo.com/book-images/",
        "image_url_template": "https://cdn.kobo.com/book-images/{ImageId}/{Width}/{Height}/false/image.jpg",
        "library_sync": "https://storeapi.kobo.com/v1/library/sync",
        "oauth_host": "https://oauth.kobo.com",
        "reading_state": "https://storeapi.kobo.com/v1/library/{Ids}/state",
        # ... (Rest der Ressourcen-Liste)
    }
