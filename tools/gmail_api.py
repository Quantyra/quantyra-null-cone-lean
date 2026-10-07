"""On-demand Quantyra Gmail reads and marking reviewed messages as read.

Credentials use Windows user-bound DPAPI outside Git. OAuth uses Google's
installed-app library, PKCE, state validation and a loopback callback.
"""

from __future__ import annotations

import argparse
import base64
import ctypes
from ctypes import wintypes
from datetime import datetime, timezone
import hashlib
import json
import logging
import os
from pathlib import Path
import re
import sys
import tempfile
from urllib.parse import quote

# The workstation has an embedded Python distribution, without venv support.
# Dependency installation is isolated from the proof tooling's packages.
DEPENDENCIES = Path.home() / "QuantyraTools" / "GmailAPI" / "site-packages"
if DEPENDENCIES.is_dir():
    sys.path.insert(0, str(DEPENDENCIES))

MAILBOX = "dfredriksen@quantyra.org"
SCOPES = ["https://www.googleapis.com/auth/gmail.modify"]
API_ROOT = "https://gmail.googleapis.com/gmail/v1/users/me"
STATE_ROOT = Path.home() / ".quantyra" / "gmail"
MAX_PDF_BYTES = 25 * 1024 * 1024
ENVELOPE = b"QUANTYRA-GMAIL-DPAPI-1\n"

# Suppress library request/callback debug logs, including OAuth query strings.
for logger_name in ("google_auth_oauthlib", "requests_oauthlib", "oauthlib", "google.auth"):
    logging.getLogger(logger_name).setLevel(logging.WARNING)


class AccessError(Exception):
    """A deliberately sanitized operational error."""


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def outside_git(path: Path):
    path = path.resolve()
    if any((parent / ".git").exists() for parent in (path, *path.parents)):
        raise AccessError("Credentials and private mail must be stored outside Git.")
    return path


def atomic_write(path: Path, data: bytes):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=".gmail-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def dpapi(data: bytes, *, decrypt=False):
    if os.name != "nt":
        raise AccessError("This credential store requires Windows user-bound DPAPI.")

    class Blob(ctypes.Structure):
        _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_ubyte))]

    memory = ctypes.create_string_buffer(data)
    source = Blob(len(data), ctypes.cast(memory, ctypes.POINTER(ctypes.c_ubyte)))
    target = Blob()
    crypt32 = ctypes.WinDLL("crypt32", use_last_error=True)
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.LocalFree.argtypes = [ctypes.c_void_p]
    kernel32.LocalFree.restype = ctypes.c_void_p
    description = ctypes.c_wchar_p()
    if decrypt:
        operation = crypt32.CryptUnprotectData
        operation.argtypes = [ctypes.POINTER(Blob), ctypes.POINTER(ctypes.c_wchar_p),
                              ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p,
                              wintypes.DWORD, ctypes.POINTER(Blob)]
        ok = operation(ctypes.byref(source), ctypes.byref(description), None, None,
                       None, 1, ctypes.byref(target))
    else:
        operation = crypt32.CryptProtectData
        operation.argtypes = [ctypes.POINTER(Blob), ctypes.c_wchar_p, ctypes.c_void_p,
                              ctypes.c_void_p, ctypes.c_void_p, wintypes.DWORD,
                              ctypes.POINTER(Blob)]
        ok = operation(ctypes.byref(source), "Quantyra Gmail API", None, None,
                       None, 1, ctypes.byref(target))
    if not ok:
        raise AccessError("Windows could not protect or unlock the credential file.")
    try:
        return ctypes.string_at(target.pbData, target.cbData)
    finally:
        kernel32.LocalFree(ctypes.cast(target.pbData, ctypes.c_void_p))
        if description:
            kernel32.LocalFree(ctypes.cast(description, ctypes.c_void_p))


def store_secret(name, value):
    root = outside_git(STATE_ROOT)
    atomic_write(root / name, ENVELOPE + dpapi(json.dumps(value).encode("utf-8")))


def load_secret(name):
    path = outside_git(STATE_ROOT) / name
    if not path.exists():
        raise AccessError(f"Missing {name}; import the desktop client and authenticate first.")
    contents = path.read_bytes()
    if not contents.startswith(ENVELOPE):
        raise AccessError("Refusing an unencrypted or unsupported credential file.")
    return json.loads(dpapi(contents[len(ENVELOPE):], decrypt=True))


def validate_client(config):
    installed = config.get("installed")
    if not isinstance(installed, dict):
        raise AccessError("Download an OAuth Desktop app client JSON, not a Web app client.")
    if not installed.get("client_id", "").endswith(".apps.googleusercontent.com"):
        raise AccessError("The desktop OAuth client ID is invalid.")
    if not installed.get("client_secret"):
        raise AccessError("The desktop OAuth client JSON has no client secret.")
    # Never send credentials or authorization codes to endpoints from arbitrary JSON.
    if installed.get("auth_uri") not in (
        "https://accounts.google.com/o/oauth2/auth", "https://accounts.google.com/o/oauth2/v2/auth"
    ):
        raise AccessError("The client must use Google's official authorization endpoint.")
    if installed.get("token_uri") != "https://oauth2.googleapis.com/token":
        raise AccessError("The client must use Google's official token endpoint.")
    return config


def validate_scopes(scopes):
    if set(scopes or []) != set(SCOPES):
        raise AccessError("This tool requires exactly the Gmail modify OAuth grant.")


def import_client(path):
    config = validate_client(json.loads(path.read_text(encoding="utf-8-sig")))
    store_secret("client.dpapi", config)
    print("Desktop OAuth client imported into the encrypted, private credential store.")


class Gmail:
    def __init__(self, credentials):
        from google.auth.transport.requests import AuthorizedSession
        self.credentials = credentials
        self.session = AuthorizedSession(credentials)
        self.verified = False

    def get(self, suffix, params=None, *, profile=False):
        if not self.verified and not profile:
            self.verify()
        response = self.session.get(API_ROOT + suffix, params=params, timeout=45,
                                    allow_redirects=False)
        if response.status_code != 200:
            raise AccessError(f"Gmail API read failed with HTTP {response.status_code}.")
        try:
            return response.json()
        except ValueError:
            raise AccessError("Gmail API returned an unexpected response format.") from None

    def verify(self):
        profile = self.get("/profile", profile=True)
        if profile.get("emailAddress", "").casefold() != MAILBOX.casefold():
            raise AccessError(f"Account mismatch. Authenticate as {MAILBOX} before reading mail.")
        self.verified = True
        return {"mailbox": MAILBOX, "verified_at": utc_now(), "operation": "Gmail users.getProfile"}

    def save(self):
        if not self.verified:
            raise AccessError("Refusing to persist a token before verifying mailbox identity.")
        store_secret("token.dpapi", json.loads(self.credentials.to_json()))


def authenticate():
    # Google's helper prints the URL before blocking; make it visible in piped runs.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)
    from google_auth_oauthlib.flow import InstalledAppFlow
    config = validate_client(load_secret("client.dpapi"))
    flow = InstalledAppFlow.from_client_config(config, SCOPES, autogenerate_code_verifier=True)
    # Browser launch is disabled because the host rejected the shell browser action.
    # The authorization link is public app/state/PKCE metadata, never a token or code.
    print(f"Sign in as {MAILBOX}. Open the following Google authorization link:", flush=True)
    credentials = flow.run_local_server(
        host="127.0.0.1", bind_addr="127.0.0.1", port=0, open_browser=False,
        authorization_prompt_message="{url}",
        success_message="Authorization received. You can return to Codex.",
        timeout_seconds=600, access_type="offline", prompt="consent", login_hint=MAILBOX,
    )
    validate_scopes(credentials.granted_scopes or credentials.scopes)
    if not credentials.refresh_token:
        raise AccessError("No offline refresh token was issued; repeat consent for offline access.")
    gmail = Gmail(credentials)
    receipt = gmail.verify()
    gmail.save()
    atomic_write(outside_git(STATE_ROOT) / "connection-receipt.json",
                 json.dumps({**receipt, "scope": SCOPES[0], "credential_storage": "Windows user DPAPI"},
                            indent=2).encode())
    print(json.dumps(receipt))


def connect():
    from google.auth.transport.requests import Request
    from google.oauth2.credentials import Credentials
    config = load_secret("token.dpapi")
    validate_scopes(config.get("scopes"))
    if config.get("token_uri") != "https://oauth2.googleapis.com/token":
        raise AccessError("Refusing a token configured for a non-Google endpoint.")
    credentials = Credentials.from_authorized_user_info(config, SCOPES)
    if not credentials.valid:
        if not credentials.refresh_token:
            raise AccessError("Reauthentication required: no usable offline credential.")
        credentials.refresh(Request())
    validate_scopes(credentials.granted_scopes or credentials.scopes)
    gmail = Gmail(credentials)
    gmail.verify()
    gmail.save()
    return gmail


def import_token(path):
    """Reuse an existing matching AIOS grant after live mailbox verification."""
    from google.auth.transport.requests import Request
    from google.oauth2.credentials import Credentials
    config = json.loads(path.read_text(encoding="utf-8-sig"))
    validate_scopes(config.get("scopes"))
    client = validate_client(load_secret("client.dpapi"))["installed"]
    if config.get("client_id") != client["client_id"]:
        raise AccessError("The existing token does not belong to the imported OAuth client.")
    if config.get("token_uri") != "https://oauth2.googleapis.com/token":
        raise AccessError("Refusing a token configured for a non-Google endpoint.")
    credentials = Credentials.from_authorized_user_info(config, SCOPES)
    if not credentials.refresh_token:
        raise AccessError("The existing credential has no offline refresh token.")
    if not credentials.valid:
        credentials.refresh(Request())
    validate_scopes(credentials.granted_scopes or credentials.scopes)
    gmail = Gmail(credentials)
    receipt = gmail.verify()
    gmail.save()
    atomic_write(outside_git(STATE_ROOT) / "connection-receipt.json",
                 json.dumps({**receipt, "scope": SCOPES[0], "credential_storage": "Windows user DPAPI",
                             "authentication": "verified-existing-AIOS-grant"}, indent=2).encode())
    print(json.dumps(receipt))


def mark_read(gmail, message_id):
    """The sole write operation: remove UNREAD from one reviewed message."""
    suffix = "/messages/" + validate_id(message_id)
    before = gmail.get(suffix, {"format": "metadata"})
    changed = "UNREAD" in before.get("labelIds", [])
    if changed:
        response = gmail.session.post(
            API_ROOT + suffix + "/modify", json={"removeLabelIds": ["UNREAD"]},
            timeout=45, allow_redirects=False,
        )
        if response.status_code != 200:
            raise AccessError(f"Gmail mark-read failed with HTTP {response.status_code}.")
        after = gmail.get(suffix, {"format": "metadata"})
        if "UNREAD" in after.get("labelIds", []):
            raise AccessError("Gmail did not confirm that the selected message is read.")
    gmail.save()
    print(json.dumps({"message_id": message_id, "marked_read": True, "changed": changed,
                      "verified_at": utc_now()}))


def parts(payload):
    yield payload
    for part in payload.get("parts", []):
        yield from parts(part)


def headers(payload):
    return {h["name"].lower(): h.get("value", "") for h in payload.get("headers", [])
            if h.get("name", "").lower() in {"from", "to", "subject", "date", "message-id"}}


def validate_id(value, *, max_length=256):
    if not isinstance(value, str) or not 1 <= len(value) <= max_length or not re.fullmatch(r"[A-Za-z0-9_-]+", value):
        raise AccessError("Invalid Gmail message or attachment ID.")
    return quote(value, safe="")


def search(gmail, query, limit):
    if not 1 <= limit <= 20:
        raise AccessError("Search limit must be between 1 and 20.")
    result = gmail.get("/messages", {"q": query, "maxResults": limit})
    messages = []
    for item in result.get("messages", []):
        message_id = validate_id(item["id"])
        message = gmail.get("/messages/" + message_id, {"format": "full"})
        messages.append({"id": item["id"], "thread_id": message.get("threadId"),
                         "headers": headers(message.get("payload", {})),
                         "pdf_attachments": [p.get("filename") for p in parts(message.get("payload", {}))
                                             if p.get("filename", "").lower().endswith(".pdf")]})
    gmail.save()
    print(json.dumps({"mailbox": MAILBOX, "result_count": len(messages), "messages": messages},
                     ensure_ascii=False, indent=2))


def decode_pdf(encoded):
    if len(encoded) > 4 * ((MAX_PDF_BYTES + 2) // 3):
        raise AccessError("PDF exceeds the download size limit.")
    try:
        data = base64.b64decode(encoded + "=" * (-len(encoded) % 4), altchars=b"-_", validate=True)
    except (ValueError, TypeError):
        raise AccessError("Attachment encoding is invalid.") from None
    if len(data) > MAX_PDF_BYTES or not data.startswith(b"%PDF-"):
        raise AccessError("Attachment is not a supported PDF.")
    return data


def download(gmail, message_id, output_dir):
    directory = outside_git(output_dir)
    directory.mkdir(parents=True, exist_ok=True)
    message = gmail.get("/messages/" + validate_id(message_id), {"format": "full"})
    records = []
    for part in parts(message.get("payload", {})):
        original_name = part.get("filename", "")
        if not original_name.lower().endswith(".pdf"):
            continue
        body = part.get("body", {})
        if body.get("size", 0) > MAX_PDF_BYTES:
            raise AccessError("PDF exceeds the download size limit.")
        if body.get("attachmentId"):
            suffix = "/messages/" + validate_id(message_id) + "/attachments/" + validate_id(body["attachmentId"], max_length=4096)
            encoded = gmail.get(suffix).get("data", "")
        else:
            encoded = body.get("data", "")
        data = decode_pdf(encoded)
        digest = hashlib.sha256(data).hexdigest()
        # Original filenames are metadata only, never filesystem paths.
        destination = directory / f"{message_id}-{digest[:16]}.pdf"
        if destination.exists():
            if destination.read_bytes() != data:
                raise AccessError("An existing output has different bytes; refusing overwrite.")
        else:
            with destination.open("xb") as handle:
                handle.write(data)
        records.append({"original_filename": original_name, "path": str(destination),
                        "sha256": digest, "bytes": len(data)})
    if not records:
        raise AccessError("No PDF attachments found in the selected message.")
    manifest = {"mailbox": MAILBOX, "message_id": message_id,
                "thread_id": message.get("threadId"), "headers": headers(message.get("payload", {})),
                "retrieved_at": utc_now(), "files": records}
    atomic_write(directory / f"{message_id}-provenance.json", json.dumps(manifest, indent=2).encode())
    gmail.save()
    print(json.dumps({"downloaded_pdf_count": len(records), "files": records}, indent=2))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    importer = commands.add_parser("import-client")
    importer.add_argument("path", type=Path)
    token_importer = commands.add_parser("import-token")
    token_importer.add_argument("path", type=Path)
    commands.add_parser("auth")
    commands.add_parser("profile")
    finder = commands.add_parser("search")
    finder.add_argument("--query", required=True)
    finder.add_argument("--limit", type=int, default=5)
    downloader = commands.add_parser("download")
    downloader.add_argument("--message-id", required=True)
    downloader.add_argument("--output-dir", type=Path, required=True)
    marker = commands.add_parser("mark-read")
    marker.add_argument("--message-id", required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "import-client":
            import_client(args.path)
        elif args.command == "import-token":
            import_token(args.path)
        elif args.command == "auth":
            authenticate()
        else:
            gmail = connect()
            if args.command == "profile":
                print(json.dumps(gmail.verify()))
            elif args.command == "search":
                search(gmail, args.query, args.limit)
            elif args.command == "mark-read":
                mark_read(gmail, args.message_id)
            else:
                download(gmail, args.message_id, args.output_dir)
    except AccessError as error:
        print(str(error), file=sys.stderr)
        return 1
    except Exception as error:
        # OAuth/network/library exception strings may contain private request data.
        print(f"Operation failed ({type(error).__name__}); no credentials or response body printed.",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
