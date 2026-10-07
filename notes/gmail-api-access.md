# Direct Gmail API research support

2026-10-07: the author requested OAuth credentials and direct Gmail API calls for purchased literature retrieval, superseding connector-dependent access. Ancillary implementation is [tools/gmail_api.py](../tools/gmail_api.py); it does not execute Lean or modify proofs/manuscripts. The fixed intended account is `dfredriksen@quantyra.org` and the sole implemented OAuth scope is `gmail.readonly`.

Install [tools/requirements-gmail.txt](../tools/requirements-gmail.txt), then use these commands with the same Python interpreter:

```text
python tools/gmail_api.py import-client <Desktop-app-client-JSON-path>
python tools/gmail_api.py auth
python tools/gmail_api.py profile
python tools/gmail_api.py search --query "has:attachment filename:pdf Winkler" --limit 5
python tools/gmail_api.py download --message-id <selected-ID> --output-dir <private-path-outside-Git>
python -m unittest discover -s tools -p test_gmail_api.py -v
```

On this Windows workstation the embedded Python is `C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe`. It lacks `venv`, so dependencies were installed separately using `pip install --target C:/Users/dfred/QuantyraTools/GmailAPI/site-packages -r tools/requirements-gmail.txt`; the tool explicitly loads that directory. Credentials are encrypted using current-user Windows DPAPI under `%USERPROFILE%/.quantyra/gmail`, outside Git. Restrict the directory ACL to its owning Windows SID and SYSTEM with inherited permissions removed before use. Another Windows account/workstation needs its own authorization.

The tool requires a legitimate Google **Desktop app** OAuth client JSON; no existing client is bundled, and a Gmail connector installation does not supply one. It validates Google's authorization/token endpoints. The official installed-app library generates PKCE and validates OAuth state with a callback on `127.0.0.1`. Sign in through the displayed authorization link; the callback expires after ten minutes. Host policy rejected a requested programmatic shell browser launch, so the tool does not attempt another browser-launch mechanism.

The tool verifies the actual Gmail profile before reading messages or persisting a newly issued token, requires an offline refresh token, and rejects different identities or broader saved scopes. Future calls refresh the token on demand and reverify the mailbox. Missing or revoked credentials require renewed consent. Library OAuth debug/callback logging is suppressed and exception messages are sanitized. No token, authorization code or private API response body is printed.

Searches are capped at twenty results; use the task's bounded query and smaller limit. PDF retrieval uses generated filenames, validates bytes and size, refuses conflicting overwrites, and writes private provenance including original filename, Gmail message/thread references, headers, retrieval time and SHA256. The tool refuses Git destinations for credentials or private attachments. Do not redistribute purchased PDFs or raw email provenance in this public repository. Only appropriate scholarly provenance and file checksums belong in the literature comparison.

Verification: credential and private-output regressions test DPAPI encryption/roundtrip, plaintext refusal, account mismatch before message read, read-only scopes, endpoint validation, state/PKCE behavior and attachment/path boundaries. These tests use fake credentials and do not establish a live Gmail connection. The missing Desktop app client and user consent remain explicit prerequisites.

Provider references: [Gmail Python quickstart](https://developers.google.com/workspace/gmail/api/quickstart/python), [installed-app OAuth](https://developers.google.com/identity/protocols/oauth2/native-app), [Gmail scopes](https://developers.google.com/workspace/gmail/api/auth/scopes).

Remaining to-do list: import a client, complete user consent, verify live profile/bounded reads and saved-token reuse, then retrieve the two Winkler papers.
