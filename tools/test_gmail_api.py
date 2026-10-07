"""Regression checks for the Gmail credential and private-output boundaries."""

import base64
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch
from urllib.parse import parse_qs, urlparse

import gmail_api as api


def client():
    return {"installed": {"client_id": "test.apps.googleusercontent.com",
                          "client_secret": "fake-client-secret",
                          "auth_uri": "https://accounts.google.com/o/oauth2/auth",
                          "token_uri": "https://oauth2.googleapis.com/token"}}


class GmailBoundaries(unittest.TestCase):
    def test_installed_app_authorization_uses_pkce_state_and_readonly_scope(self):
        from google_auth_oauthlib.flow import InstalledAppFlow
        flow = InstalledAppFlow.from_client_config(client(), api.SCOPES,
                                                  autogenerate_code_verifier=True)
        flow.redirect_uri = "http://127.0.0.1:12345/"
        url, state = flow.authorization_url(access_type="offline", login_hint=api.MAILBOX)
        query = parse_qs(urlparse(url).query)
        self.assertEqual(query["scope"], api.SCOPES)
        self.assertEqual(query["code_challenge_method"], ["S256"])
        self.assertTrue(query["code_challenge"][0])
        self.assertEqual(query["state"], [state])
        self.assertTrue(state)
        self.assertEqual(query["redirect_uri"], ["http://127.0.0.1:12345/"])

    def test_invalid_callback_state_is_rejected(self):
        from google_auth_oauthlib.flow import InstalledAppFlow
        from oauthlib.oauth2 import MismatchingStateError
        flow = InstalledAppFlow.from_client_config(client(), api.SCOPES,
                                                  autogenerate_code_verifier=True)
        flow.redirect_uri = "http://127.0.0.1:12345/"
        flow.authorization_url()
        # Google's helper converts the loopback callback to HTTPS for oauthlib.
        with self.assertRaises(MismatchingStateError):
            flow.fetch_token(authorization_response="https://127.0.0.1:12345/?code=fake&state=wrong")

    def test_reject_web_client(self):
        with self.assertRaises(api.AccessError):
            api.validate_client({"web": client()["installed"]})

    def test_reject_non_google_token_endpoint(self):
        config = client()
        config["installed"]["token_uri"] = "https://attacker.invalid/token"
        with self.assertRaises(api.AccessError):
            api.validate_client(config)

    def test_reject_non_google_auth_endpoint(self):
        config = client()
        config["installed"]["auth_uri"] = "https://attacker.invalid/auth"
        with self.assertRaises(api.AccessError):
            api.validate_client(config)

    def test_refuse_write_scopes(self):
        for scopes in [[], ["https://mail.google.com/"],
                       api.SCOPES + ["https://www.googleapis.com/auth/gmail.send"]]:
            with self.assertRaises(api.AccessError):
                api.validate_scopes(scopes)
        api.validate_scopes(api.SCOPES)

    def test_refuse_credentials_or_private_mail_in_git(self):
        with tempfile.TemporaryDirectory() as root:
            (Path(root) / ".git").touch()  # Includes a worktree .git file.
            with self.assertRaises(api.AccessError):
                api.outside_git(Path(root) / "nested" / "token.dpapi")

    def test_account_mismatch_stops_before_message_read(self):
        gmail = api.Gmail.__new__(api.Gmail)
        gmail.credentials = Mock()
        gmail.session = Mock()
        gmail.verified = False
        gmail.session.get.return_value.status_code = 200
        gmail.session.get.return_value.json.return_value = {"emailAddress": "other@example.com"}
        with self.assertRaises(api.AccessError):
            gmail.get("/messages", {"q": "has:attachment"})
        gmail.session.get.assert_called_once_with(api.API_ROOT + "/profile", params=None,
                                                 timeout=45, allow_redirects=False)
        self.assertFalse(gmail.verified)

    def test_refuse_unverified_token_persistence(self):
        gmail = api.Gmail.__new__(api.Gmail)
        gmail.verified = False
        with patch.object(api, "store_secret") as store:
            with self.assertRaises(api.AccessError):
                gmail.save()
            store.assert_not_called()

    def test_reject_path_in_message_id(self):
        with self.assertRaises(api.AccessError):
            api.validate_id("../../token")

    def test_reject_invalid_or_oversized_attachment(self):
        for payload in ["%%%", base64.urlsafe_b64encode(b"not a pdf").decode()]:
            with self.assertRaises(api.AccessError):
                api.decode_pdf(payload)
        with patch.object(api, "MAX_PDF_BYTES", 5):
            with self.assertRaises(api.AccessError):
                api.decode_pdf(base64.urlsafe_b64encode(b"%PDF-too-large").decode())

    def test_inline_pdf_filename_is_not_a_path(self):
        data = b"%PDF-1.4\nfixture"
        gmail = Mock()
        gmail.get.return_value = {"threadId": "thread123", "payload": {
            "parts": [{"filename": "../../private.pdf", "body": {
                "data": base64.urlsafe_b64encode(data).decode(), "size": len(data)}}]}}
        with tempfile.TemporaryDirectory() as directory:
            with patch("builtins.print"):
                api.download(gmail, "abc123", Path(directory))
            files = list(Path(directory).glob("*.pdf"))
            self.assertEqual(len(files), 1)
            self.assertEqual(files[0].read_bytes(), data)
            provenance = json.loads((Path(directory) / "abc123-provenance.json").read_text())
            self.assertEqual(provenance["files"][0]["original_filename"], "../../private.pdf")
            gmail.save.assert_called_once()

    @unittest.skipUnless(os.name == "nt", "Windows DPAPI")
    def test_private_store_roundtrip_and_plaintext_refusal(self):
        value = {"token": "fake-regression-token"}
        with tempfile.TemporaryDirectory() as root:
            with patch.object(api, "STATE_ROOT", Path(root)):
                api.store_secret("token.dpapi", value)
                ciphertext = (Path(root) / "token.dpapi").read_bytes()
                self.assertNotIn(b"fake-regression-token", ciphertext)
                self.assertEqual(api.load_secret("token.dpapi"), value)
                (Path(root) / "token.dpapi").write_text(json.dumps(value))
                with self.assertRaises(api.AccessError):
                    api.load_secret("token.dpapi")


if __name__ == "__main__":
    unittest.main()
