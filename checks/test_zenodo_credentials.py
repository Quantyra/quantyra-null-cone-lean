"""Credential isolation and publication gate regression checks (no live services)."""

import contextlib
import io
import json
from pathlib import Path
import runpy
import sys
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import zenodo_credentials as credentials


class CredentialSafety(unittest.TestCase):
    def setUp(self):
        self.session = Mock()
        self.sts = Mock()
        self.sm = Mock()
        self.session.client.side_effect = lambda name: {"sts": self.sts, "secretsmanager": self.sm}[name]
        self.sts.get_caller_identity.return_value = {"Account": credentials.ACCOUNT, "Arn": "test-principal"}
        self.sm.get_secret_value.return_value = {
            "ARN": credentials.SECRET_ARN, "SecretString": json.dumps({"ZENODO_ACCESS_TOKEN": "synthetic-test-token"}),
            "VersionId": "test-version", "VersionStages": ["AWSCURRENT"],
        }

    def test_defaults_and_envelope(self):
        with patch.object(credentials.boto3, "Session", return_value=self.session) as factory:
            token, metadata = credentials.aws_token()
        factory.assert_called_once_with(profile_name="quantyra", region_name="us-east-1")
        self.assertEqual(token, "synthetic-test-token")
        self.assertNotIn(token, json.dumps(metadata))

    def test_wrong_account_never_reads_secret(self):
        self.sts.get_caller_identity.return_value["Account"] = "485386182336"
        with patch.object(credentials.boto3, "Session", return_value=self.session), self.assertRaises(SystemExit):
            credentials.aws_token()
        self.sm.get_secret_value.assert_not_called()

    def test_bad_envelope_and_arn_fail_safely(self):
        for field, value in (("SecretString", "not-json"), ("SecretString", "{}"),
                             ("SecretString", '{"ZENODO_ACCESS_TOKEN":"bad\\ntoken"}'),
                             ("ARN", "wrong-arn")):
            with self.subTest(field=field, value=value):
                original = self.sm.get_secret_value.return_value.copy()
                self.sm.get_secret_value.return_value[field] = value
                with patch.object(credentials.boto3, "Session", return_value=self.session), self.assertRaises(SystemExit) as error:
                    credentials.aws_token()
                self.assertNotIn("synthetic-test-token", str(error.exception))
                self.sm.get_secret_value.return_value = original

    def test_check_only_gets_no_redirects_no_body_output(self):
        response = Mock(status_code=200, headers={"Content-Type": "application/json"})
        response.json.return_value = [{"private": "never-output"}]
        output = io.StringIO()
        with patch.object(credentials.requests, "get", return_value=response) as get, contextlib.redirect_stdout(output):
            self.assertTrue(credentials.read_only_check("synthetic-test-token", {}))
        self.assertEqual(get.call_count, 4)
        for call in get.call_args_list:
            self.assertFalse(call.kwargs["allow_redirects"])
        self.assertNotIn("synthetic-test-token", output.getvalue())
        self.assertNotIn("never-output", output.getvalue())

    def test_html_403_not_auth_success(self):
        response = Mock(status_code=403, headers={"Content-Type": "text/html"})
        with patch.object(credentials.requests, "get", return_value=response), contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(credentials.read_only_check("synthetic-test-token", {}))
        response.json.assert_not_called()

    def test_cli_check_exits_before_payload_or_state_access(self):
        script = Path(__file__).with_name("publish_manuscript_deposit.py")
        with patch.object(sys, "argv", [str(script), "--check-credentials"]), \
             patch.object(credentials, "aws_token", return_value=("synthetic-test-token", {})), \
             patch.object(credentials, "read_only_check", return_value=True), \
             patch("subprocess.check_output") as git, patch.object(Path, "mkdir") as mkdir:
            with self.assertRaises(SystemExit) as error:
                runpy.run_path(str(script), run_name="__main__")
        self.assertEqual(error.exception.code, 0)
        git.assert_not_called()
        mkdir.assert_not_called()


if __name__ == "__main__":
    unittest.main()
