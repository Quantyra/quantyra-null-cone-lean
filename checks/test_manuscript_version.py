"""Offline checks for publication modes, draft recovery and credential URL bounds."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("version_publisher", Path(__file__).with_name("publish_manuscript_version.py"))
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)
import zenodo_credentials


class VersionPublicationTests(unittest.TestCase):
    def test_only_zenodo_api_urls_receive_credentials(self):
        self.assertEqual(publisher.trusted("https://zenodo.org/api/records/123"), "https://zenodo.org/api/records/123")
        for url in ("http://zenodo.org/api/records/123", "https://zenodo.org.evil.test/api/123",
                    "https://evil.test/api/123", "https://zenodo.org/records/123",
                    "https://user@zenodo.org/api/123", "https://zenodo.org/api/123?token=value"):
            with self.subTest(url=url), self.assertRaises(AssertionError):
                publisher.trusted(url)

    def test_publish_requires_frozen_commit_before_credentials(self):
        with patch.object(sys, "argv", ["publisher", "--publish"]), patch.object(zenodo_credentials, "aws_token") as token:
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                publisher.main()
            token.assert_not_called()

    def test_reserve_and_publish_cannot_be_combined(self):
        with patch.object(sys, "argv", ["publisher", "--reserve", "--publish"]), patch.object(zenodo_credentials, "aws_token") as token:
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                publisher.main()
            token.assert_not_called()

    def test_existing_family_draft_is_recovered_without_creation(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            package = root / "manuscript/deposit/v0.3.0"
            package.mkdir(parents=True)
            (package.parent / "published-record.json").write_text(json.dumps({"files": {}}))
            previous = {"metadata": {"version": "0.2.0", "title": "Paper"},
                        "conceptrecid": "23206772", "conceptdoi": "10.5281/zenodo.23206772"}
            parent = {"submitted": True, "metadata": {"version": "0.2.0"}, "links": {}}
            draft = {"id": 23214579, "conceptrecid": "23206772", "submitted": False,
                     "metadata": {"title": "Paper", "prereserve_doi": {"doi": "10.5281/zenodo.23214579"}}}
            calls = []
            class Response:
                status_code = 200
                def __init__(self, data): self.data = data
                def json(self): return self.data
            class Session:
                headers = {}
                def request(self, method, url, **kwargs):
                    calls.append((method, url))
                    if method != "GET": raise AssertionError("Recovery must not create another draft")
                    if url.endswith("/23206773"): return Response(parent)
                    if url.endswith("/23214579"): return Response(draft)
                    return Response([draft])
            with patch.multiple(publisher, ROOT=root, PACKAGE=package, RESERVATION=package/'draft-record.json'), \
                 patch.object(publisher, "public_record", return_value=previous), \
                 patch.object(publisher, "public_files", return_value={}), \
                 patch.object(publisher.requests, "Session", Session), \
                 patch.object(zenodo_credentials, "aws_token", return_value=("offline-test-token", {})), \
                 patch.object(sys, "argv", ["publisher", "--reserve"]), contextlib.redirect_stdout(io.StringIO()):
                publisher.main()
            self.assertEqual(json.loads((package/'draft-record.json').read_text())["id"], 23214579)
            self.assertTrue(calls and all(method == "GET" for method, _ in calls))


    def test_next_literature_version_uses_selected_previous_record(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            previous_package = root/'manuscript/deposit/v0.3.0'
            previous_package.mkdir(parents=True)
            (previous_package/'published-record.json').write_text(json.dumps({'files': {}}))
            previous = {'metadata': {'version': '0.3.0', 'title': 'Paper'},
                        'conceptrecid': '23206772', 'conceptdoi': '10.5281/zenodo.23206772'}
            parent = {'submitted': True, 'metadata': {'version': '0.3.0'}}
            draft = {'id': 23225029, 'conceptrecid': '23206772', 'submitted': False,
                     'metadata': {'title': 'Paper', 'prereserve_doi': {'doi': '10.5281/zenodo.23225029'}}}
            calls = []
            class Response:
                status_code = 200
                def __init__(self, data): self.data = data
                def json(self): return self.data
            class Session:
                headers = {}
                def request(self, method, url, **kwargs):
                    calls.append((method, url))
                    if method != 'GET': raise AssertionError('Recovered draft requires no creation')
                    if url.endswith('/23214579'): return Response(parent)
                    if url.endswith('/23225029'): return Response(draft)
                    return Response([draft])
            args = ['publisher', '--reserve', '--package', 'manuscript/deposit/v0.3.1',
                    '--version', '0.3.1', '--previous', '23214579', '--previous-version', '0.3.0',
                    '--previous-package', 'manuscript/deposit/v0.3.0']
            with patch.object(publisher, 'ROOT', root), \
                 patch.object(publisher, 'public_record', return_value=previous), \
                 patch.object(publisher, 'public_files', return_value={}), \
                 patch.object(publisher.requests, 'Session', Session), \
                 patch.object(zenodo_credentials, 'aws_token', return_value=('offline-test-token', {})), \
                 patch.object(sys, 'argv', args), contextlib.redirect_stdout(io.StringIO()):
                publisher.main()
            result = json.loads((root/'manuscript/deposit/v0.3.1/draft-record.json').read_text())
            self.assertEqual(result['previous_record'], 23214579)
            self.assertEqual(result['id'], 23225029)
            self.assertTrue(all(method == 'GET' for method, _ in calls))


if __name__ == "__main__":
    unittest.main()
