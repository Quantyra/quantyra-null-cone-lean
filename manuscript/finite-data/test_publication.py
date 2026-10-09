"""Offline tests for the new record and frozen-payload publication boundary."""
import copy
from pathlib import Path
import sys
import unittest
import tempfile
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import publish

p = publish.publication


class PublicationBoundaries(unittest.TestCase):
    def test_authenticated_urls(self):
        for url in ("http://zenodo.org/api/x", "https://example.org/api/x",
                    "https://zenodo.org.evil.test/api/x", "https://zenodo.org/records/1",
                    "https://zenodo.org/api/x?access_token=secret",
                    "https://zenodo.org/api/x#fragment", "https://user@zenodo.org/api/x"):
            with self.subTest(url=url), self.assertRaises(AssertionError):
                p.trusted(url)

    def test_existing_families_and_records_rejected(self):
        draft = {"id": 99999999, "conceptrecid": "99999998",
                 "metadata": {"title": p.TITLE, "version": "0.1.0"}}
        p.validate_identity(draft)
        for key, values in (("conceptrecid", p.OLD_FAMILIES), ("id", p.OLD_RECORDS)):
            for value in values:
                bad = copy.deepcopy(draft)
                bad[key] = value
                with self.subTest(key=key, value=value), self.assertRaises(AssertionError):
                    p.validate_identity(bad)

    def test_version_relation_rejected(self):
        metadata = p.read(p.PACKAGE / "zenodo-metadata.json")
        p.validate_metadata(metadata)
        for family in p.OLD_FAMILIES:
            bad = copy.deepcopy(metadata)
            bad["related_identifiers"].append({
                "identifier": "10.5281/zenodo." + family, "relation": "isVersionOf"})
            with self.assertRaises(AssertionError):
                p.validate_metadata(bad)

    def test_wrong_reservation_rejected(self):
        record = {"id": 99999999, "conceptrecid": "99999998", "metadata": {
            "title": p.TITLE, "version": "0.1.0", "doi": "10.5281/zenodo.99999999"}}
        with self.assertRaises(AssertionError):
            p.validate_identity(record, {"id": 99999997, "conceptrecid": "99999998",
                                       "doi": "10.5281/zenodo.99999997"})

    def test_invalid_freeze_cannot_access_credentials(self):
        with patch.object(p, "authenticated_request") as authenticate:
            with patch.object(sys, "argv", ["publish.py", "--publish", "--commit", "bad"]):
                with self.assertRaises(AssertionError):
                    p.main()
            authenticate.assert_not_called()

    def test_publication_labels_require_reviewed_source(self):
        with self.assertRaises(AssertionError):
            publish.publication_source("unrelated manuscript", "10.5281/zenodo.99999999")

    def test_uncertain_creation_prevents_second_post(self):
        with tempfile.TemporaryDirectory() as directory:
            intent = Path(directory) / "intent.json"
            intent.write_text("{}")
            request = Mock(return_value=Mock(json=lambda: []))
            with patch.object(p, "INTENT", intent), patch.object(
                p, "RESERVATION", Path(directory) / "reservation.json"
            ), patch.object(p, "authenticated_request", return_value=request):
                with self.assertRaisesRegex(AssertionError, "Unresolved creation intent"):
                    p.reserve({})
            self.assertEqual([call.args[0] for call in request.call_args_list], ["GET"])

    def test_uncertain_creation_recovers_matching_draft(self):
        draft = {
            "id": 99999999, "conceptrecid": "99999998", "submitted": False,
            "metadata": {"title": p.TITLE, "version": "0.1.0",
                         "prereserve_doi": {"doi": "10.5281/zenodo.99999999"}},
        }
        with tempfile.TemporaryDirectory() as directory:
            intent = Path(directory) / "intent.json"
            intent.write_text("{}")
            request = Mock(side_effect=[Mock(json=lambda: [draft]), Mock(json=lambda: draft)])
            with patch.object(p, "INTENT", intent), patch.object(
                p, "RESERVATION", Path(directory) / "reservation.json"
            ), patch.object(p, "authenticated_request", return_value=request), patch("builtins.print"):
                p.reserve({})
                self.assertEqual(p.read(p.RESERVATION)["id"], draft["id"])
            self.assertEqual([call.args[0] for call in request.call_args_list], ["GET", "GET"])

    def test_pdf_order_before_publication(self):
        reservation = {"id": 99999999, "conceptrecid": "99999998",
                       "doi": "10.5281/zenodo.99999999"}
        pdf = {"filename": p.STEM + ".pdf", "id": "pdf-id"}
        archive = {"filename": p.STEM + "-v0.1.0-source.zip", "id": "zip-id"}
        draft = {"id": reservation["id"], "conceptrecid": reservation["conceptrecid"],
                 "metadata": {"title": p.TITLE, "version": "0.1.0", "doi": reservation["doi"]},
                 "files": [pdf, archive]}
        request = Mock(return_value=Mock(json=lambda: draft))
        publish.verify_pdf_first(request, p.API + "/deposit/depositions/99999999", reservation)
        self.assertEqual([call.args[0] for call in request.call_args_list], ["GET"])
        draft["files"] = [archive, pdf]
        with self.assertRaisesRegex(AssertionError, "PDF must be first"):
            publish.verify_pdf_first(request, p.API + "/deposit/depositions/99999999", reservation)


if __name__ == "__main__":
    unittest.main()
