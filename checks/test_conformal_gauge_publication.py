"""Offline regression checks for independent-record publication boundaries."""
import copy
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import publish_conformal_gauge as publication


class PublicationBoundaries(unittest.TestCase):
    def test_authenticated_url_boundary(self):
        for url in ('http://zenodo.org/api/x', 'https://example.org/api/x',
                    'https://zenodo.org.evil.test/api/x', 'https://zenodo.org/records/1',
                    'https://zenodo.org/api/x?access_token=secret', 'https://zenodo.org/api/x#fragment',
                    'https://user@zenodo.org/api/x'):
            with self.subTest(url=url), self.assertRaises(AssertionError):
                publication.trusted(url)

    def test_old_families_and_records_rejected(self):
        draft = {'id': 99999999, 'conceptrecid': '99999998',
                 'metadata': {'title': publication.TITLE, 'version': '0.1.0'}}
        publication.validate_identity(draft)
        for family in publication.OLD_FAMILIES:
            bad = copy.deepcopy(draft)
            bad['conceptrecid'] = family
            with self.assertRaises(AssertionError):
                publication.validate_identity(bad)
        for identity in publication.OLD_RECORDS:
            bad = copy.deepcopy(draft)
            bad['id'] = identity
            with self.assertRaises(AssertionError):
                publication.validate_identity(bad)

    def test_version_relation_rejected(self):
        metadata = publication.read(publication.PACKAGE / 'zenodo-metadata.json')
        publication.validate_metadata(metadata)
        metadata['related_identifiers'].append({'identifier': '10.5281/zenodo.23206772', 'relation': 'isVersionOf'})
        with self.assertRaises(AssertionError):
            publication.validate_metadata(metadata)

    def test_wrong_reservation_rejected(self):
        record = {'id': 99999999, 'conceptrecid': '99999998', 'metadata': {
            'title': publication.TITLE, 'version': '0.1.0', 'doi': '10.5281/zenodo.99999999'}}
        with self.assertRaises(AssertionError):
            publication.validate_identity(record, {'id': 99999997, 'conceptrecid': '99999998',
                                                   'doi': '10.5281/zenodo.99999997'})

    def test_invalid_freeze_cannot_access_credentials(self):
        with patch.object(publication, 'authenticated_request') as authenticate:
            with patch.object(sys, 'argv', ['publish_conformal_gauge.py', '--publish', '--commit', 'bad']):
                with self.assertRaises(AssertionError):
                    publication.main()
            authenticate.assert_not_called()


if __name__ == '__main__':
    unittest.main()
