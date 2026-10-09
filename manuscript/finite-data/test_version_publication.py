"""Offline S045 identity, path, recovery and credential-boundary checks."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('finite_version', Path(__file__).with_name('publish_version.py'))
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)
import zenodo_credentials


class VersionTests(unittest.TestCase):
    def test_only_trusted_api_urls(self):
        self.assertEqual(publisher.trusted('https://zenodo.org/api/records/1'), 'https://zenodo.org/api/records/1')
        for url in ('http://zenodo.org/api/1', 'https://evil.test/api/1',
                    'https://zenodo.org.evil.test/api/1', 'https://zenodo.org/records/1',
                    'https://zenodo.org/api/1?token=hidden', 'https://user@zenodo.org/api/1'):
            with self.subTest(url=url), self.assertRaises(AssertionError):
                publisher.trusted(url)

    def test_invalid_modes_and_path_fail_before_credentials(self):
        cases = [(['--reserve','--proof-commit','short'], SystemExit),
                 (['--reserve','--publish'], SystemExit),
                 (['--publish'], SystemExit),
                 (['--reserve','--package','manuscript/deposit/v0.9.0'], AssertionError),
                 (['--reserve','--package','../outside'], AssertionError)]
        for args, error in cases:
            with tempfile.TemporaryDirectory() as temp, self.subTest(args=args), \
                 patch.object(publisher, 'ROOT', Path(temp)), \
                 patch.object(sys, 'argv', ['publisher']+args), \
                 patch.object(zenodo_credentials, 'aws_token') as token:
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(error):
                    publisher.main()
                token.assert_not_called()

    def test_recover_existing_finite_family_without_post(self):
        self.recovery_case('23265066', False)

    def test_reject_wrong_family_before_deposit_calls(self):
        self.recovery_case('23206772', True)

    def recovery_case(self, family, reject):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            old=root/'manuscript/finite-data/deposit/v0.1.0'
            old.mkdir(parents=True)
            (old/'published-record.json').write_text(json.dumps({'files':{}}))
            title='Finite-sample density reconstruction from a single causal order'
            previous={'metadata':{'version':'0.1.0','title':title},
                      'conceptrecid':family,'conceptdoi':'10.5281/zenodo.'+family}
            draft={'id':12345,'submitted':False,'conceptrecid':family,
                   'metadata':{'title':title,'prereserve_doi':{'doi':'10.5281/zenodo.12345'}}}
            calls=[]
            class Response:
                status_code=200
                def __init__(self, data):self.data=data
                def json(self):return self.data
            class Session:
                def __init__(self):self.headers={}
                def request(self, method, url, **kwargs):
                    calls.append((method,url))
                    if method!='GET':raise AssertionError('Must recover without creating')
                    if url.endswith('/23265067'):
                        return Response({'submitted':True,'metadata':{'version':'0.1.0'}})
                    if url.endswith('/12345'):return Response(draft)
                    return Response([draft])
            with patch.object(publisher,'ROOT',root), \
                 patch.object(publisher,'public_record',return_value=previous), \
                 patch.object(publisher,'public_files',return_value={}), \
                 patch.object(publisher.requests,'Session',Session), \
                 patch.object(zenodo_credentials,'aws_token',return_value=('offline-token',{})), \
                 patch.object(sys,'argv',['publisher','--reserve']), contextlib.redirect_stdout(io.StringIO()):
                if reject:
                    with self.assertRaises(AssertionError):publisher.main()
                else:publisher.main()
            if reject:self.assertEqual(calls,[])
            else:
                reservation=json.loads((root/'manuscript/finite-data/deposit/v0.2.0/draft-record.json').read_text())
                self.assertEqual(reservation['previous_record'],23265067)
                self.assertEqual(reservation['conceptrecid'],'23265066')
                self.assertEqual(reservation['id'],12345)
                self.assertTrue(calls and all(method=='GET' for method,_ in calls))


if __name__=='__main__':unittest.main()
