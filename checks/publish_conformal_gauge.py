"""S029: independent manuscript deposit, with a resumable identity and frozen bytes.

--reserve is the only new-record creation route. An intent marker prevents an
automatic second POST after an uncertain creation outcome. --prepare is local.
--commit checks exact Git and local bytes before any credential access; adding
--publish uploads/publishes only that reserved record. --verify-public is read-only.
No Lean/Lake calls, credential files, authenticated response dumps or POST retries.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import zipfile

import requests

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from publish_manuscript_version import trusted, public_record, public_files

PAPER = ROOT / 'manuscript/conformal-gauge'
PACKAGE = PAPER / 'deposit/v0.1.0'
RESERVATION = PACKAGE / 'draft-record.json'
INTENT = ROOT / 'tmp/conformal-gauge-create-intent.json'
API = 'https://zenodo.org/api'
TITLE = 'A certified coordinate-gauge obstruction for causal-order reconstruction in a 2+1 diamond'
PROOF = '74c1f743d085c63b45ac2bf30008ad5d29b98fbc'
BASELINE = '3b35dc99847a52ed9133557ef2845cf62020640a'
OLD_FAMILIES = {'23206772', '23202762'}
OLD_RECORDS = {23206773, 23214579, 23225029, 23247720, 23202763}
STEM = 'conformal-gauge-counterexample'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8', newline='\n')


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def validate_metadata(metadata):
    assert metadata['title'] == TITLE
    assert metadata['version'] == '0.1.0'
    assert metadata['upload_type'] == 'publication' and metadata['publication_type'] == 'preprint'
    assert metadata['license'] == 'cc-by-4.0' and metadata['access_right'] == 'open'
    assert metadata['creators'] == [{'name': 'Fredriksen, Daniel Eric', 'affiliation': 'Quantyra Inc'}]
    assert 'doi' not in metadata
    assert not any(r['relation'] in {'isVersionOf', 'isNewVersionOf', 'isPreviousVersionOf'}
                   for r in metadata['related_identifiers'])
    assert any(r['identifier'].endswith('/tree/' + PROOF) and r['relation'] == 'isSupplementedBy'
               for r in metadata['related_identifiers'])


def validate_identity(record, reservation=None):
    assert int(record['id']) not in OLD_RECORDS
    assert str(record['conceptrecid']) not in OLD_FAMILIES
    assert record['metadata']['title'] == TITLE
    assert record['metadata']['version'] == '0.1.0'
    if reservation:
        assert record['id'] == reservation['id']
        assert str(record['conceptrecid']) == reservation['conceptrecid']
        doi = record['metadata'].get('doi') or record['metadata']['prereserve_doi']['doi']
        assert doi == reservation['doi']


def authenticated_request():
    from zenodo_credentials import aws_token
    token, _ = aws_token()
    session = requests.Session()
    session.headers['Authorization'] = 'Bearer ' + token

    def request(method, url, **kwargs):
        try:
            response = session.request(method, trusted(url), timeout=60,
                                       allow_redirects=False, **kwargs)
        except requests.RequestException:
            raise RuntimeError('Zenodo transport failure; outcome may be unknown; no automatic retry') from None
        if not 200 <= response.status_code < 300:
            raise RuntimeError(f'Zenodo {method} HTTP {response.status_code}; body withheld')
        return response
    return request


def reserve(metadata):
    request = authenticated_request()
    if RESERVATION.exists():
        reservation = read(RESERVATION)
        draft = request('GET', f"{API}/deposit/depositions/{reservation['id']}").json()
        validate_identity(draft, reservation)
    else:
        candidates = []
        for page in range(1, 51):
            deposits = request('GET', f'{API}/deposit/depositions',
                               params={'size': 100, 'page': page}).json()
            assert isinstance(deposits, list)
            candidates.extend(d for d in deposits if d.get('metadata', {}).get('title') == TITLE)
            if len(deposits) < 100:
                break
        else:
            raise RuntimeError('Deposit listing incomplete; no creation attempted')
        assert len(candidates) <= 1, 'Multiple matching records require inspection'
        if candidates:
            draft = request('GET', f"{API}/deposit/depositions/{candidates[0]['id']}").json()
        else:
            assert not INTENT.exists(), 'Unresolved creation intent; inspect account before retrying'
            INTENT.parent.mkdir(parents=True, exist_ok=True)
            save(INTENT, {'title': TITLE, 'created_utc': datetime.now(timezone.utc).isoformat()})
            draft = request('POST', f'{API}/deposit/depositions', json={'metadata': metadata}).json()
        validate_identity(draft)
        assert not draft['submitted'], 'Existing publication requires inspection, not a duplicate'
        reservation = {'id': draft['id'], 'doi': draft['metadata']['prereserve_doi']['doi'],
                       'conceptrecid': str(draft['conceptrecid']),
                       'conceptdoi': '10.5281/zenodo.' + str(draft['conceptrecid']),
                       'independent_manuscript_family': True, 'version': '0.1.0'}
        save(RESERVATION, reservation)
    print(json.dumps(reservation, indent=2))


def prepare(metadata):
    assert not (PACKAGE / 'published-record.json').exists(), 'Published package is immutable'
    reservation = read(RESERVATION)
    source = (PACKAGE / (STEM + '.tex')).read_text(encoding='utf-8')
    original = subprocess.check_output(['git', 'show', f'{BASELINE}:manuscript/conformal-gauge/{STEM}.tex'], cwd=ROOT).decode()
    assert source.split('\\section{Question, result and scope}', 1)[1] == original.split('\\section{Question, result and scope}', 1)[1]
    assert reservation['doi'] in source and 'unpublished' not in source
    review = read(PACKAGE / 'review.json')
    assert review['all_pages_visually_inspected'] == list(range(1, review['pages'] + 1))
    assert review['files'][STEM + '.pdf'] == sha((PACKAGE / (STEM + '.pdf')).read_bytes())
    assert review['files'][STEM + '.tex'] == sha((PACKAGE / (STEM + '.tex')).read_bytes())
    payload = [p for p in sorted(PACKAGE.iterdir()) if p.is_file() and p.suffix != '.zip'
               and p.name not in {'manifest.json', 'bundle.json', 'published-record.json', 'public-record.json', 'resolution-check.json'}]
    payload += [PAPER / name for name in ('formal-map.json', 'source-verification.json', 'algebra-check.json',
                'literature-comparison.md', 'literature-sources.json', 'check_algebra.py', 'verify_sources.py', 'build.py', 'review.json')]
    payload += [ROOT / 'LICENSES/CC-BY-4.0.txt']
    manifest = {'title': TITLE, 'version': '0.1.0', 'doi': reservation['doi'], 'proof_commit': PROOF,
                'reviewed_draft_commit': BASELINE, 'mathematical_body_unchanged': True,
                'metadata_sha256': sha((PACKAGE / 'zenodo-metadata.json').read_bytes()),
                'files': {p.relative_to(ROOT).as_posix(): {'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size} for p in payload}}
    save(PACKAGE / 'manifest.json', manifest)
    archive_path = PACKAGE / (STEM + '-v0.1.0-source.zip')
    with zipfile.ZipFile(archive_path, 'w') as archive:
        for path in payload + [PACKAGE / 'manifest.json']:
            entry = zipfile.ZipInfo(path.relative_to(ROOT).as_posix(), (2026, 10, 8, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, path.read_bytes())
    with zipfile.ZipFile(archive_path) as archive:
        assert archive.testzip() is None
        for name, info in manifest['files'].items():
            assert sha(archive.read(name)) == info['sha256']
    save(PACKAGE / 'bundle.json', {'file': archive_path.name, 'sha256': sha(archive_path.read_bytes()),
                                  'bytes': archive_path.stat().st_size, 'members': len(payload) + 1})
    print('PASS: unchanged mathematical body, reviewed PDF and deterministic source archive')


def frozen_payload(commit):
    assert re.fullmatch('[0-9a-f]{40}', commit)
    def frozen(path):
        return subprocess.check_output(['git', 'show', f'{commit}:{path.relative_to(ROOT).as_posix()}'], cwd=ROOT)
    for name in ('manifest.json', 'bundle.json', 'draft-record.json', 'zenodo-metadata.json'):
        assert frozen(PACKAGE / name) == (PACKAGE / name).read_bytes(), name
    metadata = read(PACKAGE / 'zenodo-metadata.json')
    validate_metadata(metadata)
    manifest = read(PACKAGE / 'manifest.json')
    assert manifest['proof_commit'] == PROOF
    assert manifest['metadata_sha256'] == sha(frozen(PACKAGE / 'zenodo-metadata.json'))
    for name, info in manifest['files'].items():
        path = (ROOT / name).resolve()
        assert path.is_relative_to(ROOT)
        assert sha(frozen(path)) == info['sha256'] == sha(path.read_bytes()), name
    bundle = read(PACKAGE / 'bundle.json')
    payload = [PACKAGE / (STEM + '.pdf'), PACKAGE / bundle['file']]
    assert payload[1].parent == PACKAGE
    assert sha(frozen(payload[1])) == bundle['sha256']
    for path in payload:
        assert frozen(path) == path.read_bytes()
    assert read(RESERVATION)['doi'] == manifest['doi']
    print('PASS: frozen Git metadata, manifest and upload bytes', flush=True)
    return metadata, read(RESERVATION), payload


def verify_public(commit, metadata, reservation, payload):
    record = public_record(reservation['id'])
    validate_identity(record, reservation)
    actual = record['metadata']
    for key in ('title', 'version', 'creators', 'publication_date', 'description', 'access_right', 'keywords'):
        assert actual[key] == metadata[key], key
    assert actual['license']['id'].lower() == 'cc-by-4.0'
    assert actual['resource_type']['type'] == 'publication' and actual['resource_type']['subtype'] == 'preprint'
    for relation in metadata['related_identifiers']:
        assert relation in actual['related_identifiers'], relation
    verified = public_files(record)
    assert set(verified) == {p.name for p in payload}
    for p in payload:
        assert verified[p.name]['sha256'] == sha(p.read_bytes())
    previous = {}
    for folder in ('', 'v0.3.0', 'v0.3.1', 'v0.4.0'):
        old = read(ROOT / 'manuscript/deposit' / folder / 'published-record.json')
        downloads = public_files(public_record(old['id']))
        assert downloads == old['files']
        previous[str(old['id'])] = downloads
    software = public_record(23202763)
    assert software['metadata']['version'] == '0.1.0'
    historical = read(ROOT / 'evidence/completion-2026-10-07/public-software-record.json')
    assert {(f['key'], f['checksum']) for f in software['files']} == {(f['key'], f['checksum']) for f in historical['files']}
    previous['23202763'] = public_files(software)
    receipt = {'id': record['id'], 'doi': actual['doi'], 'conceptdoi': record['conceptdoi'],
               'url': f"https://zenodo.org/records/{record['id']}", 'version': '0.1.0',
               'source_commit': commit, 'proof_commit': PROOF, 'reviewed_draft_commit': BASELINE,
               'independent_manuscript_family_verified': True,
               'verified_utc': datetime.now(timezone.utc).isoformat(), 'files': verified,
               'prior_manuscript_and_software_downloads_unchanged': previous}
    save(PACKAGE / 'public-record.json', record)
    save(PACKAGE / 'published-record.json', receipt)
    resolution = requests.get('https://doi.org/' + actual['doi'], timeout=60)
    assert resolution.status_code == 200
    assert resolution.url.rstrip('/') == receipt['url']
    pdf_url = receipt['url'] + '/files/' + STEM + '.pdf?download=1'
    pdf = requests.get(pdf_url, timeout=60)
    assert pdf.status_code == 200 and sha(pdf.content) == sha(payload[0].read_bytes())
    save(PACKAGE / 'resolution-check.json', {'doi': actual['doi'], 'resolved_url': resolution.url,
         'doi_http_status': resolution.status_code, 'pdf_url': pdf_url, 'pdf_http_status': pdf.status_code,
         'pdf_sha256': sha(pdf.content), 'verified_utc': datetime.now(timezone.utc).isoformat()})
    print(json.dumps({'doi': actual['doi'], 'url': receipt['url'], 'files': verified,
                      'independent_family': True, 'historical_records_verified': len(previous)}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    for mode in ('reserve', 'prepare', 'publish', 'verify-public'):
        modes.add_argument('--' + mode, action='store_true')
    parser.add_argument('--commit')
    args = parser.parse_args()
    metadata = read(PACKAGE / 'zenodo-metadata.json')
    validate_metadata(metadata)
    if args.reserve or args.prepare:
        assert not args.commit
        return reserve(metadata) if args.reserve else prepare(metadata)
    assert args.commit, '--commit is required'
    metadata, reservation, payload = frozen_payload(args.commit)
    if args.verify_public:
        return verify_public(args.commit, metadata, reservation, payload)
    if not args.publish:
        print('Dry run: no service calls or writes')
        return
    request = authenticated_request()
    record_url = f"{API}/deposit/depositions/{reservation['id']}"
    draft = request('GET', record_url).json()
    validate_identity(draft, reservation)
    if not draft['submitted']:
        existing = {e['filename']: e for e in draft['files']}
        assert set(existing) <= {p.name for p in payload}, 'Unexpected files: no changes made'
        for path in payload:
            if path.name in existing:
                entry = existing[path.name]
                if entry['checksum'].removeprefix('md5:') == hashlib.md5(path.read_bytes()).hexdigest():
                    continue
                request('DELETE', record_url + '/files/' + str(entry['id']))
            with path.open('rb') as stream:
                request('POST', record_url + '/files', data={'name': path.name}, files={'file': (path.name, stream)})
        draft = request('PUT', record_url, json={'metadata': metadata}).json()
        validate_identity(draft, reservation)
        files = {e['filename']: e for e in draft['files']}
        assert set(files) == {p.name for p in payload}
        for p in payload:
            assert files[p.name]['checksum'].removeprefix('md5:') == hashlib.md5(p.read_bytes()).hexdigest()
        for key in ('title', 'version', 'creators', 'publication_date', 'description', 'access_right', 'keywords'):
            assert draft['metadata'][key] == metadata[key], key
        assert draft['metadata']['license'].lower() == 'cc-by-4.0'
        assert draft['metadata']['upload_type'] == 'publication'
        assert draft['metadata']['publication_type'] == 'preprint'
        for relation in metadata['related_identifiers']:
            assert relation in draft['metadata']['related_identifiers']
        print('PASS: reserved independent draft, uploaded checksums and metadata; publishing', flush=True)
        request('POST', record_url + '/actions/publish')
    verify_public(args.commit, metadata, reservation, payload)


if __name__ == '__main__':
    main()
