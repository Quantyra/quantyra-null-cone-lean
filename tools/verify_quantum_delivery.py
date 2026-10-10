"""Verify S047 source/archive identities and raw Git custody without Lean."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(run, staged=False):
    study = ROOT/'evidence/quantum-measurement/feasibility-v1'
    acceptance = ROOT/'evidence/gcp'/run
    load = lambda path: json.loads(path.read_text(encoding='utf-8'))
    manifest = load(study/'manifest.json')
    for name, wanted in manifest['source_sha256'].items():
        source = subprocess.check_output(['git', 'show', manifest['source_commit']+':'+name], cwd=ROOT)
        assert digest(source) == wanted == digest((study/'source'/name).read_bytes()), name
    inventory = load(study/'inventory.json')
    for name, item in inventory.items():
        data = (study/name).read_bytes()
        assert len(data) == item['bytes'] and digest(data) == item['sha256'], name
    assert load(study/'audit.json')['passed']
    capture = load(acceptance/'capture-manifest.json')
    archive = (acceptance/'inputs.tar.gz').read_bytes()
    assert digest(archive) == load(acceptance/'input-archive.json')['sha256']
    source_blobs = {}
    with tarfile.open(acceptance/'inputs.tar.gz', 'r:gz') as bundle:
        for item in bundle.getmembers():
            assert item.isfile() and item.name in capture['source']
            data = bundle.extractfile(item).read()
            assert digest(data) == capture['source'][item.name], item.name
            source_blobs[item.name] = data
    assert set(source_blobs) == set(capture['source'])
    receipt = load(acceptance/'receipt.json')
    assert receipt['acceptance'] and receipt['exit'] == 0 and receipt['owned_warnings'] == 0
    assert receipt['source_verified_before_and_after'] and receipt['dependency_identities_before_and_after']
    assert (acceptance/'exit-code').read_text().strip() == '0'
    names = re.findall(r'^#print axioms (\S+)', source_blobs['checks/Audit.lean'].decode(), re.M)
    assert len(names) == len(set(names)) == receipt['audited_exports']
    log = (acceptance/'logs/audit.stdout.txt').read_text(encoding='utf-8')
    found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", log)
    assert sorted([name for name, _ in found]+empty) == sorted(names)
    for name, axioms in found:
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext','Classical.choice','Quot.sound'}, name
    for path in (acceptance/'logs').glob('*.txt'):
        assert not re.search(r'warning:|error:|unsolved goals|sorryAx', path.read_text(encoding='utf-8')), path.name
    # Raw blobs, including CRLF controller transcripts, must survive Git unchanged.
    git_args = ['git', 'ls-files', '--stage', '-z'] if staged else ['git', 'ls-tree', '-r', '-z', 'HEAD']
    entries = subprocess.check_output(git_args, cwd=ROOT).split(b'\0')
    git_hashes = {}
    for entry in entries:
        if not entry:
            continue
        meta, name = entry.split(b'\t', 1)
        parts = meta.split()
        git_hashes[name.decode()] = parts[1 if staged else 2].decode()
    def blob_id(data):
        return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    for name, data in source_blobs.items():
        assert git_hashes.get(name) == blob_id(data), 'Current proof differs: '+name
    raw_roots = [ROOT/'evidence/quantum-measurement'] + sorted((ROOT/'evidence/gcp').glob('space-qubit-*'))
    raw_files = total_bytes = 0
    for folder in raw_roots:
        for path in sorted(folder.rglob('*')):
            if not path.is_file() or path.name == 'delivery.json':
                continue
            name = path.relative_to(ROOT).as_posix()
            data = path.read_bytes()
            assert git_hashes.get(name) == blob_id(data), 'Raw Git mismatch: '+name
            raw_files += 1
            total_bytes += len(data)
    return dict(passed=True, run=run, source_files=len(source_blobs),
        audited_exports=len(names), numerical_source_commit=manifest['source_commit'],
        study_inventory_files=len(inventory), raw_evidence_files=raw_files,
        raw_evidence_bytes=total_bytes, git_scope='index' if staged else 'HEAD',
        archive_sha256=digest(archive),
        scope='Exact source and raw Git custody; the numerical audit and GCP logs are separate acceptance evidence.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('run')
    parser.add_argument('--staged', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.run, args.staged)
    if args.output:
        with args.output.open('x', encoding='utf-8') as dest:
            json.dump(result, dest, indent=2)
            dest.write('\n')
    print(json.dumps(result, indent=2))
