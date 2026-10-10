"""Verify retained S043 evidence against raw staged Git blobs before delivery.

Does not rerun the numerical study or modify any run artifact. The independent
study audit has already checked statistical/count/seed/resource contracts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def git(*args, data=None):
    return subprocess.check_output(['git', *args], cwd=ROOT, input=data)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify():
    base = ROOT/'evidence/geometric-gauge'
    study = base/'pair-numerical-v2'
    summary = json.loads((study/'audit/summary.json').read_text())
    resource = json.loads((study/'audit/resource.json').read_text())
    if not summary['audit_passed_for_retained_results'] or resource['outcome'] != 'completed':
        raise RuntimeError('completed independent audit required')
    for item in summary['inventory']:
        data = (study/item['path']).read_bytes()
        if digest(data) != item['sha256'] or len(data) != item['bytes']:
            raise RuntimeError('raw inventory mismatch: '+item['path'])
    if git('diff', '--name-only', '44195bacca7032ff86eadcc6f1b66650246c9454',
           '--', 'QuantyraNullCone', 'manuscript', 'lean-toolchain', 'lake-manifest.json').strip():
        raise RuntimeError('accepted proof/publication/dependency inputs changed')
    paths = sorted(path for folder in ('pair-numerical-v1', 'pair-numerical-v2')
                   for path in (base/folder).rglob('*') if path.is_file())
    names = [path.relative_to(ROOT).as_posix() for path in paths]
    # One binary-safe batch avoids thousands of subprocesses and Windows argv limits.
    response = git('cat-file', '--batch', data=''.join(':'+s+'\n' for s in names).encode())
    offset, total_bytes = 0, 0
    for path, name in zip(paths, names):
        header_end = response.index(b'\n', offset)
        fields = response[offset:header_end].split()
        if len(fields) != 3 or fields[1] != b'blob':
            raise RuntimeError('missing/nonblob staged evidence: '+name)
        size = int(fields[2]); offset = header_end+1
        raw = response[offset:offset+size]; offset += size
        if response[offset:offset+1] != b'\n':
            raise RuntimeError('Git batch framing mismatch')
        offset += 1
        if raw != path.read_bytes():
            raise RuntimeError('staged raw bytes differ: '+name)
        total_bytes += size
    if offset != len(response):
        raise RuntimeError('unparsed Git batch bytes')
    old = base/'pair-numerical-v1'
    old_exit = json.loads((old/'execution.json').read_text())
    if list((old/'cases').glob('*')) or old_exit['outcome'] != 'worker_failed':
        raise RuntimeError('original pre-sampling failure history changed')
    return {'status': 'PASS', 'scope': 'raw staged evidence; independent numerical audit; preservation',
        'raw_staged_files': len(paths), 'raw_staged_bytes': total_bytes,
        'study_complete': summary['complete_study'], 'completed_cases': summary['completed_cases'],
        'raw_inventory_files_verified': len(summary['inventory']),
        'audit_summary_sha256': digest((study/'audit/summary.json').read_bytes()),
        'audit_resource_sha256': digest((study/'audit/resource.json').read_bytes()),
        'accepted_proofs_and_manuscripts_preserved': True,
        'original_pre_data_failure_preserved': True,
        'note': 'Targeted raw-evidence attributes preserve original line endings. All v1 and '
                'v2 local evidence bytes match the raw staged blobs; neither run was rewritten.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = verify()
    with args.output.open('x', encoding='utf-8', newline='\n') as out:
        json.dump(result, out, indent=2); out.write('\n')
    print(json.dumps(result))
