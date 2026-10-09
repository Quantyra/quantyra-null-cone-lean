"""Check exact GCP evidence and staged Git custody; does not invoke Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '4b3a334f9df5fb30f68fcf437d3dd3059ece7930'
parser = argparse.ArgumentParser()
parser.add_argument('--run', required=True)
args = parser.parse_args()
assert re.fullmatch(r'space-thinning-[a-z0-9-]+-\d{8}T\d{6}Z-[0-9a-f]{6}', args.run)
folder = ROOT / 'evidence/gcp' / args.run
capture = json.loads((folder / 'capture-manifest.json').read_text())
receipt = json.loads((folder / 'receipt.json').read_text())
assert receipt['run'] == capture['run'] == args.run
assert receipt['target'] == capture['target'] == 'QuantyraNullCone'
assert capture['project'] == 'quantyra-lean-cert-20260915'
assert capture['instance'] == 'quantyra-lean-builder-01' and capture['zone'] == 'us-central1-a'
assert receipt['acceptance'] and receipt['exit'] == 0
assert receipt['audited_exports'] == 605 and receipt['owned_warnings'] == 0
assert receipt['compile_host'] == capture['compile_host'] == 'GCP'
assert receipt['source_verified_before_and_after']
assert receipt['dependency_identities_before_and_after']
assert (folder / 'exit-code').read_text().strip() == '0'
cleanup = json.loads((folder / 'cleanup.json').read_text())
assert cleanup['campaign_ownership']['started_for_task']
assert cleanup['no_other_lean_work'] and cleanup['stop_verified']
assert cleanup['final_state'] == 'TERMINATED'
sha = lambda data: hashlib.sha256(data).hexdigest()
archive = json.loads((folder / 'input-archive.json').read_text())
assert sha((folder / 'inputs.tar.gz').read_bytes()) == archive['sha256']

# One batch reads exact staged bytes, including the LF-normalized new modules.
names = list(capture['source'])
batch = subprocess.check_output(['git', 'cat-file', '--batch'], cwd=ROOT,
                                input=''.join(':' + name + '\n' for name in names).encode())
offset = 0
for name in names:
    end = batch.index(b'\n', offset)
    header = batch[offset:end].split()
    assert len(header) == 3 and header[1] == b'blob', (name, header)
    size = int(header[2])
    staged = batch[end + 1:end + 1 + size]
    offset = end + 2 + size
    assert sha(staged) == capture['source'][name], ('staged source', name)
    current = (ROOT / name).read_bytes().replace(b'\r\n', b'\n')
    assert sha(current) == capture['source'][name], ('working source', name)
assert offset == len(batch)

audit = (folder / 'logs/audit.stdout.txt').read_text(encoding='utf-8')
build = (folder / 'logs/build.stdout.txt').read_text(encoding='utf-8')
logs = '\n'.join(path.read_text(encoding='utf-8') for path in (folder / 'logs').glob('*.txt'))
assert 'PASS: proof sources and final Lean dependency reports' in audit
assert not re.search(r'warning:|error:|sorryAx|unsolved goals', logs)
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
reports += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", audit)]
reported = {name for name, _ in reports}
assert len(reports) == len(reported) == 605
for name, values in reports:
    assert set(v.strip() for v in values.split(',') if v.strip()) <= {
        'propext', 'Classical.choice', 'Quot.sound'}, name
exports = {}
for path in sorted((ROOT / 'QuantyraNullCone').glob('Thinning*.lean')):
    exports[path.stem] = []
    for short in re.findall(r'^theorem ([\w.]+)', path.read_text(encoding='utf-8'), re.M):
        name = 'QuantyraNullCone.' + short
        assert name in reported, name
        assert re.search(r'^' + re.escape(name) + r'(?:\.\{[^}]*\})?(?:\s|\{|\()', audit, re.M), name
        exports[path.stem].append(name)
assert sum(map(len, exports.values())) == 28
allowed = {'.gitattributes', 'README.md', 'QuantyraNullCone.lean', 'checks/Audit.lean'}
changes = subprocess.check_output(['git', 'diff', '--name-status', BASELINE], cwd=ROOT,
                                  text=True).splitlines()
assert not [line for line in changes if line.split('\t')[0] != 'A'
            and line.split('\t')[-1] not in allowed], 'Protected baseline changed'
pilot = ROOT / 'evidence/marked-volume/pilot-1'
freeze = json.loads((pilot / 'freeze.json').read_text())
for name, digest in freeze['sources'].items():
    assert sha((ROOT / name).read_bytes().replace(b'\r\n', b'\n')) == digest, name
pilot_audit = json.loads((pilot / 'artifact-audit.json').read_text())
assert pilot_audit['passed'] and pilot_audit['exact_interval_certificates'] == 1348
assert pilot_audit['adjacent_inward_endpoint_rejections'] == 2688
assert json.loads((pilot / 'python-tests.json').read_text())['result'] == 'OK'

result = {
    'status': 'PASS', 'run': args.run, 'audited_exports': len(reports),
    'new_exports_by_module': exports,
    'root_build_jobs': int(re.search(r'Build completed successfully \((\d+) jobs\)', build).group(1)),
    'accepted_source_count': len(names), 'all_current_and_staged_source_hashes_match': True,
    'task_owned_vm_cleanup_verified': True,
    'baseline_preserved_except_allowed_integration': BASELINE,
    'allowed_existing_changes': sorted(allowed), 'new_local_lean_invocations': 0,
    'new_samples': 0, 'frozen_pilot_sources_preserved': True,
    'retained_pilot_sha256': {path.name: sha(path.read_bytes()) for path in sorted(pilot.glob('*.json'))},
    'raw_log_sha256': {name: sha((folder / name).read_bytes()) for name in [
        'capture-manifest.json', 'receipt.json', 'cleanup.json', 'input-archive.json', 'run.sh',
        'logs/build.stdout.txt', 'logs/build.stderr.txt',
        'logs/audit.stdout.txt', 'logs/audit.stderr.txt']},
    'limits': ['independent generated-count mixtures, Poisson process and sampling until n remain S040',
               'complete S038 geometric confounding endpoint remains S040',
               'Python/SciPy execution semantics are tested, not Lean compiled',
               'no field detector or operational application validated'],
}
destination = ROOT / 'evidence/thinning/formal-verification.json'
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps({key: value for key, value in result.items()
                  if key not in {'new_exports_by_module', 'raw_log_sha256'}}, indent=2))
