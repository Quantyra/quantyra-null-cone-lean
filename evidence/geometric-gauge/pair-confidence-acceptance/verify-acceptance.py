"""Validate immutable GCP confidence evidence and exact committed inputs; no Lean invocation."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tarfile

sat = Path(__file__).resolve().parents[3]
run = 'space-pair3-acceptance-20261010T130617Z-981811'
proof_commit = 'f4672c4ea5290e65759253e8052efae270702cbb'
baseline = 'b5aa9aed937a1dca8fbcf0c7928e9dc4061f1c02'
out = sat / 'evidence/gcp' / run
spec = importlib.util.spec_from_file_location('cache_audit', sat / 'tools/check_gcp_incremental_cache.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
verified = audit.inspect_run(out)
manifest = verified['manifest']
assert manifest['target'] == 'QuantyraNullCone'
assert manifest['parent_commit'] == proof_commit
receipt = json.loads((out / 'receipt.json').read_text())
assert receipt['acceptance'] and receipt['audited_exports'] == 1276
assert receipt['dependency_identities_before_and_after'] and receipt['owned_warnings'] == 0

def blob(commit, name):
    return subprocess.check_output(['git', 'show', commit + ':' + name], cwd=sat)

for name, sha in manifest['source'].items():
    assert hashlib.sha256(blob(proof_commit, name)).hexdigest() == sha, name
    assert hashlib.sha256((sat / name).read_bytes().replace(b'\r\n', b'\n')).hexdigest() == sha, name

prior = json.loads((sat / 'evidence/gcp/space-open3-acceptance-20261010T104116Z-16cc4f/capture-manifest.json').read_text())
registry = {'QuantyraNullCone.lean', 'checks/Audit.lean', 'checks/check_integrity.py'}
for name, sha in prior['source'].items():
    if name not in registry:
        assert manifest['source'][name] == sha, name
new_modules = sorted(set(manifest['source']) - set(prior['source']))
assert len(new_modules) == 27 and all(n.startswith('QuantyraNullCone/') and n.endswith('.lean') for n in new_modules)
old_audit = blob(baseline, 'checks/Audit.lean').decode('utf-8')
current_audit = (sat / 'checks/Audit.lean').read_text(encoding='utf-8')
assert current_audit.startswith(old_audit)
expected = re.findall(r'^#print axioms (\S+)$', current_audit, re.M)
checks = re.findall(r'^#check (\S+)$', current_audit, re.M)
assert len(expected) == len(set(expected)) == 1276
assert set(expected) <= set(checks)
stdout = (out / 'logs/audit.stdout.txt').read_text(encoding='utf-8')
stderr = (out / 'logs/audit.stderr.txt').read_text(encoding='utf-8')
assert not re.search(r'warning:|error:|unsolved goals|sorryAx', stdout + '\n' + stderr)
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", stdout, re.S)
empty_reports = re.findall(r"'([^']+)' does not depend on any axioms", stdout)
names = [n for n, _ in reports] + empty_reports
assert len(names) == len(set(names)) == 1276 and set(names) == set(expected)
for name, body in reports:
    assert set(body.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}, name
for name in expected:
    assert re.search(r'^' + re.escape(name) + r'(?:\.\{[^\n}]+\})?(?:\s|:)', stdout, re.M), name
assert 'PASS: proof sources and final Lean dependency reports' in stdout
for path in [sat / n for n in new_modules]:
    assert not re.search(r'\b(?:sorry|admit)\b|^\s*axiom\s', path.read_text(encoding='utf-8'), re.M)

terminal_runs = {}
paths = []
for number in range(23, 33):
    candidates = list((sat / 'evidence/gcp').glob(f'space-pair3-dev{number}-*'))
    assert len(candidates) == 1
    paths.extend(candidates)
paths.append(out)
for path in paths:
    code = int((path / 'exit-code').read_text().strip())
    assert code in (0, 1)
    capture = json.loads((path / 'capture-manifest.json').read_text())
    inputs = path / 'inputs.tar.gz'
    assert hashlib.sha256(inputs.read_bytes()).hexdigest() == json.loads((path / 'input-archive.json').read_text())['sha256']
    with tarfile.open(inputs) as bundle:
        assert set(bundle.getnames()) == set(capture['source'])
        for name, sha in capture['source'].items():
            assert hashlib.sha256(bundle.extractfile(name).read()).hexdigest() == sha, (path.name, name)
    with tarfile.open(path / (path.name + '-evidence.tar.gz')) as bundle:
        for member in bundle.getmembers():
            if member.isfile():
                assert bundle.extractfile(member).read() == (path / member.name).read_bytes(), (path.name, member.name)
    log = (path / 'logs/build.stdout.txt').read_text(encoding='utf-8')
    terminal_runs[path.name] = {'exit': code, 'warnings': len(re.findall(r'^warning:', log, re.M))}

maintenance_path = paths[0]
maintenance = json.loads((maintenance_path / 'maintenance-custody.json').read_text())
assert hashlib.sha256((maintenance_path / maintenance['archive']).read_bytes()).hexdigest() == maintenance['sha256']
with tarfile.open(maintenance_path / maintenance['archive']) as bundle:
    for member in bundle.getmembers():
        if member.isfile():
            assert bundle.extractfile(member).read() == (maintenance_path / member.name).read_bytes()

changed = subprocess.check_output(['git', 'diff', '--name-only', baseline, proof_commit], cwd=sat, text=True).splitlines()
assert not any(n.startswith(('manuscript/', 'evidence/finite-data/', 'evidence/marked-volume/',
                             'evidence/binomial/', 'evidence/thinning/', 'evidence/process/',
                             'evidence/stopping/', 'evidence/firstretained/', 'evidence/confounding/',
                             'evidence/volumeupper/', 'evidence/volumerate/')) for n in changed)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', verified['stdout'])
assert len(jobs) == 1
result = {
    'status': 'PASS_FULL_GCP_ACCEPTANCE', 'run': run, 'source_commit': proof_commit,
    'baseline_commit': baseline, 'captured_files': len(manifest['source']),
    'lean_inputs': sum(n.endswith('.lean') for n in manifest['source']),
    'source_matches_committed_raw_blobs_and_normalized_local': True,
    'input_archive_sha256': json.loads((out / 'input-archive.json').read_text())['sha256'],
    'audited_named_exports': len(expected), 'new_reports': len(expected) - 1165,
    'new_modules': new_modules, 'root_build_jobs': int(jobs[0]), 'warnings': 0,
    'standard_axioms_only': True, 'prior_1165_audit_statements_preserved': True,
    'earlier_mathematical_modules_unchanged': True, 'published_manuscripts_and_frozen_studies_preserved': True,
    'build_seconds': verified['build_seconds'], 'cache_checkpoint': verified['checkpoint'],
    'all_campaign_terminal_outcomes_collected': terminal_runs, 'maintenance_custody_verified': True,
    'local_lean_invocations': 0, 'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'scope': 'Restricted time-quadratic family, actual all-pairs unlabeled observation, original geometric loss. External smooth reconstruction converse unchanged. No full-class rate, sharpness or practical utility claim.',
}
(Path(__file__).parent / 'acceptance-validation.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in result.items() if k not in {'new_modules', 'all_campaign_terminal_outcomes_collected'}}, indent=2))
