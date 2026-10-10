import hashlib
import importlib.util
import json
import pathlib
import re
import subprocess
import tarfile

sat = pathlib.Path(__file__).resolve().parents[3]
run = 'space-pair3-dev6-20261010T114526Z-23f3f2'
out = sat / 'evidence/gcp' / run
spec = importlib.util.spec_from_file_location('cache_audit', sat / 'tools/check_gcp_incremental_cache.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
verified = audit.inspect_run(out)
manifest = verified['manifest']
assert manifest['target'] == 'QuantyraNullCone.LorentzTimeGeometry'
assert manifest['parent_commit'] == 'cf0bd87df75f5f21299891b4d733088bcad3df8b'
modules = ['LorentzTimeMoments', 'LorentzTimeFamily', 'LorentzTimeEnvelope', 'LorentzTimeGeometry']
expected = []
for module in modules:
    name = 'QuantyraNullCone/' + module + '.lean'
    source = (sat / name).read_text(encoding='utf-8')
    assert not re.search(r'\b(?:sorry|admit)\b|^\s*axiom\s', source, re.M)
    expected += ['QuantyraNullCone.' + n for n in re.findall(r'^#print axioms (\S+)$', source, re.M)]
assert len(expected) == len(set(expected)) == 21
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", verified['stdout'], re.S)
selected = {}
for name, body in reports:
    if name in expected:
        assert name not in selected
        axioms = set(body.replace(',', ' ').split())
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
        selected[name] = sorted(axioms)
assert set(selected) == set(expected)
previous = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', manifest['parent_commit']], cwd=sat, text=True).splitlines()
previous_inputs = {n for n in previous if n.startswith(('QuantyraNullCone/', 'checks/')) or n in {'QuantyraNullCone.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', '.github/workflows/verify.yml'}}
assert set(manifest['source']) - previous_inputs == {'QuantyraNullCone/' + m + '.lean' for m in modules}
for name, sha in manifest['source'].items():
    data = (sat / name).read_bytes().replace(b'\r\n', b'\n')
    assert hashlib.sha256(data).hexdigest() == sha, name
    if name in previous_inputs:
        prior = subprocess.check_output(['git', 'show', manifest['parent_commit'] + ':' + name], cwd=sat)
        assert hashlib.sha256(prior.replace(b'\r\n', b'\n')).hexdigest() == sha, name
assert len(re.findall(r'^#print axioms ', (sat / 'checks/Audit.lean').read_text(encoding='utf-8'), re.M)) == 1165
terminal_runs = {}
captured_runs = [
    'space-pair3-cache1-20261010T111516Z-2272d1',
    'space-pair3-cache2-20261010T112058Z-74fc69',
    'space-pair3-cache3-20261010T112429Z-c7e358',
    'space-pair3-cache4-20261010T112716Z-93b105',
    'space-pair3-cache5-20261010T113018Z-7b7d8a',
    'space-pair3-dev1-20261010T113239Z-98a26c',
    'space-pair3-dev2-20261010T113433Z-ec603f',
    'space-pair3-dev3-20261010T113634Z-49ce1e',
    'space-pair3-dev4-20261010T113849Z-fcd60f',
    'space-pair3-dev5-20261010T114109Z-47b284',
    run,
]
for name in captured_runs:
    path = sat / 'evidence/gcp' / name
    code = int((path / 'exit-code').read_text().strip())
    assert code == (1 if '-dev' in path.name and path.name != run else 0)
    retained = path / (path.name + '-evidence.tar.gz')
    assert retained.is_file()
    with tarfile.open(retained) as bundle:
        assert bundle.extractfile('exit-code').read().decode().strip() == str(code)
    terminal_runs[path.name] = code
verifier_sha256 = hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
result = {
    'verifier_sha256': verifier_sha256,
    'status': 'PASS_TARGETED_GCP_DEVELOPMENT',
    'run': run,
    'campaign': manifest['campaign'],
    'target': manifest['target'],
    'archive_sha256': json.loads((out / 'input-archive.json').read_text())['sha256'],
    'captured_source_files': len(manifest['source']),
    'captured_lean_files': sum(n.endswith('.lean') for n in manifest['source']),
    'new_modules': modules,
    'new_axiom_reports': selected,
    'new_axiom_report_count': len(selected),
    'source_matches_worktree': True,
    'prior_mathematical_inputs_unchanged': len(previous_inputs),
    'prior_source_commit': manifest['parent_commit'],
    'full_acceptance_run': False,
    'accepted_audit_count_unchanged': 1165,
    's042_criteria_complete_unchanged': 3,
    's043_gate_passed': False,
    'warnings': 0,
    'build_seconds': verified['build_seconds'],
    'all_campaign_terminal_outcomes_collected': terminal_runs,
    'cache_checkpoint': verified['checkpoint'],
    'local_lean_invocations': 0,
    'remaining': ['actual pair-law integral', 'order-only statistic and dependence-aware Bernstein probability', 'monotone inverse and complete confidence endpoint', 'full GCP acceptance and S043 decision'],
}
dest = sat / 'evidence/geometric-gauge/pair-campaign-development/development-validation.json'
dest.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in result.items() if k not in {'new_axiom_reports', 'all_campaign_terminal_outcomes_collected'}}, indent=2))
