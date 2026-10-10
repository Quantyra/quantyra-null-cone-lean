"""Validate retained pair-law development artifacts; never invokes Lean or Lake."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tarfile

sat = Path(__file__).resolve().parents[3]
run = 'space-pair3-dev22-20261010T123035Z-433904'
out = sat / 'evidence/gcp' / run
spec = importlib.util.spec_from_file_location('cache_audit', sat / 'tools/check_gcp_incremental_cache.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
verified = audit.inspect_run(out)
manifest = verified['manifest']
assert manifest['target'] == 'QuantyraNullCone.LorentzPairConditioning'
assert manifest['parent_commit'] == 'dc308e46cc4a5400b035c8d541c08c83ebfe245c'
modules = ['LorentzBoost', 'LorentzRadialIntegral', 'LorentzPairInterval',
           'LorentzIntervalVolume', 'LorentzSpatialMoments', 'LorentzAffineMoments',
           'LorentzIntervalMoments', 'LorentzLightConeIntegral', 'LorentzTriangleMoments',
           'LorentzPairIntegral', 'LorentzPairProbability', 'LorentzPairConditioning']
expected = []
for module in modules:
    source = (sat / 'QuantyraNullCone' / (module + '.lean')).read_text(encoding='utf-8')
    assert not re.search(r'\b(?:sorry|admit)\b|^\s*axiom\s', source, re.M)
    expected += ['QuantyraNullCone.' + n for n in re.findall(r'^#print axioms (\S+)$', source, re.M)]
assert len(expected) == len(set(expected))
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", verified['stdout'], re.S)
selected = {}
for name, body in reports:
    if name in expected:
        assert name not in selected
        axioms = set(body.replace(',', ' ').split())
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
        selected[name] = sorted(axioms)
assert set(selected) == set(expected)
prior_names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', manifest['parent_commit']],
                                      cwd=sat, text=True).splitlines()
prior_inputs = {n for n in prior_names if n.startswith(('QuantyraNullCone/', 'checks/')) or n in {
    'QuantyraNullCone.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', '.github/workflows/verify.yml'}}
assert set(manifest['source']) - prior_inputs == {'QuantyraNullCone/' + m + '.lean' for m in modules}
for name, sha in manifest['source'].items():
    data = (sat / name).read_bytes().replace(b'\r\n', b'\n')
    assert hashlib.sha256(data).hexdigest() == sha, name
    if name in prior_inputs:
        prior = subprocess.check_output(['git', 'show', manifest['parent_commit'] + ':' + name], cwd=sat)
        assert hashlib.sha256(prior.replace(b'\r\n', b'\n')).hexdigest() == sha, name
assert (sat / 'checks/Audit.lean').read_text(encoding='utf-8').count('#print axioms ') == 1165
terminal_runs = {}
run_paths = []
for number in range(7, 23):
    paths = list((sat / 'evidence/gcp').glob(f'space-pair3-dev{number}-*'))
    assert len(paths) == 1, (number, paths)
    run_paths += paths
for path in run_paths:
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
result = {
    'status': 'PASS_TARGETED_GCP_DEVELOPMENT', 'run': run, 'target': manifest['target'],
    'campaign': manifest['campaign'],
    'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'archive_sha256': json.loads((out / 'input-archive.json').read_text())['sha256'],
    'captured_source_files': len(manifest['source']),
    'captured_lean_files': sum(n.endswith('.lean') for n in manifest['source']),
    'new_modules': modules, 'new_axiom_reports': selected, 'new_axiom_report_count': len(selected),
    'source_matches_worktree': True, 'prior_mathematical_inputs_unchanged': len(prior_inputs),
    'prior_source_commit': manifest['parent_commit'],
    'full_acceptance_run': False, 'accepted_audit_count_unchanged': 1165,
    's042_criteria_complete_unchanged': 3, 's043_gate_passed': False,
    'warnings': 0, 'build_seconds': verified['build_seconds'],
    'all_campaign_terminal_outcomes_collected': terminal_runs,
    'cache_checkpoint': verified['checkpoint'], 'local_lean_invocations': 0,
    'remaining': ['order-invariant all-pairs statistic and permutation representation',
                  'dependence-aware Bernstein probability bound',
                  'measurable clipped inverse and complete confidence endpoint',
                  'full GCP acceptance and S043 decision'],
}
(Path(__file__).parent / 'development-validation.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in result.items() if k not in {'new_axiom_reports', 'all_campaign_terminal_outcomes_collected'}}, indent=2))
