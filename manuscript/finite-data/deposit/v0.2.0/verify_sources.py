"""Verify source, audit and preservation identities; never execute Lean/Lake."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

folder = Path(__file__).resolve().parent
root = folder.parents[3]
mapping = json.loads((folder / 'formal-map.json').read_text(encoding='utf-8'))
evidence = root / 'evidence/gcp' / mapping['gcp_run']
capture = json.loads((evidence / 'capture-manifest.json').read_text(encoding='utf-8'))
receipt = json.loads((evidence / 'receipt.json').read_text(encoding='utf-8'))
sha = lambda b: hashlib.sha256(b).hexdigest()
assert receipt['acceptance'] and receipt['exit'] == 0
assert receipt['compile_host'] == 'GCP' and receipt['audited_exports'] == 508
assert receipt['owned_warnings'] == 0
assert receipt['source_verified_before_and_after'] and receipt['dependency_identities_before_and_after']
assert len(capture['source']) == 143
eol = {}
for name, expected in capture['source'].items():
    data = (root / name).read_bytes()
    if sha(data) != expected:
        assert b'\r\n' in data and sha(data.replace(b'\r\n', b'\n')) == expected, name
        eol[name] = {'checkout_sha256': sha(data), 'accepted_lf_sha256': expected}
    committed = subprocess.check_output(['git', 'show', f"{mapping['proof_commit']}:{name}"], cwd=root)
    assert sha(committed) == expected, ('Proof revision mismatch', name)
audit = (evidence / 'logs/audit.stdout.txt').read_text(encoding='utf-8')
build = (evidence / 'logs/build.stdout.txt').read_text(encoding='utf-8')
assert 'PASS: proof sources and final Lean dependency reports' in audit
assert not re.search(r'warning:|error:|sorryAx|unsolved goals', audit + build)
jobs = int(re.search(r'Build completed successfully \((\d+) jobs\)', build).group(1))
axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
axioms += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", audit)]
accepted = {n for n, _ in axioms}
assert len(axioms) == len(accepted) == 508
for name, values in axioms:
    assert set(v.strip() for v in values.split(',') if v.strip()) <= {'propext','Classical.choice','Quot.sound'}, name
tex = (folder / mapping['manuscript']).read_text(encoding='utf-8')
names = set()
for claim in mapping['claims']:
    assert r'\label{' + claim['tex_label'] + '}' in tex
    for export in claim['exports']:
        assert export['file'] in capture['source']
        name = export['name']
        assert name in accepted
        assert re.search(r'^' + re.escape(name) + r'(?:\.|\s|\{)', audit, re.M), ('Missing exact type', name)
        source = (root / export['file']).read_text(encoding='utf-8')
        assert re.search(r'\btheorem\s+' + re.escape(name.removeprefix('QuantyraNullCone.')) + r'\b', source)
        names.add(name)
assert len(names) == 101

# Only navigation, EOL control and additive root/audit integration may modify
# existing files. Every other baseline blob, including raw evidence, published
# editions, preparation snapshots and frozen pilot data, is protected.
allowed = {'.gitattributes', 'README.md', 'notes/manuscript-portfolio.md',
           'QuantyraNullCone.lean', 'checks/Audit.lean'}
baseline = mapping['preservation_baseline']
diff = subprocess.check_output(['git','diff','--name-status',baseline],cwd=root).decode().splitlines()
unexpected = [line for line in diff if line.split('\t')[0] != 'A' and line.split('\t')[-1] not in allowed]
assert not unexpected, ('Changed protected baseline files', unexpected)
tree = subprocess.check_output(['git','ls-tree','-r','--name-only',baseline],cwd=root).decode().splitlines()
protected = [p for p in tree if p not in allowed]
result = dict(status='PASS', proof_commit=mapping['proof_commit'], gcp_run=mapping['gcp_run'],
    accepted_source_count=143, current_and_cited_commit_match_accepted_capture=capture['source'],
    checkout_crlf_to_lf_comparisons=eol, mapped_audited_exports=len(names),
    total_accepted_export_reports=len(axioms), root_build_jobs=jobs,
    allowed_axioms=['propext','Classical.choice','Quot.sound'], preservation_baseline=baseline,
    protected_baseline_file_count=len(protected), protected_baseline_files_unchanged=True,
    allowed_modified_baseline_files=sorted(allowed), new_lean_invocations=0,
    raw_evidence_sha256={p.relative_to(root).as_posix():sha(p.read_bytes()) for p in
        [evidence/'capture-manifest.json',evidence/'receipt.json',evidence/'logs/audit.stdout.txt',evidence/'logs/build.stdout.txt']},
    semantic_map_review='Manual mathematical source/type/prose inspection recorded in verification.md and review.json; not inferred from export names')
(folder/'source-verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(f'PASS: 143 identities, 101 mapped exports, 508 reports, {jobs} root jobs; {len(protected)} baseline files protected; no Lean invoked')
