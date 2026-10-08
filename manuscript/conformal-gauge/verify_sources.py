"""Read-only Lean evidence verification plus a manuscript receipt; no Lean/Lake.

Checks source hashes and retained accepted type/axiom reports. This cannot
automatically prove correspondence between prose and formal statements.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parent
ROOT=P.parents[1]
mapping=json.loads((P/'formal-map.json').read_text(encoding='utf-8'))
evidence=ROOT/'evidence/gcp'/mapping['gcp_run']
capture=json.loads((evidence/'capture-manifest.json').read_text())
receipt=json.loads((evidence/'receipt.json').read_text())
assert receipt['acceptance'] and receipt['exit']==0 and receipt['compile_host']=='GCP'
assert receipt['audited_exports']==295 and receipt['owned_warnings']==0
assert receipt['source_verified_before_and_after'] and receipt['dependency_identities_before_and_after']
sha=lambda b:hashlib.sha256(b).hexdigest()
selected={name:expected for name,expected in capture['source'].items()
          if name.endswith('.lean') or name in {'lean-toolchain','lakefile.toml','lake-manifest.json',
             'checks/check_integrity.py','.github/workflows/verify.yml'}}
for name,expected in selected.items():
    assert sha((ROOT/name).read_bytes())==expected, ('Current bytes differ from accepted capture',name)
    committed=subprocess.check_output(['git','show',f"{mapping['proof_commit']}:{name}"],cwd=ROOT)
    assert sha(committed)==expected, ('Cited proof revision differs from accepted capture',name)
audit=(evidence/'logs/audit.stdout.txt').read_text(encoding='utf-8')
build=(evidence/'logs/build.stdout.txt').read_text(encoding='utf-8')
assert 'Build completed successfully (3001 jobs).' in build
assert 'PASS: proof sources and final Lean dependency reports' in audit
axioms=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",audit)
axioms += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",audit)]
assert len(axioms)==295
for name,values in axioms:
    assert set(v.strip() for v in values.split(',') if v.strip()) <= {'propext','Classical.choice','Quot.sound'},name
accepted={name for name,_ in axioms}
assert len(accepted)==295
names=set()
for claim in mapping['claims']:
    for export in claim['exports']:
        assert export['file'] in selected
        name=export['name'];names.add(name)
        source=(ROOT/export['file']).read_text(encoding='utf-8')
        assert re.search(r'\btheorem\s+'+re.escape(name.split('.')[-1])+r'\b',source),name
        if export['audit_kind']=='selected_type_and_axiom_report':
            assert name in accepted, ('Mapped theorem missing from accepted audit',name)
        else:
            assert export['audit_kind']=='compiled_dependency'
            assert export['audited_parent'] in accepted
            parent_body=source.split('theorem '+export['audited_parent'].split('.')[-1],1)[1]
            parent_body=parent_body.split('\ntheorem ',1)[0]
            assert name.split('.')[-1] in parent_body
preserved={}
for folder in ['', 'v0.3.0','v0.3.1','v0.4.0']:
    package=ROOT/'manuscript/deposit'/folder
    old=json.loads((package/'published-record.json').read_text())
    # Original 0.2 payload can reside at the root manuscript rather than the deposit directory.
    for name,info in old['files'].items():
        path=package/name
        if path.exists():
            assert sha(path.read_bytes())==info['sha256'],path
            preserved[path.relative_to(ROOT).as_posix()]=info['sha256']
assert not subprocess.check_output(['git','diff','2e581adfa22722f264f91055139158a37519a773','--',
    'manuscript/deposit','manuscript/revisions','manuscript/working',
    'manuscript/finite-causal-order-reconstruction.tex','manuscript/finite-causal-order-reconstruction.pdf',
    '.zenodo.json','CITATION.cff'],cwd=ROOT)
result={'status':'PASS','proof_commit':mapping['proof_commit'],'gcp_run':mapping['gcp_run'],
        'current_and_cited_commit_match_accepted_capture':selected,
        'accepted_selected_source_count':len(selected),'mapped_unique_exports':len(names),
        'mapped_separately_audited_exports':len(names & accepted),
        'mapped_compiled_dependency_exports':sorted(names-accepted),
        'total_accepted_export_reports':len(axioms),'root_build_jobs':3001,
        'allowed_axioms':['propext','Classical.choice','Quot.sound'],
        'captured_publication_utilities_excluded':'The publisher and its tests changed during S027; no assertion that every captured utility is unchanged.',
        'prior_payload_hashes':preserved,'prior_deposits_review_candidates_software_metadata_unchanged':True,
        'new_lean_invocations':0,'semantic_map_review':'Manual statement/source inspection; not inferred solely from occurrence checks.'}
(P/'source-verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print('PASS:',len(selected),'accepted source identities;',len(names),'mapped exports;',len(axioms),'retained audit reports; prior artifacts preserved')
