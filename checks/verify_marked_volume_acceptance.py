"""Verify retained GCP acceptance and staged source custody without invoking Lean."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
RUN='space-marked-volume-calibration-20261009T193939Z-b7f4f7'
BASELINE='bd2c1a4dff9c98abdec48b39d42cefe52aa4cbc5'
folder=ROOT/'evidence/gcp'/RUN
capture=json.loads((folder/'capture-manifest.json').read_text())
receipt=json.loads((folder/'receipt.json').read_text())
assert receipt['acceptance'] and receipt['exit']==0 and receipt['audited_exports']==532
assert receipt['compile_host']=='GCP' and receipt['owned_warnings']==0
assert receipt['source_verified_before_and_after'] and receipt['dependency_identities_before_and_after']
assert (folder/'exit-code').read_text().strip()=='0'
sha=lambda b:hashlib.sha256(b).hexdigest()
for name,digest in capture['source'].items():
    assert sha((ROOT/name).read_bytes().replace(b'\r\n',b'\n'))==digest,name
    staged=subprocess.check_output(['git','show',':'+name],cwd=ROOT)
    assert sha(staged)==digest,('staged bytes differ',name)
audit=(folder/'logs/audit.stdout.txt').read_text(encoding='utf-8')
build=(folder/'logs/build.stdout.txt').read_text(encoding='utf-8')
assert 'PASS: proof sources and final Lean dependency reports' in audit
assert not re.search(r'warning:|error:|sorryAx|unsolved goals',audit+build)
reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",audit)
reports += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",audit)]
assert len(reports)==len({n for n,_ in reports})==532
for name,values in reports:
    assert set(v.strip() for v in values.split(',') if v.strip())<={'propext','Classical.choice','Quot.sound'},name
exports=[]
for module in ['MarkedVolume','MarkedThinning']:
    text=(ROOT/f'QuantyraNullCone/{module}.lean').read_text(encoding='utf-8')
    for short in re.findall(r'^theorem (\w+)',text,re.M):
        name='QuantyraNullCone.'+short
        assert name in {n for n,_ in reports}
        assert re.search(r'^'+re.escape(name)+r'(?:\.|\s|\{)',audit,re.M),name
        exports.append(name)
assert len(exports)==24
allowed={'.gitattributes','README.md','QuantyraNullCone.lean','checks/Audit.lean'}
changes=subprocess.check_output(['git','diff','--name-status',BASELINE],cwd=ROOT,text=True).splitlines()
assert not [line for line in changes if line.split('\t')[0]!='A' and line.split('\t')[-1] not in allowed]
result={'status':'PASS','run':RUN,'audited_exports':532,'new_exports':exports,
        'root_build_jobs':int(re.search(r'Build completed successfully \((\d+) jobs\)',build).group(1)),
        'accepted_source_count':len(capture['source']),'all_current_and_staged_source_hashes_match':True,
        'baseline_preserved_except_allowed_integration':BASELINE,'allowed_existing_changes':sorted(allowed),
        'new_local_lean_invocations':0,'raw_log_sha256':{n:sha((folder/n).read_bytes()) for n in
          ['capture-manifest.json','receipt.json','logs/build.stdout.txt','logs/audit.stdout.txt']},
        'limits':['exact-binomial count-law/inversion not yet formalized',
                  'process-level iid thinning/Poisson bridge not yet formalized',
                  'complete S038 confounding endpoint not yet formalized',
                  'Python execution semantics are tested, not Lean compiled']}
(ROOT/'evidence/marked-volume/formal-verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k not in ['new_exports','raw_log_sha256']},indent=2))
