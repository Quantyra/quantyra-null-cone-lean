"""Read-only exact audit of frozen pilot artifacts; no new samples or quantiles."""
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from marked_volume import Interval, tail_at_most, verify_interval

started=time.perf_counter()
folder=ROOT/'evidence/marked-volume/pilot-1'
freeze=json.loads((folder/'freeze.json').read_text())
for name,digest in freeze['sources'].items():
    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    committed=subprocess.check_output(['git','show',freeze['parent_commit']+':'+name],cwd=ROOT)
    assert hashlib.sha256(committed).hexdigest()==digest,name
tables=json.loads((folder/'interval-tables.json').read_text())
certificates=neighbors=0
for table in tables:
    n=table['n']
    assert len(table['endpoints'])==n+1
    for k,pair in enumerate(table['endpoints']):
        l,u=map(F,pair)
        assert verify_interval(k,n,Interval(l,u))
        certificates+=1
        if k>0:
            # Certifies that the exact lower root is within one grid step.
            assert not tail_at_most(n,k,l+F(1,65536),F(1,40),True)
            neighbors+=1
        if k<n:
            assert not tail_at_most(n,k,u-F(1,65536),F(1,40),False)
            neighbors+=1
rows=json.loads((folder/'cells.json').read_text())
assert len(rows)==1200
rational_valid=[F(row['coverage_rational']) for row in rows
                if row['coverage_rational'] is not None and row['method']!='binomial_ignoring_bias_diagnostic']
assert len(rational_valid)==450 and min(rational_valid)>=F(19,20)
geometries=json.loads((folder/'geometry.json').read_text())
assert len(geometries)==4
lookup={table['n']:table['endpoints'] for table in tables}
for geo in geometries:
    assert len(geo['counts'])==200
    p,r=F(geo['target']),F(geo['R'])
    hits=0
    for k in geo['counts']:
        l,u=map(F,lookup[geo['n']][k])
        lower=l/(r-(r-1)*l)
        upper=r*u/(1+(r-1)*u)
        hits+=lower<=p<=upper
    assert hits/200==geo['coverage']
receipt={'date_utc':datetime.now(timezone.utc).isoformat(),
         'source_commit':freeze['parent_commit'],'source_blobs_and_worktree_match_freeze':True,
         'exact_interval_certificates':certificates,'adjacent_inward_endpoint_rejections':neighbors,
         'rounding_error_bound_per_endpoint':'<=1/65536 relative to exact Clopper-Pearson root',
         'exact_rational_valid_coverage_rows':len(rational_valid),
         'geometry_coverage_recomputed_from_counts':True,'new_samples':0,'float_quantile_calls':0,
         'elapsed_seconds':time.perf_counter()-started,'passed':True}
(folder/'artifact-audit.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(receipt,indent=2))
