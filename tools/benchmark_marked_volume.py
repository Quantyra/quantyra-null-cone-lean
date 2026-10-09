"""Execute the frozen S040/S041 pilot once into a new evidence directory."""
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
from math import comb
from pathlib import Path
import platform
import subprocess
import time
import tracemalloc

import numpy as np
import scipy
from scipy.stats import binom
from marked_volume import (Interval, analytic_interval, detected_probability,
                           exact_interval, marked_count, retention_interval, verify_interval)

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    out=Path(args.output)
    out.mkdir(parents=True,exist_ok=False)
    paths=['notes/marked-volume-protocol.json','notes/marked-volume-finite-data.md',
           'tools/marked_volume.py','tools/benchmark_marked_volume.py','checks/test_marked_volume.py']
    binding={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in paths}
    frozen={'created_utc':datetime.now(timezone.utc).isoformat(), 'sources':binding,
            'parent_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
            'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__}
    (out/'freeze.json').write_text(json.dumps(frozen,indent=2)+'\n',encoding='utf-8')
    protocol=json.loads((ROOT/paths[0]).read_text())
    started=time.perf_counter()
    tracemalloc.start()
    rng=np.random.default_rng(protocol['seed'])
    rows=[]
    reports={}
    tables=[]
    for n in protocol['sizes']:
        cs=[exact_interval(k,n,F(protocol['delta']),protocol['integer_endpoint_denominator']) for k in range(n+1)]
        certificates=[verify_interval(k,n,c,F(protocol['delta'])) for k,c in enumerate(cs)]
        assert all(certificates)
        hs=[analytic_interval(k,n) for k in range(n+1)]
        reports[n]=cs,hs
        tables.append({'n':n,'endpoints':[[str(c.lower),str(c.upper)] for c in cs],
                       'all_certificates_pass':all(certificates),
                       'adjustments':sum(c.adjustments for c in cs),'fallbacks':sum(c.fallback for c in cs)})
        print('certified table',n,flush=True)
        for ps in protocol['physical_probabilities']:
            p=F(ps)
            for rs in protocol['retention_ratios']:
                r=F(rs)
                for pattern in protocol['retention_patterns']:
                    theta=detected_probability(p,r,pattern)
                    counts=rng.binomial(n,float(theta),protocol['replications_per_cell'])
                    pmf=binom.pmf(np.arange(n+1),n,float(theta))
                    methods={'exact_tail_certified_binomial':[retention_interval(c,r) for c in cs],
                             'analytic_hoeffding':[retention_interval(c,r) for c in hs],
                             'no_data':[Interval(F(0),F(1))]*(n+1),
                             'binomial_ignoring_bias_diagnostic':cs}
                    for method,intervals in methods.items():
                        covered=np.array([c.lower<=p<=c.upper for c in intervals],dtype=bool)
                        widths=np.array([float(c.upper-c.lower) for c in intervals])
                        exact_cov=None
                        if n<=64:
                            exact_cov=sum(F(comb(n,k))*theta**k*(1-theta)**(n-k)
                                          for k in range(n+1) if covered[k])
                        rows.append({'n':n,'p':ps,'R':rs,'pattern':pattern,'theta':str(theta),'method':method,
                                     'coverage_full_law':float(pmf@covered),
                                     'coverage_rational':str(exact_cov) if exact_cov is not None else None,
                                     'coverage_monte_carlo':float(np.mean(covered[counts])),
                                     'mean_width_full_law':float(pmf@widths),
                                     'mean_width_monte_carlo':float(np.mean(widths[counts])),
                                     'width_95th_percentile':float(np.quantile(widths[counts],.95)),
                                     'raw_fraction_mae_physical':float(np.mean(abs(counts/n-float(p)))) if n else None})
    (out/'interval-tables.json').write_text(json.dumps(tables,indent=2)+'\n',encoding='utf-8')
    (out/'cells.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')

    # Actual marked geometry checks use rejection sampling followed by independent detection.
    grng=np.random.default_rng(protocol['seed']+1)
    geometries=[]
    for tilted in (False,True):
        for compensating in (False,True):
            p=F(17,64) if tilted else F(1,4)
            r=F(5,3) if tilted and compensating else F(1)
            covered=[]; widths=[]; counts=[]; proposal_counts=[]
            for _ in range(200):
                chunks=[]; have=proposed=0
                while have<1024:
                    points=grng.random((2048,2)); proposed+=len(points)
                    rho=1+(2*points[:,0]-1)*(2*points[:,1]-1)/4 if tilted else np.ones(len(points))
                    generated=grng.random(len(points))<=rho/1.25
                    retention=.75/rho if compensating else np.full(len(points),.75)
                    detected=grng.random(len(points))<=retention
                    chosen=points[generated&detected]
                    chunks.append(chosen); have+=len(chosen)
                sample=np.concatenate(chunks)[:1024]
                flags=[(bool(u>0 and v>0),bool(u<.5 and v<.5)) for u,v in sample]
                x,n=marked_count(flags)
                assert n==1024 and x==int(np.sum((sample[:,0]<.5)&(sample[:,1]<.5)))
                c=retention_interval(reports[n][0][x],r)
                counts.append(x); proposal_counts.append(proposed)
                covered.append(c.lower<=p<=c.upper);widths.append(float(c.upper-c.lower))
            geometries.append({'density':'polynomial' if tilted else 'flat',
                               'detection':'compensating' if compensating else 'constant',
                               'target':str(p),'R':str(r),'n':1024,'trials':200,
                               'coverage':float(np.mean(covered)),'mean_width':float(np.mean(widths)),
                               'mean_detected_fraction':float(np.mean(counts)/1024),
                               'expected_detected_fraction':float(F(1,4) if compensating else p),
                               'counts':counts,'proposals':proposal_counts})
    (out/'geometry.json').write_text(json.dumps(geometries,indent=2)+'\n',encoding='utf-8')
    elapsed=time.perf_counter()-started
    _,peak=tracemalloc.get_traced_memory();tracemalloc.stop()
    valid=[row for row in rows if row['method']!='binomial_ignoring_bias_diagnostic']
    exact=[row for row in rows if row['method']=='exact_tail_certified_binomial']
    reference={(row['n'],row['p'],row['R'],row['pattern']):row for row in rows if row['method']=='analytic_hoeffding'}
    width_gate=[row for row in exact if row['n']==1024 and F(row['R'])<=F(5,4)]
    validity=(min(row['coverage_full_law'] for row in valid)>=.95-1e-10 and
              all(F(row['coverage_rational'])>=F(19,20) for row in valid if row['coverage_rational'] is not None))
    width_pass=all(row['mean_width_full_law']<=.2 and row['mean_width_full_law']<=reference[
        row['n'],row['p'],row['R'],row['pattern']]['mean_width_full_law'] for row in width_gate)
    resource_pass=(elapsed<=protocol['resource_ceiling']['elapsed_seconds'] and
                   peak<=protocol['resource_ceiling']['peak_python_traced_bytes'])
    for name,sha in binding.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==sha
    summary={'elapsed_seconds':elapsed,'peak_python_traced_bytes':peak,'rows':len(rows),
             'exact_rational_rows':sum(row['coverage_rational'] is not None for row in rows),
             'integer_tail_certificate_failures':0,'endpoint_adjustments':sum(t['adjustments'] for t in tables),
             'fallbacks':sum(t['fallbacks'] for t in tables),'validity_pass':validity,
             'width_gate_pass':width_pass,'resource_gate_pass':resource_pass,
             'minimum_valid_coverage':min(row['coverage_full_law'] for row in valid),
             'minimum_misspecified_coverage':min(row['coverage_full_law'] for row in rows if row['method']=='binomial_ignoring_bias_diagnostic'),
             'maximum_gate_mean_width':max(row['mean_width_full_law'] for row in width_gate),
             'decision':'continue' if validity and resource_pass and width_pass else 'narrow' if validity and resource_pass else 'stop',
             'source_hashes_preserved':True,'scope':'controlled sampling and geometry only; no real detector validation'}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(summary,indent=2),flush=True)


if __name__=='__main__':
    main()
