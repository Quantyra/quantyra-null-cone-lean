"""Immutable, resource-bounded S047 evaluation. No Lean invocation."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
from math import comb, floor, fsum, lcm
import hashlib
import json
import platform
import subprocess
import time

from finite_data_resource import supervise

PROTOCOL = ROOT/'notes/quantum-measurement-protocol.json'
SOURCES = ['notes/quantum-measurement-protocol.json',
    'notes/quantum-measurement-protocol.md', 'notes/quantum-measurement-model.md',
    'notes/quantum-measurement-sources.md',
    'evidence/quantum-measurement/source-inventory.json',
    'tools/quantum_measurement.py', 'tools/test_quantum_measurement.py',
    'tools/run_quantum_measurement_study.py', 'tools/audit_quantum_measurement_study.py',
    'tools/marked_volume.py', 'tools/finite_data_resource.py']


def dump(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as out:
        json.dump(value, out, indent=2, allow_nan=False)
        out.write('\n')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def bin_weights(n, p):
    return ([comb(n, k)*p.numerator**k*(p.denominator-p.numerator)**(n-k)
             for k in range(n+1)], p.denominator**n)


def probe_weights(n, probs):
    d = lcm(*(p.denominator for p in probs))
    nums = [int(p*d) for p in probs]
    weights = {(xp, xm): comb(n, xp)*comb(n-xp, xm)*nums[0]**xp*nums[1]**xm
               * nums[2]**(n-xp-xm) for xp in range(n+1) for xm in range(n-xp+1)}
    return weights, d**n


def rounded_counts(n, probs):
    exact = [n*p for p in probs]
    counts = [floor(x) for x in exact]
    order = sorted(range(3), key=lambda j: (-(exact[j]-counts[j]), j))
    for j in order[:n-sum(counts)]:
        counts[j] += 1
    return counts


def worker(out):
    import numpy
    import scipy
    from marked_volume import Interval, exact_interval
    from quantum_measurement import (ALPHA, DELTA, baseline_box, joint_fit,
                                     probabilities, project_box)
    start = time.perf_counter()
    spec = json.loads(PROTOCOL.read_text(encoding='utf-8'))
    marginal_rows = {}

    @lru_cache(maxsize=None)
    def interval(k, n, delta):
        result = exact_interval(k, n, delta)
        marginal_rows[(n, k, str(delta))] = dict(n=n, k=k, delta=str(delta),
            lower=str(result.lower), upper=str(result.upper),
            adjustments=result.adjustments, fallback=result.fallback)
        return result

    reports = {}
    count_rows = []
    for n in spec['exact_n']:
        for m in spec['exact_m']:
            block = []
            for xp in range(n+1):
                for xm in range(n-xp+1):
                    for kp in range(m+1):
                        for km in range(m+1):
                            boxes = (interval(xp, n, DELTA), interval(xm, n, DELTA),
                                     interval(kp, m, DELTA), interval(km, m, DELTA))
                            report = project_box(*boxes)
                            assert report == baseline_box(*boxes)
                            block.append((xp, xm, kp, km, report))
                            count_rows.append([n, m, xp, xm, kp, km,
                                               str(report.lower), str(report.upper), report.fallback])
            reports[(n, m)] = block
    assert len(count_rows) == spec['expected_count_tuples']
    with (out/'reports.jsonl').open('x', encoding='utf-8', newline='\n') as dest:
        for row in count_rows:
            dest.write(json.dumps(row)+'\n')

    cells = []
    for index, stratum in enumerate(spec['strata']):
        p, ep, em = map(F, stratum['parameters'])
        probs = probabilities(p, ep, em)
        for n in spec['exact_n']:
            pw, pd = probe_weights(n, probs)
            assert sum(pw.values()) == pd
            for m in spec['exact_m']:
                ew1, ed1 = bin_weights(m, ep)
                ew2, ed2 = bin_weights(m, em)
                denominator = pd*ed1*ed2
                covered = fallback = total = 0
                widths = []
                for xp, xm, kp, km, report in reports[(n, m)]:
                    weight = pw[(xp, xm)]*ew1[kp]*ew2[km]
                    total += weight
                    if report.lower <= p <= report.upper:
                        covered += weight
                    if report.fallback:
                        fallback += weight
                    widths.append(float(report.theta_radius)*(weight/denominator))
                assert total == denominator
                coverage = F(covered, denominator)
                cells.append(dict(stratum=index, n=n, m=m, coverage=str(coverage),
                    fallback_probability=str(F(fallback, denominator)),
                    mean_theta_radius_float=fsum(widths),
                    coverage_pass=coverage >= 1-ALPHA))
        print('exact stratum', index, 'complete', flush=True)
    dump(out/'exact-coverage.json', cells)

    diagnostics = []
    for n, m in spec['diagnostic_budgets']:
        for index, stratum in enumerate(spec['strata']):
            case_start = time.perf_counter()
            p, ep, em = map(F, stratum['parameters'])
            probs = probabilities(p, ep, em)
            xp, xm, x0 = rounded_counts(n, probs)
            kp, km = floor(m*ep), floor(m*em)
            counts = (n, xp, xm, m, kp, km)
            boxes = (interval(xp, n, DELTA), interval(xm, n, DELTA),
                     interval(kp, m, DELTA), interval(km, m, DELTA))
            report = project_box(*boxes)
            baseline = baseline_box(*boxes)
            assert report == baseline
            oracle = project_box(interval(xp, n, ALPHA/2), interval(xm, n, ALPHA/2),
                                 Interval(ep, ep), Interval(em, em))
            naive_p = F(xp, xp+xm) if xp+xm else F(1, 2)
            naive = interval(xp, xp+xm, ALPHA)
            fit_start = time.perf_counter()
            fit = joint_fit(counts)
            fit_seconds = time.perf_counter()-fit_start
            def serialize(r):
                return dict(lower=str(r.lower), upper=str(r.upper),
                            theta_radius=str(r.theta_radius), fallback=r.fallback)
            diagnostics.append(dict(stratum=index, counts=counts, no_clicks=x0,
                candidate=serialize(report), baseline=serialize(baseline),
                oracle=serialize(oracle), naive_p=str(naive_p),
                naive_interval=[str(naive.lower), str(naive.upper)], joint_fit=fit,
                fit_seconds=fit_seconds, wall_seconds=time.perf_counter()-case_start))
        print('diagnostic budget', n, m, 'complete', flush=True)
    dump(out/'diagnostics.json', diagnostics)
    dump(out/'marginals.json', list(marginal_rows.values()))
    largest = [d for d in diagnostics if d['counts'][0] == 2048]
    good_width = [d for d in largest if F(d['candidate']['theta_radius']) <= F(1, 10)]
    summary = dict(exact_cells=len(cells), count_tuples=len(count_rows),
        diagnostic_cases=len(diagnostics), marginal_reports=len(marginal_rows),
        minimum_coverage=str(min(F(c['coverage']) for c in cells)),
        all_exact_coverage_pass=all(c['coverage_pass'] for c in cells),
        matched_endpoints_equal=True, largest_budget_width_passes=len(good_width),
        largest_budget_cases=len(largest), mean_radius_improvement=0,
        improvement_gate_pass=False, worker_seconds=time.perf_counter()-start,
        versions=dict(python=platform.python_version(), numpy=numpy.__version__,
                      scipy=scipy.__version__),
        limitations='Exact coverage grid is not uniform proof; near-mean cases are not random trials; '
                    'joint fits have no global optimum or confidence certificate.')
    dump(out/'summary.json', summary)
    print(json.dumps(summary), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['run', 'worker'])
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    out = args.destination.resolve()
    if args.mode == 'worker':
        worker(out)
        return
    out.mkdir(parents=True, exist_ok=False)
    spec = json.loads(PROTOCOL.read_text(encoding='utf-8'))
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    records = {}
    for name in SOURCES:
        blob = subprocess.check_output(['git', 'show', head+':'+name], cwd=ROOT)
        local = (ROOT/name).read_bytes().replace(b'\r\n', b'\n')
        assert blob == local, 'Uncommitted frozen source: '+name
        records[name] = hashlib.sha256(blob).hexdigest()
        target = out/'source'/name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(blob)
    dump(out/'manifest.json', dict(source_commit=head, source_sha256=records,
        started_utc=datetime.now(timezone.utc).isoformat(), protocol=spec,
        execution='local Python only; no Lean invocation'))
    result = supervise('import runpy; script=sys.argv.pop(1); runpy.run_path(script,run_name="__main__")',
        [Path(__file__).resolve(), 'worker', out], out/'worker.log',
        seconds=spec['wall_seconds'], rss_limit=spec['memory_bytes'])
    dump(out/'resource.json', result)
    inventory = {p.relative_to(out).as_posix(): dict(sha256=sha(p), bytes=p.stat().st_size)
                 for p in sorted(out.rglob('*')) if p.is_file()}
    dump(out/'inventory.json', inventory)
    print(json.dumps(result), flush=True)
    if result['outcome'] != 'completed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
