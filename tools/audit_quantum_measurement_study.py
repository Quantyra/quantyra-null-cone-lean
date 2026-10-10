"""Independent arithmetic and artifact audit for the frozen S047 study.

Does not import the candidate, runner or binomial implementation. Tail
polynomials use a different homogeneous Horner evaluation; full-law weights
use factorial multinomial coefficients. No Lean invocation.
"""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
from fractions import Fraction as F
from math import comb, factorial, floor, fsum, isfinite, lcm, log
import hashlib
import json
import time


def cdf_numerator(n, k, p, q):
    result, qpower = comb(n, k), 1
    for j in range(k-1, -1, -1):
        qpower *= q
        result = result*p + comb(n, j)*qpower
    return result*q**(n-k)


def tail_check(n, k, lower, upper, delta):
    assert 0 <= lower <= upper <= 1
    if not n:
        assert lower == 0 and upper == 1
        return
    if k == 0:
        assert lower == 0
    else:
        # P_p(X>=k) = P_(1-p)(X<=n-k).
        num = cdf_numerator(n, n-k, lower.denominator-lower.numerator, lower.numerator)
        assert 2*num*delta.denominator <= delta.numerator*lower.denominator**n
    if k == n:
        assert upper == 1
    else:
        num = cdf_numerator(n, k, upper.numerator, upper.denominator-upper.numerator)
        assert 2*num*delta.denominator <= delta.numerator*upper.denominator**n


def reference_report(boxes):
    a, b, e, f = boxes
    e, f = (max(F(1, 2), e[0]), e[1]), (max(F(1, 2), f[0]), f[1])
    if e[0] > e[1] or f[0] > f[1]:
        return F(0), F(1), 'empty_calibration'
    # Constraints expressed directly in p and (1-p), solved independently.
    positive = (a[0]/e[1], a[1]/e[0])
    negative = (b[0]/f[1], b[1]/f[0])
    low, high = max(F(0), positive[0], 1-negative[1]), min(F(1), positive[1], 1-negative[0])
    return (low, high, '') if low <= high else (F(0), F(1), 'empty_projection')


def audit(out):
    started = time.perf_counter()
    load = lambda name: json.loads((out/name).read_text(encoding='utf-8'))
    inventory = load('inventory.json')
    for name, item in inventory.items():
        data = (out/name).read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
    manifest = load('manifest.json')
    for name, digest in manifest['source_sha256'].items():
        assert hashlib.sha256((out/'source'/name).read_bytes()).hexdigest() == digest
    spec = manifest['protocol']
    assert spec == json.loads((out/'source/notes/quantum-measurement-protocol.json').read_text())
    marginals = {}
    for row in load('marginals.json'):
        key = (row['n'], row['k'], F(row['delta']))
        assert key not in marginals
        pair = F(row['lower']), F(row['upper'])
        tail_check(*key[:2], *pair, key[2])
        marginals[key] = pair
    def interval(n, k, delta=F(1, 80)):
        return marginals[(n, k, delta)]

    reports = {}
    for line in (out/'reports.jsonl').read_text().splitlines():
        n, m, xp, xm, kp, km, low, high, fallback = json.loads(line)
        key = (n, m, xp, xm, kp, km)
        assert key not in reports and 0 <= xp+xm <= n and 0 <= kp <= m and 0 <= km <= m
        expected = reference_report((interval(n, xp), interval(n, xm), interval(m, kp), interval(m, km)))
        assert expected == (F(low), F(high), fallback)
        reports[key] = expected
    expected_keys = {(n, m, xp, xm, kp, km) for n in spec['exact_n'] for m in spec['exact_m']
        for xp in range(n+1) for xm in range(n-xp+1) for kp in range(m+1) for km in range(m+1)}
    assert set(reports) == expected_keys and len(reports) == spec['expected_count_tuples']
    cells = load('exact-coverage.json')
    assert len(cells) == len(spec['strata'])*len(spec['exact_n'])*len(spec['exact_m'])
    seen_cells = set()
    for cell in cells:
        index, n, m = cell['stratum'], cell['n'], cell['m']
        key = index, n, m
        assert key not in seen_cells
        seen_cells.add(key)
        p, ep, em = map(F, spec['strata'][index]['parameters'])
        probs = p*ep, (1-p)*em, 1-p*ep-(1-p)*em
        d = lcm(*(v.denominator for v in probs))
        a, b, c = [int(v*d) for v in probs]
        denominator = d**n*ep.denominator**m*em.denominator**m
        weights_p = [comb(m, k)*ep.numerator**k*(ep.denominator-ep.numerator)**(m-k) for k in range(m+1)]
        weights_m = [comb(m, k)*em.numerator**k*(em.denominator-em.numerator)**(m-k) for k in range(m+1)]
        covered = fallback = total = 0
        widths = []
        for xp in range(n+1):
            for xm in range(n-xp+1):
                x0 = n-xp-xm
                probe = factorial(n)//(factorial(xp)*factorial(xm)*factorial(x0))*a**xp*b**xm*c**x0
                for kp in range(m+1):
                    for km in range(m+1):
                        low, high, flag = reports[(n, m, xp, xm, kp, km)]
                        weight = probe*weights_p[kp]*weights_m[km]
                        total += weight
                        covered += weight*int(low <= p <= high)
                        fallback += weight*bool(flag)
                        widths.append(float(high-low)*(weight/denominator))
        assert total == denominator
        assert F(covered, denominator) == F(cell['coverage']) >= F(19, 20)
        assert F(fallback, denominator) == F(cell['fallback_probability'])
        assert abs(fsum(widths)-cell['mean_theta_radius_float']) <= 1e-12
        assert cell['coverage_pass'] is True

    diagnostics = load('diagnostics.json')
    seen_diagnostics = set()
    fit_starts = fit_successes = 0
    max_ll_error = 0.
    for row in diagnostics:
        n, xp, xm, m, kp, km = row['counts']
        index = row['stratum']
        key = index, n, m
        assert key not in seen_diagnostics and [n, m] in spec['diagnostic_budgets']
        seen_diagnostics.add(key)
        p, ep, em = map(F, spec['strata'][index]['parameters'])
        exact = [n*p*ep, n*(1-p)*em, n*(1-p*ep-(1-p)*em)]
        counts = [int(v) for v in exact]
        for j in sorted(range(3), key=lambda j: (counts[j]-exact[j], j))[:n-sum(counts)]:
            counts[j] += 1
        assert counts == [xp, xm, row['no_clicks']]
        assert (kp, km) == (floor(m*ep), floor(m*em))
        expected = reference_report((interval(n, xp), interval(n, xm), interval(m, kp), interval(m, km)))
        def check_report(name, value):
            target = row[name]
            assert value == (F(target['lower']), F(target['upper']), target['fallback'])
            assert value[1]-value[0] == F(target['theta_radius'])
        check_report('candidate', expected)
        check_report('baseline', expected)
        check_report('oracle', reference_report((interval(n, xp, F(1, 40)), interval(n, xm, F(1, 40)), (ep, ep), (em, em))))
        assert F(row['naive_p']) == (F(xp, xp+xm) if xp+xm else F(1, 2))
        assert tuple(map(F, row['naive_interval'])) == interval(xp+xm, xp, F(1, 20))
        fit = row['joint_fit']
        assert len(fit['starts']) == 3
        for trial in fit['starts']:
            fit_starts += 1
            fit_successes += trial['success']
            if trial['feasible']:
                q, e1, e2 = trial['point']
                assert 0 <= q <= 1 and .5 <= e1 <= 1 and .5 <= e2 <= 1
                terms = [(xp, q*e1), (xm, (1-q)*e2), (n-xp-xm, 1-q*e1-(1-q)*e2),
                         (kp, e1), (m-kp, 1-e1), (km, e2), (m-km, 1-e2)]
                assert all(v > 0 for k, v in terms if k)
                value = fsum(k*log(v) for k, v in terms if k)
                error = abs(value-trial['loglikelihood'])
                max_ll_error = max(max_ll_error, error)
                assert error <= 1e-8
        eligible = [t for t in fit['starts'] if t['feasible']]
        assert fit['best'] == (max(eligible, key=lambda t:t['loglikelihood']) if eligible else None)
        assert 0 <= row['fit_seconds'] <= row['wall_seconds']
    assert len(diagnostics) == len(spec['strata'])*len(spec['diagnostic_budgets'])
    summary = load('summary.json')
    assert summary['exact_cells'] == len(cells) and summary['count_tuples'] == len(reports)
    assert summary['diagnostic_cases'] == len(diagnostics) and summary['marginal_reports'] == len(marginals)
    assert F(summary['minimum_coverage']) == min(F(c['coverage']) for c in cells)
    assert summary['all_exact_coverage_pass'] and summary['matched_endpoints_equal']
    largest = [r for r in diagnostics if r['counts'][0] == 2048]
    assert summary['largest_budget_cases'] == len(largest)
    assert summary['largest_budget_width_passes'] == sum(F(r['candidate']['theta_radius']) <= F(1, 10) for r in largest)
    assert summary['mean_radius_improvement'] == 0 and not summary['improvement_gate_pass']
    resource = load('resource.json')
    assert resource['outcome'] == 'completed' and resource['exit_code'] == 0
    assert resource['wall_seconds'] <= spec['wall_seconds']
    assert resource['process_tree_peak_rss_bytes'] <= spec['memory_bytes']
    assert resource['peak_job_committed_bytes'] <= spec['memory_bytes']
    return dict(passed=True, exact_cells=len(cells), count_tuples=len(reports),
        marginal_tail_checks=len(marginals), diagnostic_cases=len(diagnostics),
        fit_starts=fit_starts, fit_successes=fit_successes,
        max_likelihood_recheck_error=max_ll_error, wall_seconds=time.perf_counter()-started,
        scope='All recorded exact tails, report tuples, coverage sums, deterministic counts and fit values; '
              'no uniform theorem, optimizer global optimality or Lean acceptance inferred.')


def main():
    import argparse
    from finite_data_resource import supervise
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['run', 'worker'])
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    out = args.destination.resolve()
    if args.mode == 'worker':
        result = audit(out)
        with (out/'audit.json').open('x', encoding='utf-8') as dest:
            json.dump(result, dest, indent=2, allow_nan=False)
            dest.write('\n')
        print(json.dumps(result), flush=True)
        return
    result = supervise('import runpy; script=sys.argv.pop(1); runpy.run_path(script,run_name="__main__")',
        [Path(__file__).resolve(), 'worker', out], out/'audit.log', seconds=900, rss_limit=768*1024**2)
    with (out/'audit-resource.json').open('x', encoding='utf-8') as dest:
        json.dump(result, dest, indent=2)
        dest.write('\n')
    print(json.dumps(result), flush=True)
    if result['outcome'] != 'completed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
