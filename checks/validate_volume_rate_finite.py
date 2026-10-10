"""Execute the frozen S046 deterministic comparison; never invokes Lean."""
import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
from math import comb
from pathlib import Path
import platform
import subprocess
import sys
import time
import traceback
import tracemalloc

ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = 'notes/physical-volume-finite-protocol.json'
sys.path.insert(0, str(ROOT / 'tools'))
from marked_volume import (Interval, analytic_interval, detected_probability,
                           exact_interval, retention_interval, verify_interval)


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(out, name, value):
    (out / name).write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def product(p, q):
    result = {}
    for (i, j), a in p.items():
        for (k, l), b in q.items():
            result[i+k, j+l] = result.get((i+k, j+l), F(0)) + a*b
    return result


def density(epsilon):
    p = {key: epsilon*value for key, value in product(
        {(1, 0): F(2), (0, 0): F(-1)},
        {(0, 1): F(2), (0, 0): F(-1)}).items()}
    p[0, 0] += 1
    return p


def integral(p, upper_u=F(1), upper_v=F(1)):
    return sum((c*upper_u**(i+1)*upper_v**(j+1)/((i+1)*(j+1))
                for (i, j), c in p.items()), F(0))


def evaluate(p, u, v):
    return sum((c*u**i*v**j for (i, j), c in p.items()), F(0))


def ratios(protocol, q=None):
    result = {F(r) for r in protocol['base_retention_ratios']}
    if q is not None:
        for b in {F(1, 2*q), F(1, q), min(F(2, q), F(1, 3))}:
            if 0 <= b <= F(1, 3):
                result.add((1+b)/(1-b))
    return sorted(result)


def clipped(pair):
    return max(F(1, 8), pair[0]), min(F(3, 8), pair[1])


def width(pair):
    return max(F(0), pair[1]-pair[0])


def enclosure(value):
    d = 10**12
    lower = value.numerator*d // value.denominator
    upper = -((-value.numerator*d) // value.denominator)
    return {'lower': str(F(lower, d)), 'upper': str(F(upper, d))}


def reports(n, q, k, r, cp, hoeffding):
    if n == 0:
        return {m: (F(1, 8), F(3, 8)) for m in (
            'transformed_exact_binomial', 'transformed_hoeffding', 'joint_rate', 'known_range')}
    c, h = retention_interval(cp, r), retention_interval(hoeffding, r)
    radius = 2*min(F(1), F(1, q)+(r-1)/(r+1))
    return {
        'transformed_exact_binomial': clipped((c.lower, c.upper)),
        'transformed_hoeffding': clipped((h.lower, h.upper)),
        'joint_rate': clipped((F(k, n)-radius, F(k, n)+radius)),
        'known_range': (F(1, 8), F(3, 8)),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    protocol = json.loads((ROOT / PROTOCOL).read_text(encoding='utf-8'))
    assert protocol['version'] == 's046-finite-v1'
    assert not git('status', '--porcelain').strip(), 'Freeze requires a clean worktree'
    head = git('rev-parse', 'HEAD').decode().strip()
    assert git('ls-remote', 'origin', 'refs/heads/main').decode().split()[0] == head
    out = (ROOT / args.output).resolve()
    assert out.is_relative_to((ROOT / 'evidence/volumerate').resolve())
    out.mkdir(parents=True, exist_ok=False)
    started = time.perf_counter()
    tracemalloc.start()
    counters = Counter()

    def require(condition, label):
        if not condition:
            raise AssertionError(label)
        counters[label] += 1

    def resources():
        elapsed = time.perf_counter()-started
        _, peak = tracemalloc.get_traced_memory()
        assert elapsed <= protocol['resource_ceiling']['elapsed_seconds'], 'runtime ceiling'
        assert peak <= protocol['resource_ceiling']['peak_python_traced_bytes'], 'traced memory ceiling'
        return elapsed, peak

    try:
        names = git('ls-tree', '-r', '--name-only', 'HEAD').decode().splitlines()
        preservation = {name: digest((ROOT / name).read_bytes()) for name in names}
        source_names = [PROTOCOL, 'checks/validate_volume_rate_finite.py', 'tools/marked_volume.py',
                        'notes/physical-volume-joint-certification.md']
        source_names += ['QuantyraNullCone/' + stem + '.lean' for stem in (
            'VolumeRateBounds', 'VolumeRateUpper', 'VolumeRateExperiment',
            'VolumeRateLikelihood', 'VolumeRateScale', 'VolumeRateSampling',
            'VolumeRateJoint', 'VolumeRateEmpty')]
        source_hashes = {}
        for name in source_names:
            committed = git('show', 'HEAD:'+name)
            require(committed == (ROOT / name).read_bytes().replace(b'\r\n', b'\n'),
                    'committed source identity')
            source_hashes[name] = digest(committed)
        save(out, 'freeze.json', {
            'created_utc': datetime.now(timezone.utc).isoformat(), 'commit': head,
            'remote_head_matches': True, 'python': platform.python_version(),
            'protocol_version': protocol['version'], 'committed_source_sha256': source_hashes,
            'preserved_worktree_sha256': preservation, 'new_samples': 0,
        })
        resources()

        epsilons = sorted({F(e) for e in protocol['fixed_epsilons']} |
                          {F(1, 2*q) for q in protocol['formula_sqrt_sizes']})
        moments = []
        for e in epsilons:
            p = density(e)
            mass, target, second = integral(p), integral(p, F(1, 2), F(1, 2)), integral(product(p, p))
            require(mass == 1, 'polynomial normalization')
            require(target == F(1, 4)+e/16, 'quarter-square target')
            require(second == 1+e*e/9, 'polynomial second moment')
            for axis in (0, 1):
                marginal = {}
                for key, c in p.items():
                    i, j = key[axis], key[1-axis]
                    marginal[i] = marginal.get(i, F(0)) + c/(j+1)
                require({i: c for i, c in marginal.items() if c} == {0: F(1)},
                        'uniform marginal polynomial')
            moments.append({'epsilon': str(e), 'mass': str(mass), 'target': str(target),
                            'second_moment': str(second)})
        all_ratios = sorted(set().union(*(set(ratios(protocol, q))
                                         for q in protocol['formula_sqrt_sizes'])))
        formula_rows = []
        branches = Counter()
        for q in protocol['formula_sqrt_sizes']:
            n, a, e = q*q, F(1, q), F(1, 2*q)
            second = integral(product(density(e), density(e)))
            divergence = second**n-1
            require(divergence == (1+e*e/9)**n-1, 'product divergence identity')
            require(divergence <= F(1, 35), 'finite divergence bound')
            require((1+F(1, 36*n))**n <= F(36, 35), 'finite Bernoulli power bound')
            require(n*(2*a)**2 == 4, 'sampling upper budget')
            for r in ratios(protocol, q):
                b = (r-1)/(r+1)
                s = min(F(1), a+b)
                branch = 'sampling' if b <= a else 'detector'
                gap = e/16 if branch == 'sampling' else b/16
                require(2*s/256 < gap, 'joint strict scalar separation')
                require((1-b)/(1+b) == 1/r, 'compensating detector ratio')
                branches[branch] += 1
                branches['crossover_equality'] += b == a
                formula_rows.append({'n': n, 'R': str(r), 'a': str(a), 'b': str(b),
                                     's': str(s), 'branch': branch, 'gap': str(gap),
                                     'lower_radius': str(s/256), 'upper_radius': str(2*s),
                                     'divergence_numerator_bits': divergence.numerator.bit_length(),
                                     'divergence_denominator_bits': divergence.denominator.bit_length()})
            resources()
        coords = [F(x) for x in protocol['detector_coordinates']]
        for r in all_ratios:
            b = (r-1)/(r+1)
            for u in coords:
                for v in coords:
                    rho = evaluate(density(b), u, v)
                    pi = (1-b)/max(1-b, min(1+b, rho))
                    require(1/r <= pi <= 1, 'global detector grid bounds')
                    if 0 <= u <= 1 and 0 <= v <= 1:
                        require(rho*pi == 1-b, 'detector compensation on support')
            for j in range(17):
                theta = F(j, 16)
                low, high = theta/(r-(r-1)*theta), r*theta/(1+(r-1)*theta)
                require(0 <= low <= theta <= high <= 1, 'retention endpoint range')
                require(theta-low <= b and high-theta <= b, 'retention bias bound')
        require(abs(F(1, 4)-F(1, 8)) <= F(1, 8) and
                abs(F(1, 4)-F(3, 8)) <= F(1, 8), 'zero-sample endpoint error')
        require(2*F(1, 128) < F(1, 2)/16, 'zero-sample strict gap')
        save(out, 'formulas.json', {'moments': moments, 'rate_cells': formula_rows,
                                    'branches': dict(branches), 'ratios': list(map(str, all_ratios))})
        print('PASS independent polynomial, detector and rate formulas', flush=True)

        wrong_target = F(1, 4)+F(1, 2)/15
        wrong_second = 1+F(1, 2)**2/8
        require(integral(density(F(1, 2)), F(1, 2), F(1, 2)) != wrong_target,
                'reject incorrect target denominator')
        require(integral(product(density(F(1, 2)), density(F(1, 2)))) != wrong_second,
                'reject incorrect moment denominator')
        gap = F(1, 32)
        require(not 2*(gap/2) < gap, 'reject strict-gap boundary')
        unclamped = F(1, 2)/evaluate(density(F(1, 2)), F(-1), F(2))
        require(not F(1, 3) <= unclamped <= 1, 'reject ambient unclamped detector')
        require(not verify_interval(4, 16, Interval(F(1, 4), F(1, 4))),
                'reject shrunken binomial interval')

        table_rows, coverage_rows = [], []
        width_pairs = Counter()
        sizes = [(0, None)] + [(q*q, q) for q in protocol['report_sqrt_sizes']]
        for n, q in sizes:
            counts = list(range(n+1)) if n <= protocol['exact_coverage_max_n'] else sorted(
                {0, 1, n//4, n//2, 3*n//4, n-1, n})
            base = {}
            for k in counts:
                cp = exact_interval(k, n, F(protocol['delta']), protocol['integer_endpoint_denominator'])
                require(verify_interval(k, n, cp, F(protocol['delta'])), 'exact endpoint certificate')
                require(not cp.fallback, 'no binomial fallback')
                base[k] = cp, analytic_interval(k, n)
            for r in ratios(protocol, q):
                cells = {}
                for k in counts:
                    cells[k] = reports(n, q, k, r, *base[k])
                    require(set(cells[k]) == set(protocol['methods']), 'declared comparator set')
                    wc = width(cells[k]['transformed_exact_binomial'])
                    wj = width(cells[k]['joint_rate'])
                    width_pairs['joint_narrower' if wj < wc else 'joint_wider' if wj > wc else 'equal'] += 1
                    table_rows.append({'n': n, 'k': k, 'R': str(r),
                        'raw_binomial': [str(base[k][0].lower), str(base[k][0].upper)],
                        'adjustments': base[k][0].adjustments,
                        'methods': {m: {'lower': str(pair[0]), 'upper': str(pair[1]),
                                       'empty': pair[0] > pair[1], 'width': str(width(pair))}
                                    for m, pair in cells[k].items()}})
                if n > protocol['exact_coverage_max_n']:
                    continue
                for e in map(F, protocol['fixed_epsilons']):
                    physical = integral(density(e), F(1, 2), F(1, 2))
                    for pattern in protocol['retention_patterns']:
                        inside, outside = {'uniform': (F(1), F(1)),
                            'lower_in_interval': (1/r, F(1)), 'higher_in_interval': (F(1), 1/r)}[pattern]
                        theta = physical*inside/(physical*inside+(1-physical)*outside)
                        require(theta == detected_probability(physical, r, pattern), 'actual retained scalar law')
                        weights = [F(comb(n, k))*theta**k*(1-theta)**(n-k) for k in counts]
                        require(sum(weights) == 1, 'complete binomial mass')
                        for method in protocol['methods']:
                            pairs = [cells[k][method] for k in counts]
                            coverage = sum((w for w, (lo, hi) in zip(weights, pairs)
                                            if lo <= physical <= hi), F(0))
                            require(coverage >= F(19, 20), 'exact finite-law coverage')
                            ew = sum((w*width(pair) for w, pair in zip(weights, pairs)), F(0))
                            empty = sum((w for w, (lo, hi) in zip(weights, pairs) if lo > hi), F(0))
                            coverage_rows.append({'n': n, 'R': str(r), 'epsilon': str(e),
                                'physical': str(physical), 'pattern': pattern, 'theta': str(theta),
                                'method': method, 'coverage': str(coverage),
                                'expected_width': enclosure(ew), 'empty_probability': str(empty)})
                resources()
            save(out, 'intervals.json', table_rows)
            save(out, 'coverage.json', coverage_rows)
            resources()
            print('PASS report grid and applicable complete laws n='+str(n), flush=True)

        require(all(digest((ROOT / name).read_bytes()) == h for name, h in preservation.items()),
                'all pre-existing tracked files preserved')
        require(not git('diff', 'HEAD', '--name-only').strip(), 'clean tracked worktree after execution')
        import scipy
        summary = {
            'status': 'PASS', 'protocol_version': protocol['version'], 'frozen_commit': head,
            'scipy': scipy.__version__, 'checks': dict(counters), 'rate_cells': len(formula_rows),
            'interval_cells': len(table_rows), 'coverage_cells': len(coverage_rows),
            'minimum_exact_coverage': str(min(F(row['coverage']) for row in coverage_rows)),
            'paired_width_counts': dict(width_pairs),
            'joint_uniformly_no_wider_on_tested_grid': width_pairs['joint_wider'] == 0 and width_pairs['joint_narrower'] > 0,
            'new_samples': 0, 'new_lean_invocations': 0, 'preserved_tracked_files': len(preservation),
            'remaining': ['direct primary-proof comparison and comparator applicability audit',
                          'any comparison amendment required by that audit', 'manuscript disposition'],
        }
        save(out, 'summary.json', summary)
        elapsed, peak = resources()
        summary.update(elapsed_seconds=elapsed, peak_python_traced_bytes=peak, resource_gate_pass=True)
        save(out, 'summary.json', summary)
        print(json.dumps(summary, indent=2), flush=True)
    except BaseException as exc:
        save(out, 'failure.json', {'status': 'FAIL', 'error': repr(exc), 'traceback': traceback.format_exc(),
                                   'checks_before_failure': dict(counters), 'elapsed_seconds': time.perf_counter()-started})
        raise
    finally:
        tracemalloc.stop()


if __name__ == '__main__':
    main()
