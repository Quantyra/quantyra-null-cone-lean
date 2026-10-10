"""Audit retained S046 tables with integer tails and a distinct PMF recurrence."""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from math import isqrt
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from marked_volume import Interval, binomial_tail_numerator, verify_interval


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding='utf-8'))


def grid_ratios(protocol, n):
    result = set(map(F, protocol['base_retention_ratios']))
    if n:
        q = isqrt(n)
        assert q*q == n
        for b in (F(1, 2*q), F(1, q), min(F(2, q), F(1, 3))):
            if b <= F(1, 3):
                result.add((1+b)/(1-b))
    return result


def clip(lo, hi):
    return max(F(1, 8), lo), min(F(3, 8), hi)


def interval_width(pair):
    return max(F(0), pair[1]-pair[0])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run', required=True)
    args = parser.parse_args()
    out = (ROOT / args.run).resolve()
    assert out.is_relative_to((ROOT / 'evidence/volumerate').resolve())
    destination = out / 'artifact-audit.json'
    assert not destination.exists(), 'Preserve the existing audit'
    started = time.perf_counter()
    protocol = load(ROOT / 'notes/physical-volume-finite-protocol.json')
    freeze, summary = load(out / 'freeze.json'), load(out / 'summary.json')
    assert summary['status'] == 'PASS' and summary['resource_gate_pass']
    assert summary['frozen_commit'] == freeze['commit']
    assert summary['protocol_version'] == freeze['protocol_version'] == protocol['version']
    assert summary['new_samples'] == summary['new_lean_invocations'] == 0
    names = list(freeze['committed_source_sha256'])
    batch = subprocess.check_output(['git', 'cat-file', '--batch'], cwd=ROOT,
        input=''.join(freeze['commit']+':'+name+'\n' for name in names).encode())
    offset = 0
    for name in names:
        end = batch.index(b'\n', offset)
        header = batch[offset:end].split()
        assert len(header) == 3 and header[1] == b'blob'
        size = int(header[2])
        committed = batch[end+1:end+1+size]
        offset = end+2+size
        assert sha(committed) == freeze['committed_source_sha256'][name]
        assert committed == (ROOT / name).read_bytes().replace(b'\r\n', b'\n')
    assert offset == len(batch)
    receipt = load(ROOT / 'evidence/gcp' / protocol['formal_run'] / 'receipt.json')
    assert receipt['acceptance'] and receipt['exit'] == 0 and receipt['audited_exports'] == 797

    ns = [0]+[q*q for q in protocol['report_sqrt_sizes']]
    count_grids = {n: list(range(n+1)) if n <= protocol['exact_coverage_max_n'] else
                  sorted({0, 1, n//4, n//2, 3*n//4, n-1, n}) for n in ns}
    expected = {(n, k, r) for n in ns for k in count_grids[n] for r in grid_ratios(protocol, n)}
    intervals = load(out / 'intervals.json')
    tables, raw_binomial = {}, {}
    comparisons = Counter({'joint_narrower': 0, 'joint_wider': 0, 'equal': 0})
    for row in intervals:
        n, k, r = row['n'], row['k'], F(row['R'])
        key = n, k, r
        assert key not in tables and key in expected
        raw = tuple(map(F, row['raw_binomial']))
        if (n, k) in raw_binomial:
            assert raw_binomial[n, k] == raw
        else:
            assert verify_interval(k, n, Interval(*raw), F(protocol['delta']))
            raw_binomial[n, k] = raw
        assert set(row['methods']) == set(protocol['methods'])
        cells = {method: (F(cell['lower']), F(cell['upper'])) for method, cell in row['methods'].items()}
        for method, cell in row['methods'].items():
            assert cell['empty'] == (cells[method][0] > cells[method][1])
            assert F(cell['width']) == interval_width(cells[method])
        assert cells['known_range'] == (F(1, 8), F(3, 8))
        if n == 0:
            assert all(pair == cells['known_range'] for pair in cells.values())
        else:
            lo, hi = raw
            assert cells['transformed_exact_binomial'] == clip(lo/(r-(r-1)*lo), r*hi/(1+(r-1)*hi))
            radius = 2*min(F(1), F(1, isqrt(n))+(r-1)/(r+1))
            assert cells['joint_rate'] == clip(F(k, n)-radius, F(k, n)+radius)
            d = 2**24
            m = isqrt(2*d*d//n)
            m += m*m*n < 2*d*d
            low, high = max(F(0), F(k, n)-F(m, d)), min(F(1), F(k, n)+F(m, d))
            assert cells['transformed_hoeffding'] == clip(low/(r-(r-1)*low), r*high/(1+(r-1)*high))
        diff = interval_width(cells['joint_rate'])-interval_width(cells['transformed_exact_binomial'])
        comparisons['joint_wider' if diff > 0 else 'joint_narrower' if diff < 0 else 'equal'] += 1
        tables[key] = cells
    assert set(tables) == expected
    assert len(intervals) == summary['interval_cells']
    assert comparisons == Counter(summary['paired_width_counts'])

    expected_coverage = {(n, r, F(e), pattern, method) for n in ns
        if n <= protocol['exact_coverage_max_n'] for r in grid_ratios(protocol, n)
        for e in protocol['fixed_epsilons'] for pattern in protocol['retention_patterns']
        for method in protocol['methods']}
    coverage_rows = load(out / 'coverage.json')
    seen, pmfs = set(), {}
    min_coverage = F(1)
    for row in coverage_rows:
        n, r, e, pattern, method = row['n'], F(row['R']), F(row['epsilon']), row['pattern'], row['method']
        key = n, r, e, pattern, method
        assert key not in seen and key in expected_coverage
        seen.add(key)
        physical = F(1, 4)+e/16
        inside, outside = {'uniform': (F(1), F(1)), 'lower_in_interval': (1/r, F(1)),
                           'higher_in_interval': (F(1), 1/r)}[pattern]
        theta = physical*inside/(physical*inside+(1-physical)*outside)
        assert F(row['physical']) == physical and F(row['theta']) == theta
        assert 0 < theta < 1
        pairs = [tables[n, k, r][method] for k in range(n+1)]
        accepted = [k for k, (lo, hi) in enumerate(pairs) if lo <= physical <= hi]
        assert accepted and accepted == list(range(min(accepted), max(accepted)+1))
        left, right = min(accepted), max(accepted)
        m, d = theta.numerator, theta.denominator
        missed = (binomial_tail_numerator(n, left-1, m, d, False) if left else 0)
        missed += binomial_tail_numerator(n, right+1, m, d, True) if right < n else 0
        coverage = 1-F(missed, d**n)
        assert coverage == F(row['coverage']) and coverage >= F(19, 20)
        min_coverage = min(min_coverage, coverage)
        if (n, theta) not in pmfs:
            weights = [(1-theta)**n]
            for k in range(n):
                weights.append(weights[-1]*(n-k)*theta/((k+1)*(1-theta)))
            assert sum(weights) == 1
            pmfs[n, theta] = weights
        weights = pmfs[n, theta]
        ew = sum((w*interval_width(pair) for w, pair in zip(weights, pairs)), F(0))
        rounded = row['expected_width']
        assert F(rounded['lower']) <= ew <= F(rounded['upper'])
        assert F(rounded['upper'])-F(rounded['lower']) <= F(1, 10**12)
        empty = sum((w for w, (lo, hi) in zip(weights, pairs) if lo > hi), F(0))
        assert empty == F(row['empty_probability'])
    assert seen == expected_coverage and len(coverage_rows) == summary['coverage_cells']
    assert min_coverage == F(summary['minimum_exact_coverage'])
    assert summary['joint_uniformly_no_wider_on_tested_grid'] == (
        comparisons['joint_wider'] == 0 and comparisons['joint_narrower'] > 0)
    assert sum(count for name, count in summary['checks'].items() if name.startswith('reject ')) == 5
    import numpy, scipy
    result = {
        'status': 'PASS', 'frozen_commit': freeze['commit'], 'committed_source_identities': len(names),
        'unique_binomial_certificates': len(raw_binomial), 'interval_cells': len(tables),
        'independent_integer_tail_coverage_cells': len(seen), 'pmf_recurrences': len(pmfs),
        'minimum_exact_coverage': str(min_coverage), 'paired_width_counts': dict(comparisons),
        'all_prespecified_cells_present_once': True, 'expected_width_enclosures_verified': True,
        'numpy': numpy.__version__, 'scipy': scipy.__version__,
        'audit_source_sha256': sha(Path(__file__).read_bytes().replace(b'\r\n', b'\n')),
        'artifact_sha256': {name: sha((out / name).read_bytes()) for name in
                           ['freeze.json', 'formulas.json', 'intervals.json', 'coverage.json', 'summary.json']},
        'elapsed_seconds': time.perf_counter()-started,
        'limits': 'Checks the frozen finite grid and retained artifacts; no universal Python proof or source-literature completion.',
    }
    destination.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k not in {'artifact_sha256', 'minimum_exact_coverage'}}, indent=2))


if __name__ == '__main__':
    main()
