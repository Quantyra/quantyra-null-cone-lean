"""Independent retained S039 geometry, polynomial, report and decision audit."""
import argparse
from fractions import Fraction as F
import gzip
import hashlib
import json
from math import comb
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))


def read(path):
    p = Path(path); b = p.read_bytes()
    return json.loads(gzip.decompress(b) if p.suffix == '.gz' else b)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(value, f, indent=2, default=str); f.write('\n')


def function(kind, t):
    if kind == 'linear': return 2*t-1
    if kind == 'quadratic': return 6*t*t-6*t+1
    if kind == 'boundary': return (1-t)**8-t**8
    x = 2*t-1
    return (35*x**4-30*x*x+3)/8


def primitive(kind, t):
    if kind == 'linear': return t*t-t
    if kind == 'quadratic': return 2*t**3-3*t*t+t
    if kind == 'boundary': return -((1-t)**9+t**9)/9
    return 14*t**5-35*t**4+30*t**3-10*t*t+t


def extrema(kind, a, b):
    vals = [function(kind, a), function(kind, b)]
    if kind == 'quadratic' and a <= F(1, 2) <= b: vals.append(F(-1, 2))
    if kind == 'legendre':
        if a <= F(1, 2) <= b: vals.append(F(3, 8))
        # Transform the cell to x in [-1,1]; check both algebraic critical points.
        for sign in [-1, 1]:
            lo, hi = sorted([sign*(2*a-1), sign*(2*b-1)])
            if hi >= 0 and max(lo, F(0))**2 <= F(3, 7) and hi**2 >= F(3, 7):
                vals.append(F(-3, 7))
    return min(vals), max(vals)


def exact_truth(config):
    pairs = {'fgm': ('linear', 'linear'), 'asymmetric': ('linear', 'quadratic'),
             'boundary8': ('boundary', 'boundary'), 'legendre4': ('legendre', 'legendre')}
    a, b = pairs[config['family']]; c = F(config['coefficient']); k = config['grid']
    avg, low, high = [], [], []
    for i in range(k):
        for j in range(k):
            u0, u1, v0, v1 = F(i, k), F(i+1, k), F(j, k), F(j+1, k)
            vals = [1+c*x*y for x in extrema(a, u0, u1) for y in extrema(b, v0, v1)]
            low.append(min(vals)); high.append(max(vals))
            avg.append(1+c*k*k*(primitive(a, u1)-primitive(a, u0))*(primitive(b, v1)-primitive(b, v0)))
    assert sum(avg) == k*k
    return avg, low, high


def metric(hist, lower, upper, radius, truth, k, cell_lo=None, cell_hi=None):
    h, lower, upper = [list(map(F, x)) for x in [hist, lower, upper]]
    row = []
    for swap in [False, True]:
        a, lo, hi = [[v[j*k+i] for i in range(k) for j in range(k)] if swap else v for v in truth]
        err = max(max(abs(v-x), abs(v-y)) for v, x, y in zip(h, lo, hi))
        covered = all(x <= y and z <= t for x, y, z, t in zip(lower, lo, hi, upper))
        cells = True if cell_lo is None else all(F(x) <= y <= F(z) for x, y, z in zip(cell_lo, a, cell_hi))
        row.append({'swap': swap, 'sup_error': str(err), 'point_band_coverage': covered,
                    'cell_average_coverage': cells, 'joint_density_coverage': covered and cells and err <= F(radius)})
    return {'orientations': row, 'quotient_sup_error': str(min(F(x['sup_error']) for x in row)),
            'joint_density_coverage': any(x['joint_density_coverage'] for x in row),
            'maximum_width': str(max(y-x for x, y in zip(lower, upper))),
            'mean_width': str(sum(y-x for x, y in zip(lower, upper))/(k*k)), 'radius': str(F(radius))}


def case_audit(case, destination):
    import numpy as np
    from finite_data_core import bits
    from finite_data import verify_report
    from degree_density import verify

    start = time.perf_counter()
    cfg = read(case/'config.json'); r = read(case/'result.json'); saved = read(case/'order.json.gz')
    assert r['status'] == 'PASS' and r['config'] == cfg
    assert read(case/'resource.json')['outcome'] == 'completed'
    n, k = cfg['n'], cfg['grid']; rows = list(map(int, saved['rows']))
    assert saved['n'] == n and len(rows) == n
    uv = np.array(read(case/'coordinates.json.gz'))
    assert uv.shape == (n, 2) and np.all((0 <= uv) & (uv < 1))
    assert len(np.unique(uv[:, 0])) == n and len(np.unique(uv[:, 1])) == n
    tt, xx = (uv[:, 0]+uv[:, 1])/2, (uv[:, 0]-uv[:, 1])/2
    chronology = tt[None, :]-tt[:, None] > abs(xx[None, :]-xx[:, None])
    packed = np.packbits(chronology, axis=1, bitorder='little')
    assert [int.from_bytes(v.tobytes(), 'little') for v in packed] == rows
    del chronology, packed
    order = {'n': n, 'relations': [[i, j] for i, row in enumerate(rows) for j in bits(row)]}
    candidate = read(case/'candidate.json.gz')
    assert verify(order, candidate)
    b = read(case/'baseline.json.gz'); b['input'] = order
    assert verify_report(b)
    truth = exact_truth(cfg)
    assert truth == tuple(list(map(F, r[name])) for name in ['truth_cell_averages', 'truth_cell_minima', 'truth_cell_maxima'])
    flat = metric([1]*(k*k), [F(1, 2)]*(k*k), [F(3, 2)]*(k*k), F(1, 2), truth, k)
    assert r['metrics']['degree_specialization'] == r['metrics']['flat_no_data'] == flat
    bands = b['bands']
    assert r['metrics']['split_dkw'] == metric(bands['histogram'], bands['point_lower'], bands['point_upper'],
        bands['histogram_error_upper'], truth, k, bands['cell_lower'], bands['cell_upper'])
    assert flat['joint_density_coverage'] == cfg['admitted']
    assert r['mathematical_flat_branch'] and not r['candidate_resource_fallback']
    assert n <= r['sampling']['consumed_proposals'] <= 8*n
    assert r['sampling']['drawn_proposals'] >= r['sampling']['consumed_proposals']
    counts = [0]*(k*k)
    for u, v in uv: counts[min(k-1, int(k*u))*k+min(k-1, int(k*v))] += 1
    assert counts == r['oracle']['counts']
    hist = [max(F(1, 2), min(F(3, 2), F(count*k*k, n))) for count in counts]
    assert hist == list(map(F, r['oracle']['histogram']))
    assert metric(hist, [F(1, 2)]*(k*k), [F(3, 2)]*(k*k), 1, truth, k)['quotient_sup_error'] == r['oracle']['quotient_sup_error']
    for receipt in r['artifacts']:
        p = case/receipt['path']; assert p.parent == case
        payload = gzip.decompress(p.read_bytes())
        assert sha(p) == receipt['sha256_gzip'] and len(payload) == receipt['uncompressed_bytes']
        assert hashlib.sha256(payload).hexdigest() == receipt['sha256_json']
    if cfg['metamorphic']:
        relabeled = {'n': n, 'relations': [[n-1-i, n-1-j] for i, j in order['relations']]}
        assert verify(relabeled, read(case/'candidate-relabeled.json.gz'))
        other = read(case/'baseline-relabeled.json.gz'); other['input'] = relabeled
        assert verify_report(other)
        bb = other['bands']
        mm = metric(bb['histogram'], bb['point_lower'], bb['point_upper'],
                    bb['histogram_error_upper'], truth, k, bb['cell_lower'], bb['cell_upper'])
        assert mm == r['metamorphic']['baseline_relabel_metrics']
        assert r['metamorphic']['baseline_output_changes'] == {key: bb[key] != bands[key] for key in ['histogram', 'point_lower', 'point_upper']}
    write(destination, {'status': 'PASS', 'case': case.name, 'exact_density_cells': k*k,
                        'full_relation_checked_from_lorentz_coordinates': True,
                        'report_certificates_checked': True, 'all_density_metrics_recomputed': True,
                        'input_sha256': {p.name: sha(p) for p in case.iterdir() if p.suffix in ['.gz', '.json']},
                        'elapsed_seconds': time.perf_counter()-start})
    print('PASS', case.name, flush=True)


def audit(output):
    from finite_data_resource import supervise
    started = time.perf_counter()
    output = output.resolve()
    assert output.is_relative_to((ROOT/'evidence/degree-practical').resolve())
    assert not (output/'artifact-audit.json').exists() and not (output/'audit').exists()
    f = read(output/'freeze.json'); s = read(output/'summary.json')
    assert s['status'] == 'PASS' and not (output/'failure.json').exists()
    p = f['protocol']
    for name, identities in f['sources'].items():
        committed = subprocess.check_output(['git', 'show', f['commit']+':'+name], cwd=ROOT)
        assert hashlib.sha256(committed).hexdigest() == identities['committed_sha256']
        assert sha(ROOT/name) == identities['executed_sha256']
    cases = sorted(output.glob('case-*')); assert len(cases) == 29
    expected = [(n, model['name'], rep, True) for n in p['sizes'] for model in p['models'] for rep in range(2)]
    expected.append((512, 'misspecified_density', 0, False))
    audit_dir = output/'audit'; audit_dir.mkdir()
    code = 'import runpy; sys.argv=sys.argv[1:]; runpy.run_path(sys.argv[0],run_name="__main__")'
    results, resources = [], []
    for case, (n, name, rep, admitted) in zip(cases, expected):
        cfg = read(case/'config.json')
        assert (cfg['n'], cfg['name'], cfg['replicate'], cfg['admitted']) == (n, name, rep, admitted)
        if admitted:
            model_index = next(i for i, model in enumerate(p['models']) if model['name'] == name)
            model = p['models'][model_index]
            assert cfg['family'] == model['family'] and cfg['coefficient'] == model['coefficient']
            assert cfg['seed'] == [p['seed'], 0, p['sizes'].index(n), model_index, rep]
            assert cfg['metamorphic'] == (model_index == 0 and rep == 0)
        else:
            assert cfg['family'] == 'fgm' and cfg['coefficient'] == '3/4'
            assert cfg['seed'] == [p['seed'], 2, 0, 0, 0] and not cfg['metamorphic']
        assert cfg['grid'] == p['grid']
        receipt = supervise(code, [Path(__file__).resolve(), '--case', case, '--receipt', audit_dir/(case.name+'.json')],
                            audit_dir/(case.name+'.log'), seconds=600, rss_limit=4*1024**3, commit_limit=4*1024**3)
        write(audit_dir/(case.name+'-resource.json'), receipt); resources.append(receipt)
        assert receipt['outcome'] == 'completed', (case.name, receipt)
        assert read(audit_dir/(case.name+'.json'))['status'] == 'PASS'
        results.append(read(case/'result.json'))
        print('audited', len(results), 'of', len(cases), flush=True)
        assert time.perf_counter()-started <= p['resources']['pilot_total_seconds']
    for row in s['strata']:
        group = [r for r in results if r['config']['admitted'] and r['config']['n'] == row['n'] and r['config']['name'] == row['name']]
        assert len(group) == row['trials'] == 2
        for method, got in row['methods'].items():
            x = sum(r['metrics'][method]['joint_density_coverage'] for r in group)
            assert got['joint_coverage_successes'] == x
            lo, hi = map(F, got['exact_binomial_95_interval_outward'])
            lower_tail = sum(F(comb(2, j))*lo**j*(1-lo)**(2-j) for j in range(x, 3))
            upper_tail = sum(F(comb(2, j))*hi**j*(1-hi)**(2-j) for j in range(x+1))
            assert (lo == 0 if x == 0 else lower_tail <= F(1, 40))
            assert (hi == 1 if x == 2 else upper_tail <= F(1, 40))
            assert got['quotient_sup_errors'] == [r['metrics'][method]['quotient_sup_error'] for r in group]
            assert got['maximum_widths'] == [r['metrics'][method]['maximum_width'] for r in group]
    assert s['gate_passed'] is False and s['confirmation_samples'] == 0 and not s['revised_candidate_selected']
    assert s['decision'] == 'park_literal_degree_candidate'
    assert all(sha(ROOT/name) == h for name, h in f['preserved'].items())
    assert sum(pth.stat().st_size for pth in output.rglob('*') if pth.is_file()) < p['resources']['artifact_bytes']
    write(output/'artifact-audit.json', {'status': 'PASS', 'trial_records': 29, 'admitted_trials': 28,
        'full_lorentz_relations_reconstructed': 29, 'exact_cell_extrema_and_integrals_checked': 1856,
        'retained_method_reports_checked': 58, 'additional_relabel_reports_checked': 4,
        'metric_rows': 87, 'preserved_files': len(f['preserved']), 'frozen_sources': len(f['sources']),
        'source_sha256': sha(Path(__file__)), 'summary_sha256': sha(output/'summary.json'),
        'elapsed_seconds': time.perf_counter()-started,
        'largest_worker_peak_rss_bytes': max(r['process_tree_peak_rss_bytes'] for r in resources),
        'decision': s['decision'], 'limits': 'Finite retained-artifact checks; no proof of floating sampler semantics or new Lean certification.'})
    print('PASS: independent S039 retained-artifact audit', flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path); ap.add_argument('--case', type=Path); ap.add_argument('--receipt', type=Path)
    args = ap.parse_args()
    if args.case: case_audit(args.case.resolve(), args.receipt.resolve())
    elif args.output: audit(args.output)
    else: ap.error('provide --output or --case and --receipt')


if __name__ == '__main__': main()
