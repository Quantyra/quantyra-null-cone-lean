"""Frozen S039 paired pilot, exact polynomial diagnostics, bounded workers."""
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
PROTOCOL = 'notes/degree-density-practical-protocol.json'
SOURCES = [PROTOCOL, 'notes/degree-density-practical-audit.md',
           'tools/degree_density.py', 'tools/degree_density_models.py',
           'tools/test_degree_density.py', 'tools/run_degree_density_practical.py',
           'tools/audit_degree_density_practical.py', 'tools/finite_data.py',
           'tools/finite_data_core.py', 'tools/finite_data_lp.py',
           'tools/finite_data_resource.py', 'tools/run_finite_data_feasibility.py',
           'tools/benchmark_finite_data.py', 'tools/marked_volume.py',
           'QuantyraNullCone/DegreeEstimator.lean', 'QuantyraNullCone/DegreeRateNumbers.lean']


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as out:
        json.dump(value, out, indent=2, default=str); out.write('\n')


def load(path):
    p = Path(path)
    return json.loads(gzip.decompress(p.read_bytes()) if p.suffix == '.gz' else p.read_bytes())


def power_calibration():
    n = 128
    def tail(k, p):
        return sum(F(comb(n, j))*p**j*(1-p)**(n-j) for j in range(k, n+1))
    k = next(k for k in range(n+1) if tail(k, F(1, 20)) <= F(1, 40))
    size, power = tail(k, F(1, 20)), tail(k, F(3, 20))
    assert k == 13 and power >= F(9, 10)
    return {'n': n, 'failure_rejection_threshold': k, 'nominal_coverage': '19/20',
            'per_stratum_size_budget': '1/40', 'actual_test_size': str(size),
            'power_at_coverage_17_over_20': str(power), 'confirmation_samples_generated': 0}


def reconstruct_order(saved):
    from finite_data_core import bits
    return {'n': saved['n'], 'relations': [[i, j] for i, row in enumerate(saved['rows'])
                                         for j in bits(int(row))]}


def sample(config):
    import numpy as np
    from degree_density_models import coefficients
    n = config['n']
    rng = np.random.Generator(np.random.PCG64(np.random.SeedSequence(config['seed'])))
    a, b = [[float(v) for v in x] for x in coefficients(config['family'])]
    c = float(F(config['coefficient']))
    points, consumed, drawn = [], 0, 0
    while len(points) < n:
        batch = min(1024, 8*n-consumed)
        if batch <= 0: raise RuntimeError('frozen proposal budget exhausted')
        z = rng.random((batch, 3)); drawn += batch
        def poly(coefs, t):
            value = np.zeros_like(t)
            for coef in reversed(coefs): value = value*t+coef
            return value
        rho = 1+c*poly(a, z[:, 0])*poly(b, z[:, 1])
        assert np.all((rho > 0) & (rho <= 2))
        indices = np.flatnonzero(2*z[:, 2] < rho)
        need = n-len(points)
        chosen = indices[:need]
        points.extend((float(z[i, 0]), float(z[i, 1])) for i in chosen)
        consumed += int(chosen[-1])+1 if len(chosen) == need else batch
    assert len({x for x, y in points}) == n and len({y for x, y in points}) == n, 'coordinate tie'
    return points, {'consumed_proposals': consumed, 'drawn_proposals': drawn}


def report_metrics(report, truth, k, degree=False):
    from degree_density_models import metrics
    if degree:
        return metrics([report['density']]*(k*k), [report['lower']]*(k*k),
                       [report['upper']]*(k*k), report['radius'], truth, k)
    b = report['bands']
    return metrics(b['histogram'], b['point_lower'], b['point_upper'],
                   b['histogram_error_upper'], truth, k, b['cell_lower'], b['cell_upper'])


def worker(case):
    import numpy as np
    import scipy
    from benchmark_finite_data import observed_order
    from degree_density import estimate as degree_estimate, verify as degree_verify
    from degree_density_models import metrics, truth_cells
    from finite_data import estimate as baseline_estimate, verify_report
    from finite_data_core import order_rows
    from run_finite_data_feasibility import artifact

    cfg = load(case/'config.json'); stages = {}; start = time.perf_counter()
    stamp = time.perf_counter(); points, sampling = sample(cfg)
    stages['sampling'] = time.perf_counter()-stamp
    stamp = time.perf_counter(); order = observed_order(points)
    stages['relation_construction'] = time.perf_counter()-stamp
    stamp = time.perf_counter(); candidate = degree_estimate(order)
    stages['candidate_including_validation'] = time.perf_counter()-stamp
    stamp = time.perf_counter()
    baseline = baseline_estimate(order, cfg['grid'], F(1, 20), 'split-dkw')
    stages['baseline_including_validation'] = time.perf_counter()-stamp
    stamp = time.perf_counter()
    k = cfg['grid']; truth = truth_cells(k, cfg['family'], F(cfg['coefficient']))
    outcomes = {'degree_specialization': report_metrics(candidate, truth, k, True),
                'split_dkw': report_metrics(baseline, truth, k)}
    flat = {'density': '1', 'lower': '1/2', 'upper': '3/2', 'radius': '1/2'}
    outcomes['flat_no_data'] = report_metrics(flat, truth, k, True)
    oracle_counts = [0]*(k*k)
    for u, v in points: oracle_counts[min(k-1, int(u*k))*k+min(k-1, int(v*k))] += 1
    oracle = [max(F(1, 2), min(F(3, 2), F(v*k*k, cfg['n']))) for v in oracle_counts]
    oracle_metric = metrics(oracle, [F(1, 2)]*(k*k), [F(3, 2)]*(k*k), 1, truth, k)
    assert outcomes['degree_specialization'] == outcomes['flat_no_data']
    if cfg['admitted']:
        assert outcomes['degree_specialization']['joint_density_coverage']
    else:
        assert not outcomes['degree_specialization']['joint_density_coverage']
    stages['exact_diagnostics_and_oracle'] = time.perf_counter()-stamp
    metamorphic = {'performed': False}
    if cfg['metamorphic']:
        stamp = time.perf_counter()
        n = cfg['n']; relabeled = {'n': n, 'relations': [[n-1-i, n-1-j] for i, j in order['relations']]}
        rerun = degree_estimate(relabeled)
        assert report_metrics(rerun, truth, k, True) == outcomes['degree_specialization']
        old = baseline_estimate(relabeled, k, F(1, 20), 'split-dkw')
        changed = {key: old['bands'][key] != baseline['bands'][key]
                   for key in ['histogram', 'point_lower', 'point_upper']}
        assert observed_order([(v, u) for u, v in points]) == order
        metamorphic = {'performed': True, 'candidate_density_invariant': True,
                       'axis_swap_relation_identical': True, 'baseline_output_changes': changed,
                       'baseline_relabel_metrics': report_metrics(old, truth, k)}
        artifact(case/'baseline-relabeled.json.gz', {key: value for key, value in old.items() if key != 'input'})
        artifact(case/'candidate-relabeled.json.gz', rerun)
        stages['metamorphic_reruns'] = time.perf_counter()-stamp
        del old, rerun, relabeled
    stamp = time.perf_counter()
    saved = {'n': cfg['n'], 'rows': list(map(str, order_rows(cfg['n'], order['relations'])))}
    receipts = [artifact(case/'order.json.gz', saved), artifact(case/'coordinates.json.gz', points),
                artifact(case/'candidate.json.gz', candidate)]
    baseline.pop('input')
    receipts.append(artifact(case/'baseline.json.gz', baseline))
    del baseline
    reloaded = load(case/'baseline.json.gz'); reloaded['input'] = order
    assert verify_report(reloaded) and degree_verify(order, load(case/'candidate.json.gz'))
    stages['serialization_and_reload_verification'] = time.perf_counter()-stamp
    result = {'status': 'PASS', 'config': cfg, 'sampling': sampling, 'metrics': outcomes,
              'oracle': {'counts': oracle_counts, 'histogram': oracle,
                         'quotient_sup_error': oracle_metric['quotient_sup_error'],
                         'scope': 'latent-coordinate diagnostic; no confidence claim'},
              'truth_cell_averages': truth[0], 'truth_cell_minima': truth[1], 'truth_cell_maxima': truth[2],
              'mathematical_flat_branch': True, 'candidate_resource_fallback': False,
              'baseline_status': reloaded['bands']['status'], 'metamorphic': metamorphic,
              'stage_seconds': stages, 'worker_body_seconds': time.perf_counter()-start,
              'python': sys.version, 'numpy': np.__version__, 'scipy': scipy.__version__,
              'artifacts': receipts}
    dump(case/'result.json', result)
    print(json.dumps({'status': 'PASS', 'case': case.name, 'seconds': time.perf_counter()-start,
                      'candidate_width': outcomes['degree_specialization']['maximum_width']}), flush=True)


def run(output):
    from finite_data_resource import supervise, probe
    from degree_density_models import class_audit
    from marked_volume import exact_interval, verify_interval

    started = time.perf_counter()
    output = output.resolve()
    assert output.is_relative_to((ROOT/'evidence/degree-practical').resolve())
    assert not output.exists()
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True)
    remote = subprocess.check_output(['git', 'ls-remote', 'origin', 'refs/heads/main'], cwd=ROOT, text=True).split()[0]
    assert remote == commit
    sources = {}
    for name in SOURCES:
        committed = subprocess.check_output(['git', 'show', commit+':'+name], cwd=ROOT)
        actual = (ROOT/name).read_bytes()
        assert committed.replace(b'\r\n', b'\n') == actual.replace(b'\r\n', b'\n'), name
        sources[name] = {'committed_sha256': hashlib.sha256(committed).hexdigest(),
                         'executed_sha256': hashlib.sha256(actual).hexdigest()}
    names = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().strip('\0').split('\0')
    preserved = {name: sha(ROOT/name) for name in names}
    p = load(ROOT/PROTOCOL)
    output.mkdir(parents=True)
    dump(output/'freeze.json', {'commit': commit, 'sources': sources, 'preserved': preserved,
                               'python': sys.version, 'protocol': p,
                               'line_endings': 'Both exact hashes retained; normalized byte equality required for sources.'})
    results = []
    try:
        probe(output/'resource-probe')
        dump(output/'preflight.json', {'class_audit': class_audit(), 'confirmation_power': power_calibration(),
                                      'supported_sizes_audited': 4095, 'occupancy_feasible_mesh_cases': 172767,
                                      'control_tests': 'tools/test_degree_density.py; run and retain below'})
        code = 'import runpy; sys.argv=sys.argv[1:]; runpy.run_path(sys.argv[0],run_name="__main__")'
        test_code = ('import unittest; sys.path.insert(0,sys.argv[1]); '
                     'r=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.discover(sys.argv[1],pattern="test_degree_density.py")); '
                     'sys.exit(0 if r.wasSuccessful() else 1)')
        test = supervise(test_code, [ROOT/'tools'], output/'preflight-tests.log', seconds=60,
                         rss_limit=512*1024**2, commit_limit=512*1024**2)
        dump(output/'preflight-tests.json', test); assert test['outcome'] == 'completed'
        configs = []
        for size_index, n in enumerate(p['sizes']):
            for model_index, model in enumerate(p['models']):
                for rep in range(p['pilot_replications_per_stratum']):
                    configs.append(dict(model, n=n, grid=p['grid'], admitted=True, replicate=rep,
                        seed=[p['seed'], 0, size_index, model_index, rep],
                        metamorphic=model_index == 0 and rep == 0))
        mis = p['misspecified_density_control']
        configs.append({'name': 'misspecified_density', 'family': mis['family'], 'coefficient': mis['coefficient'],
                        'n': mis['n'], 'grid': p['grid'], 'admitted': False, 'replicate': 0,
                        'seed': [p['seed'], 2, 0, 0, 0], 'metamorphic': False})
        for index, cfg in enumerate(configs):
            assert time.perf_counter()-started < p['resources']['pilot_total_seconds']
            case = output/f'case-{index:02d}'; case.mkdir(); dump(case/'config.json', cfg)
            receipt = supervise(code, [Path(__file__).resolve(), '--worker', case], case/'worker.log',
                seconds=p['resources']['worker_seconds'], rss_limit=p['resources']['worker_peak_rss_bytes'],
                commit_limit=p['resources']['worker_commit_bytes'])
            dump(case/'resource.json', receipt)
            assert receipt['outcome'] == 'completed', (case.name, receipt)
            result = load(case/'result.json'); assert result['status'] == 'PASS'
            results.append(result)
            assert sum(f.stat().st_size for f in output.rglob('*') if f.is_file()) <= p['resources']['artifact_bytes']
            print(json.dumps({'case': case.name, 'completed': len(results), 'total': len(configs),
                              'elapsed_seconds': time.perf_counter()-started,
                              'worker_seconds': receipt['wall_seconds']}), flush=True)
        summary = {'status': 'PASS', 'valid_trials': 28, 'misspecified_trials': 1,
                   'source_commit': commit, 'strata': [], 'gate_passed': True}
        for n in p['sizes']:
            for model in p['models']:
                group = [r for r in results if r['config']['admitted'] and r['config']['n'] == n and r['config']['name'] == model['name']]
                row = {'n': n, 'name': model['name'], 'trials': len(group), 'methods': {}}
                for method in p['methods']:
                    good = sum(r['metrics'][method]['joint_density_coverage'] for r in group)
                    interval = exact_interval(good, len(group), denominator=2**32)
                    assert verify_interval(good, len(group), interval)
                    row['methods'][method] = {'joint_coverage_successes': good,
                        'exact_binomial_95_interval_outward': [str(interval.lower), str(interval.upper)],
                        'quotient_sup_errors': [r['metrics'][method]['quotient_sup_error'] for r in group],
                        'maximum_widths': [r['metrics'][method]['maximum_width'] for r in group]}
                summary['strata'].append(row)
        gate_rows = [r for r in results if r['config']['n'] == 3072 and r['config']['name'] in ('fgm_negative', 'fgm_positive')]
        for r in gate_rows:
            m = r['metrics']; q = m['degree_specialization']
            gate = (F(q['maximum_width']) <= F(9, 10) and F(q['radius']) <= F(9, 20)
                    and all(F(q['quotient_sup_error'])+F(1, 20) <= F(m[b]['quotient_sup_error'])
                            for b in ['flat_no_data', 'split_dkw']))
            summary['gate_passed'] = summary['gate_passed'] and gate
        assert len(gate_rows) == 4 and not summary['gate_passed']
        assert all(sha(ROOT/name) == h for name, h in preserved.items())
        summary.update({'decision': 'park_literal_degree_candidate', 'confirmation_samples': 0,
                        'revised_candidate_selected': False,
                        'basis': 'Exact flat specialization and retained finite-bound obstruction; no parameter-only revision warranted.',
                        'elapsed_seconds': time.perf_counter()-started,
                        'artifact_bytes_before_summary': sum(f.stat().st_size for f in output.rglob('*') if f.is_file()),
                        'new_lean_invocations': 0, 'preexisting_files_preserved': len(preserved)})
        assert summary['elapsed_seconds'] <= p['resources']['pilot_total_seconds']
        dump(output/'summary.json', summary)
        print(json.dumps({key: value for key, value in summary.items() if key != 'strata'}), flush=True)
    except BaseException as exc:
        dump(output/'failure.json', {'type': type(exc).__name__, 'error': str(exc),
                                    'completed_cases': len(results), 'elapsed_seconds': time.perf_counter()-started})
        raise


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path); ap.add_argument('--worker', type=Path)
    args = ap.parse_args()
    if args.worker: worker(args.worker.resolve())
    elif args.output: run(args.output)
    else: ap.error('provide --output or --worker')


if __name__ == '__main__': main()
