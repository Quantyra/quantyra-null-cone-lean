"""Frozen independent count/resource/custody audit and numerical summary."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
import math
import statistics
import time
import numpy as np
from scipy.stats import beta
from geometric_pair import (GRID, L, MIDPOINT, BASE_RADIUS, pair_probability,
    validate_points, verify_report, reference_relation_count, exact_log_certificate)
from run_geometric_pair_study import dump, sha, sample, plan
from finite_data_resource import supervise


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def time_sorted_count(points):
    """Independent future-row implementation, without the tiled counter."""
    a = points[np.argsort(points[:, 0], kind='stable')]
    total = 0
    for i in range(len(a)-1):
        future = a[i+1:]
        dt = future[:, 0]-a[i, 0]
        dx = future[:, 1]-a[i, 1]
        dy = future[:, 2]-a[i, 2]
        total += int(np.count_nonzero(dx*dx+dy*dy < dt*dt))
    return total


def interval(successes, trials):
    return [0. if successes == 0 else float(beta.ppf(.025, successes, trials-successes+1)),
            1. if successes == trials else float(beta.ppf(.975, successes+1, trials-successes))]


def audit(dest):
    dest = Path(dest)
    started = time.perf_counter()
    freeze = json.loads((dest/'freeze.json').read_text())
    for item in freeze['sources']:
        snapshot = dest/'source'/item['path']
        require(sha(snapshot) == item['git_sha256'], 'frozen source hash mismatch')
        require((ROOT/item['path']).read_bytes().replace(b'\r\n', b'\n') ==
                snapshot.read_bytes().replace(b'\r\n', b'\n'), 'source changed since freeze')
    p = json.loads((dest/'source/notes/geometric-pair-numerical-protocol.json').read_text())
    groups = json.loads((dest/'plan.json').read_text())
    require(groups == plan(p), 'planned case mismatch')
    require(exact_log_certificate(), 'log(40) rational certificate failed')
    execution = json.loads((dest/'execution.json').read_text())
    resource_rows = []
    for group in groups[:execution['groups_attempted']]:
        resource = json.loads((dest/'workers'/f'{group["id"]:02d}.json').read_text())
        require(resource['group_id'] == group['id'], 'resource group mismatch')
        require(resource['active_process_limit'] == 1, 'process limit mismatch')
        if resource['outcome'] == 'completed':
            require(resource['exit_code'] == 0, 'resource exit mismatch')
            require(resource['process_tree_peak_rss_bytes'] <= p['resource']['rss_bytes'],
                    'RSS exceeded')
            require(resource['peak_job_committed_bytes'] <= p['resource']['commit_bytes'],
                    'job commit exceeded')
            # Supervision returns after process exit/cleanup; allow that overhead.
            require(resource['wall_seconds'] <= resource['wall_limit_seconds']+10,
                    'unbounded supervisor overhead')
        resource_rows.append(resource)
    strata = defaultdict(list)
    all_records, missing, completed_ids = [], [], set()
    for group in groups:
        for case in group['cases']:
            case_dir = dest/'cases'/case['id']
            result_path = case_dir/'result.json'
            if not result_path.exists():
                missing.append(case['id']); continue
            result = json.loads(result_path.read_text())
            require(result['input'] == case, 'result input mismatch')
            require(json.loads((case_dir/'input.json').read_text()) == case, 'input file mismatch')
            require(sha(case_dir/'coordinates.npz') == result['coordinate_sha256'],
                    'coordinate hash mismatch')
            with np.load(case_dir/'coordinates.npz', allow_pickle=False) as archive:
                require(archive.files == ['points'], 'unexpected array payload')
                points = archive['points']
            validate_points(points)
            require(len(points) == case['n'], 'sample size mismatch')
            replay, sampling = sample(case, p)
            require(np.array_equal(points, replay), 'seed replay mismatch')
            require(sampling == result['sampling'], 'sampling metadata mismatch')
            del replay
            independent_r = time_sorted_count(points)
            report = result['report']
            require(report['n'] == case['n'] and report['relations'] == independent_r,
                    'independent complete count mismatch')
            require(verify_report(report), 'rational report inequality failed')
            oracle = points if case['n'] == 128 else points[:64]
            require(reference_relation_count(oracle) == result['scalar_oracle_count'],
                    'scalar oracle mismatch')
            require(len(oracle) == result['scalar_oracle_n'], 'scalar oracle size mismatch')
            truth = F(case['theta'])
            for name, value, radius in [('midpoint', MIDPOINT, BASE_RADIUS),
                    ('raw', F(report['raw']['theta']), F(report['raw']['radius'])),
                    ('policy', F(report['theta']), F(report['radius']))]:
                error = abs(value-truth)
                expected = {'absolute_parameter_error': str(error),
                    'geometric_upper': str(L*error), 'radius': str(radius),
                    'upper_within_radius': L*error <= radius}
                require(result['errors'][name] == expected, 'evaluation metric mismatch')
            require(result['continuous_mean_t2'] == str(F(1, 10)+F(13, 700)*truth),
                    'theoretical moment mismatch')
            require(result['sample_mean_t2'] == float(np.mean((points[:, 0]/GRID)**2)),
                    'sample moment mismatch')
            require(result['coordinate_bytes'] == (case_dir/'coordinates.npz').stat().st_size,
                    'coordinate byte mismatch')
            require(result['unordered_pairs_examined'] == case['n']*(case['n']-1)//2,
                    'pair count work metric mismatch')
            require(result['dense_directed_bitmatrix_bytes'] == (case['n']**2+7)//8,
                    'hypothetical storage metric mismatch')
            require(all(math.isfinite(x) and x >= 0 for x in result['seconds'].values()),
                    'invalid timing')
            completed_ids.add(case['id'])
            strata[(case['phase'], case['n'], case['theta'])].append(result)
            all_records.append(result)
        print('audit group', group['id'], 'complete', flush=True)
    actual_ids = {f.parent.name for f in (dest/'cases').glob('*/result.json')}
    require(actual_ids == completed_ids, 'unplanned completed cases')
    if execution['outcome'] == 'completed':
        require(not missing and execution['groups_completed'] == len(groups),
                'execution marked complete with missing cases')
    summaries = []
    for (phase, n, theta), rows in strata.items():
        methods = {}
        for method in ('midpoint', 'raw', 'policy'):
            errors = [float(F(r['errors'][method]['absolute_parameter_error'])) for r in rows]
            upper = [float(F(r['errors'][method]['geometric_upper'])) for r in rows]
            successes = sum(r['errors'][method]['upper_within_radius'] for r in rows)
            radii = [float(F(r['errors'][method]['radius'])) for r in rows]
            methods[method] = {'parameter_mae': statistics.mean(errors),
                'parameter_rmse': math.sqrt(statistics.mean(e*e for e in errors)),
                'mean_geometric_upper': statistics.mean(upper),
                'upper_within_radius': successes, 'replicates': len(rows),
                'event_frequency': successes/len(rows),
                'event_binomial_95_interval': interval(successes, len(rows)),
                'radius_min': min(radii), 'radius_max': max(radii)}
        us = [float(F(r['report']['raw']['u'])) for r in rows]
        summaries.append({'phase': phase, 'n': n, 'theta': theta, 'methods': methods,
            'fallback_count': sum(r['report']['branch'] == 'midpoint' for r in rows),
            'mean_u': statistics.mean(us), 'continuous_p': float(pair_probability(F(theta))),
            'replicate_mean_u_standard_error': statistics.stdev(us)/math.sqrt(len(us))
                if len(us) > 1 else None,
            'mean_t2': statistics.mean(r['sample_mean_t2'] for r in rows),
            'continuous_mean_t2': float(F(rows[0]['continuous_mean_t2'])),
            'mean_seconds': {k: statistics.mean(r['seconds'][k] for r in rows)
                for k in rows[0]['seconds']}})
    withheld = [s for s in summaries if s['phase'] == 'withheld']
    point_gate = len(withheld) == len(p['withheld_thetas'])*len(p['withheld_n']) and all(
        s['methods']['raw']['replicates'] == p['replicates'] and
        s['methods']['raw']['parameter_mae'] <= .9*s['methods']['midpoint']['parameter_mae']
        for s in withheld)
    costs = [r for r in all_records if r['input']['phase'] == 'cost'
             and r['input']['n'] == 74606]
    cost_gate = (len(costs) == 3 and execution['outcome'] == 'completed' and
                all(F(r['report']['radius']) <= F(1, 40) for r in costs))
    # Inventory all raw inputs/outcomes, excluding audit outputs and the live audit log.
    files = []
    for path in sorted(dest.rglob('*')):
        if path.is_file() and 'audit' not in path.relative_to(dest).parts:
            files.append({'path': path.relative_to(dest).as_posix(),
                          'bytes': path.stat().st_size, 'sha256': sha(path)})
    total_bytes = sum(f['bytes'] for f in files)
    require(total_bytes <= p['resource']['artifact_bytes'], 'artifact limit exceeded')
    summary = {'protocol': p['id'], 'freeze_commit': freeze['head'],
        'audit_passed_for_retained_results': True, 'execution_outcome': execution['outcome'],
        'complete_study': not missing and execution['outcome'] == 'completed',
        'completed_cases': len(all_records), 'missing_cases': missing,
        'point_diagnostic_gate_passed': point_gate, 'bounded_cost_gate_passed': cost_gate,
        'strata': summaries, 'resource': {'execution_wall_seconds': execution['wall_seconds'],
            'audit_compute_seconds': time.perf_counter()-started,
            'max_worker_wall_seconds': max(r['wall_seconds'] for r in resource_rows),
            'max_worker_peak_rss_bytes': max(r['process_tree_peak_rss_bytes'] for r in resource_rows),
            'max_worker_job_commit_bytes': max(r['peak_job_committed_bytes'] for r in resource_rows),
            'raw_artifact_bytes': total_bytes, 'raw_artifact_files': len(files),
            'grid_rejections': sum(r['sampling']['grid_rejected'] for r in all_records)},
        'limitations': ['finite-grid sampling approximates the continuous theorem law',
            'geometric upper bounds are not computed exact geometric distances',
            'small repeated strata have broad coverage uncertainty',
            'single cost cases establish cost and certificate output, not empirical coverage',
            'no physical data, observation-cost model or higher-dimensional theorem'],
        'inventory': files}
    dump(dest/'audit/summary.json', summary)


def supervised_audit(destination):
    dest = Path(destination).resolve()
    (dest/'audit').mkdir(exist_ok=False)
    p = json.loads((dest/'source/notes/geometric-pair-numerical-protocol.json').read_text())
    limits = p['resource']
    result = supervise('import runpy; runpy.run_path(sys.argv[1],run_name="__main__")',
        [__file__, 'worker', str(dest)], dest/'audit/audit.log',
        seconds=limits['audit_seconds'], rss_limit=limits['rss_bytes'],
        commit_limit=limits['commit_bytes'], poll_seconds=limits['poll_seconds'])
    dump(dest/'audit/resource.json', result)
    print(json.dumps(result), flush=True)
    return 0 if result['outcome'] == 'completed' else 1


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ('run', 'worker'):
        raise SystemExit('usage: audit_geometric_pair_study.py run|worker DESTINATION')
    if sys.argv[1] == 'worker':
        audit(sys.argv[2])
    else:
        sys.exit(supervised_audit(sys.argv[2]))
