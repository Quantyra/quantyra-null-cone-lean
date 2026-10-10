"""Audit S039's prespecified resource stop without rerunning estimation.

The original attempt remains immutable. This auditor was written after the
timeout; it does not change the scientific protocol or claim a completed grid.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import comb, isqrt
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
from audit_degree_density_practical import read, write, sha


def replay(case, destination):
    from run_degree_density_practical import sample
    from run_finite_data_feasibility import artifact
    from benchmark_finite_data import observed_order
    from finite_data_core import order_rows
    start = time.perf_counter()
    cfg = read(case/'config.json'); points, metadata = sample(cfg)
    order = observed_order(points)
    rows = order_rows(cfg['n'], order['relations'])
    a = artifact(destination/'prescribed-coordinates.json.gz', points)
    b = artifact(destination/'prescribed-order.json.gz', {'n': cfg['n'], 'rows': list(map(str, rows))})
    write(destination/'replay.json', {'status': 'PASS', 'config': cfg, 'sampling': metadata,
        'artifacts': [a, b], 'seconds': time.perf_counter()-start, 'estimator_runs': 0,
        'scope': 'Deterministic replay of the interrupted prescribed seed, not recovered original bytes or an additional trial. The interrupted worker saved no coordinate hash.'})
    print('PASS: prescribed input replay only; no estimation rerun', flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--attempt', type=Path, required=True); ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--replay-only', action='store_true')
    args = ap.parse_args(); attempt, out = args.attempt.resolve(), args.output.resolve()
    assert attempt.is_relative_to((ROOT/'evidence/degree-practical').resolve())
    assert out.is_relative_to((ROOT/'evidence/degree-practical').resolve())
    if args.replay_only:
        replay(attempt/'case-14', out); return
    from finite_data_resource import supervise
    from marked_volume import exact_interval, verify_interval
    started = time.perf_counter()
    assert not out.exists(); out.mkdir(parents=True)
    original = {str(p.relative_to(attempt)): sha(p) for p in attempt.rglob('*') if p.is_file()}
    f = read(attempt/'freeze.json'); p = f['protocol']; failure = read(attempt/'failure.json')
    assert not (attempt/'summary.json').exists()
    assert failure['type'] == 'AssertionError' and failure['completed_cases'] == 14
    cases = sorted(attempt.glob('case-*')); assert [c.name for c in cases] == [f'case-{i:02d}' for i in range(15)]
    stop = read(cases[-1]/'resource.json')
    assert stop['outcome'] == 'timeout' and stop['exit_code'] == 125
    assert stop['wall_limit_seconds'] == p['resources']['worker_seconds'] == 600
    assert stop['wall_seconds'] >= 600 and stop['process_tree_peak_rss_bytes'] < 4*1024**3
    assert not (cases[-1]/'result.json').exists()
    assert read(attempt/'preflight-tests.json')['outcome'] == 'completed'
    assert 'Ran 6 tests' in (attempt/'preflight-tests.log').read_text(encoding='utf-8')
    assert read(attempt/'resource-probe/probe.json')['passed']
    power = read(attempt/'preflight.json')['confirmation_power']
    for key, prob in [('actual_test_size', F(1, 20)), ('power_at_coverage_17_over_20', F(3, 20))]:
        assert F(power[key]) == sum(F(comb(128, j))*prob**j*(1-prob)**(128-j) for j in range(13, 129))
    assert F(power['actual_test_size']) <= F(1, 40) and F(power['power_at_coverage_17_over_20']) >= F(9, 10)
    for name, ids in f['sources'].items():
        raw = subprocess.check_output(['git', 'show', f['commit']+':'+name], cwd=ROOT)
        assert hashlib.sha256(raw).hexdigest() == ids['committed_sha256']
        assert sha(ROOT/name) == ids['executed_sha256']
    code = 'import runpy; sys.argv=sys.argv[1:]; runpy.run_path(sys.argv[0],run_name="__main__")'
    results, audits, resources = [], [], []
    for i, case in enumerate(cases):
        cfg = read(case/'config.json'); size_index = 0 if i < 14 else 1
        model_index, rep = divmod(i % 14, 2); model = p['models'][model_index]
        assert cfg['n'] == p['sizes'][size_index] and cfg['admitted']
        assert all(cfg[k] == model[k] for k in ['name', 'family', 'coefficient'])
        assert cfg['grid'] == p['grid'] and cfg['replicate'] == rep
        assert cfg['seed'] == [p['seed'], 0, size_index, model_index, rep]
        assert cfg['metamorphic'] == (model_index == 0 and rep == 0)
        resource = read(case/'resource.json'); resources.append(resource)
        if i == 14: continue
        assert resource['outcome'] == 'completed' and resource['wall_seconds'] <= 600
        assert resource['process_tree_peak_rss_bytes'] <= 4*1024**3 and resource['peak_job_committed_bytes'] <= 4*1024**3
        receipt = supervise(code, [ROOT/'tools/audit_degree_density_practical.py', '--case', case,
                            '--receipt', out/(case.name+'.json')], out/(case.name+'.log'),
                            seconds=600, rss_limit=4*1024**3, commit_limit=4*1024**3)
        write(out/(case.name+'-resource.json'), receipt); audits.append(receipt)
        assert receipt['outcome'] == 'completed', (case.name, receipt)
        assert read(out/(case.name+'.json'))['status'] == 'PASS'
        results.append(read(case/'result.json'))
        print('audited completed case', len(results), 'of 14', flush=True)
    replay_dir = out/'interrupted-input-replay'; replay_dir.mkdir()
    receipt = supervise(code, [Path(__file__).resolve(), '--attempt', attempt, '--output', replay_dir,
                               '--replay-only'], replay_dir/'replay.log', seconds=600,
                               rss_limit=4*1024**3, commit_limit=4*1024**3)
    write(replay_dir/'resource.json', receipt)
    assert receipt['outcome'] == 'completed' and read(replay_dir/'replay.json')['estimator_runs'] == 0
    strata = []
    for model in p['models']:
        group = [r for r in results if r['config']['name'] == model['name']]; assert len(group) == 2
        row = {'n': 512, 'name': model['name'], 'trials': 2, 'methods': {}}
        for method in p['methods']:
            m = [r['metrics'][method] for r in group]
            successes = sum(x['joint_density_coverage'] for x in m)
            band = exact_interval(successes, 2, denominator=2**32); assert verify_interval(successes, 2, band)
            row['methods'][method] = {'coverage_successes': successes,
                'exact_95_binomial_interval_outward': [str(band.lower), str(band.upper)],
                'maximum_widths': [x['maximum_width'] for x in m],
                'quotient_sup_errors': [x['quotient_sup_error'] for x in m]}
        strata.append(row)
    assert sum(isqrt(n) for n in range(2, 4097)) == 172767
    assert isqrt(4096//4) == 32 < 65536 and F(192, isqrt(4096)) == 3
    assert all(r['metrics']['degree_specialization']['maximum_width'] == '1' for r in results)
    assert all(sha(ROOT/name) == h for name, h in f['preserved'].items())
    assert {str(q.relative_to(attempt)): sha(q) for q in attempt.rglob('*') if q.is_file()} == original
    size = sum(q.stat().st_size for folder in [attempt, out] for q in folder.rglob('*') if q.is_file())
    assert size < p['resources']['artifact_bytes']
    result = {'status': 'PASS_SCOPED_STOPPED_STUDY_AUDIT', 'original_run_status': 'prespecified_worker_timeout',
        'original_source_commit': f['commit'], 'audit_source_sha256': sha(Path(__file__)),
        'audit_source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'original_attempt_sha256': original, 'completed_valid_trials': 14, 'interrupted_valid_trials': 1,
        'unstarted_valid_trials': 13, 'unstarted_misspecified_trials': 1, 'planned_valid_trials': 28,
        'full_lorentz_relations_audited': 14, 'exact_density_cells_audited': 896,
        'computed_reports_audited': 28, 'additional_relabel_reports_audited': 2,
        'strata': strata, 'confirmation_trials': 0, 'new_pilot_estimation_runs_in_audit': 0,
        'interrupted_input_replays': 1, 'interrupted_original_input_bytes_recovered': False,
        'successful_worker_seconds': sum(r['wall_seconds'] for r in resources[:-1]),
        'timeout_worker_seconds': stop['wall_seconds'], 'original_run_elapsed_seconds': failure['elapsed_seconds'],
        'largest_successful_worker_seconds': max(r['wall_seconds'] for r in resources[:-1]),
        'largest_successful_worker_peak_rss_bytes': max(r['process_tree_peak_rss_bytes'] for r in resources[:-1]),
        'timeout_peak_rss_bytes': stop['process_tree_peak_rss_bytes'],
        'audit_elapsed_seconds': time.perf_counter()-started,
        'audit_worker_seconds': sum(r['wall_seconds'] for r in audits),
        'replay_worker_seconds': receipt['wall_seconds'], 'artifact_bytes_before_audit_summary': size,
        'preserved_prior_files': len(f['preserved']), 'frozen_sources': len(f['sources']),
        'decision': 'park_literal_degree_candidate', 'revised_candidate_selected': False,
        'basis': 'Every possible valid candidate report in the supported range has width one and equals the flat estimator; observed smaller trials agree. The frozen larger comparison also reaches its worker resource stop.',
        'limitations': 'Not a completed 28-trial grid; no n=3072 report, missed-density sample, empirical confirmation or attribution of the interrupted worker cost to a particular stage. Source/constant audit supplies the deterministic width conclusion.'}
    write(out/'artifact-audit.json', result)
    print(json.dumps({k: v for k, v in result.items() if k not in ['strata', 'original_attempt_sha256']}), flush=True)


if __name__ == '__main__': main()
