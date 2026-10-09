"""Audit all frozen pilot outputs, without generating or selecting new samples.

Produces exact feasible LP witnesses where available. These certify a
limitation of the retained relaxation, not of the statistical experiment.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
from run_finite_data_feasibility import ROOT, PROTOCOL, sha, dump, read_artifact
from finite_data_local_mass import local_model


def feasible(lp, point):
    return (all(F(1, 2) <= x <= F(3, 2) for x in point) and
            all(sum(F(a)*x for a, x in zip(row, point)) <= F(b)
                for row, b in zip(lp['A'], lp['b'])) and
            all(sum(F(a)*x for a, x in zip(row, point)) == F(b)
                for row, b in zip(lp['E'], lp['d'])))


def witnesses(report):
    k = report['grid']
    lp = local_model(k, report['mass'])
    g = [1-F(2*i, k-1) for i in range(k)]
    points = [[1+sign*F(1, 4)*g[i]*g[j] for i in range(k) for j in range(k)]
              for sign in (-1, 1)]
    valid = [feasible(lp, p) for p in points]
    boxed = sum(F(a) <= F(1, 2*k*k) and F(b) >= F(3, 2*k*k)
                for a, b in zip(report['mass']['lower'], report['mass']['upper']))
    return {'witnesses': [[str(x) for x in p] for p in points], 'exact_feasible': valid,
            'corner_average_values': [str(p[0]) for p in points],
            'full_width_forced_by_relaxation_and_expansion_at_corner': all(valid),
            'mass_intervals_containing_entire_prior_cell_range': boxed,
            'interpretation': 'Two feasible average vectors at corner 3/4 and 5/4 force '
                              'point-band width 1 under the fixed 1/4 expansion; '
                              'vectors are relaxation witnesses, not asserted smooth K densities.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('campaign', type=Path)
    args = parser.parse_args()
    dest = args.campaign
    run_manifest = dest/'pilot-run-manifest.json'
    if not run_manifest.exists():
        run_manifest = dest/'manifest.json'
    manifest = json.loads(run_manifest.read_text())
    if manifest['status'] != 'pilot_complete_confirmation_gate_pending':
        raise ValueError('pilot must reach its terminal gate before audit')
    protocol = json.loads(PROTOCOL.read_text())
    assert manifest['protocol_sha256'] == sha(PROTOCOL)
    assert all(sha(ROOT/p) == value for p, value in manifest['source_sha256'].items())
    assert manifest['confirmation_samples'] == 0
    runs = {(r['case'],r['method']): r for r in manifest['runs']}
    assert len(runs) == len(manifest['runs'])
    assert len(runs) <= 40
    for run in runs.values():
        if run['outcome'] == 'completed':
            assert run['exit_code'] == 0
            assert run['process_tree_peak_rss_bytes'] <= 4*1024**3
            assert run['wall_seconds'] < 600
        assert run['active_process_limit'] == 1
    preflight_seconds = sum(v['wall_seconds']
        for p in dest.glob('resource-preflight*/probe.json')
        for v in json.loads(p.read_text()).values()
        if isinstance(v, dict) and 'wall_seconds' in v)
    assert abs(manifest['total_run_wall_seconds'] - preflight_seconds -
               sum(r['wall_seconds'] for r in runs.values())) < 1e-6
    cases, rows, witness_rows = [], [], []
    for n in protocol['sizes']:
        for model in protocol['models']:
            name = f"n{n}-m{model['index']}-t0"
            cases.append(name)
            folder = dest/name
            cfg = json.loads((folder/'case.json').read_text())
            assert cfg['seed'] == protocol['pilot']['seed_base']+100000*n+1000*model['index']
            assert cfg['n'] == n and cfg['family'] == model['family'] and cfg['coefficient'] == model['coefficient']
            assert (name, 'prepare') in runs
            hashes = set()
            for method in ('bernstein','binomial','split-dkw'):
                run = runs.get((name,method))
                path = folder/(method+'-metrics.json')
                if run and run['outcome'] == 'completed':
                    row = json.loads(path.read_text())
                    assert row['method'] == method
                    assert row['certificate_check_passed']
                    assert run['process_tree_peak_rss_bytes'] <= 4*1024**3
                    assert run['wall_seconds'] < 600
                    receipt = row['certificate']
                    p = folder/receipt['path']
                    env, digest, size = read_artifact(p)
                    assert sha(p) == receipt['sha256_gzip'] and digest == receipt['sha256_json']
                    assert size == receipt['uncompressed_bytes']
                    assert p.stat().st_size == receipt['compressed_bytes']
                    for kind in ('rank','order'):
                        shared = env[kind]
                        assert sha(folder/shared['path']) == shared['sha256_gzip']
                        assert (folder/shared['path']).stat().st_size == shared['compressed_bytes']
                    assert env['order']['uncompressed_bytes'] <= 64*1024**2
                    assert size + env['rank']['uncompressed_bytes'] == row['certificate_bytes']
                    assert row['certificate_bytes'] <= 512*1024**2
                    hashes.add(row['input_order_sha256'])
                    assert row['input_order_sha256'] == env['order']['sha256_json']
                    if method != 'split-dkw':
                        witness_rows.append(dict(case=name, method=method, **witnesses(env['report'])))
                else:
                    # Retain a deterministic fallback even if preparation failed.
                    row = {'method': method, 'certificate_check_passed': False,
                           'maximum_point_band_width': '1', 'mean_point_band_width': '1',
                           'fraction_cells_with_point_band_width_at_most_0_90': '0',
                           'certified_global_error_for_the_actual_output_estimator': '1/2',
                           'actual_supremum_error_in_each_global_orientation': [model['coefficient'].lstrip('-')]*2,
                           'all_guarantees_hold_in_one_global_orientation': True,
                           'fallback_or_rejection_reason': run['outcome'] if run else 'preparation_failed',
                           'coverage_scope': 'deterministic full-range fallback'}
                row.update(case=name, n=n, family=cfg['family'], coefficient=cfg['coefficient'], seed=cfg['seed'],
                           resource=run,
                           coverage_binomial_95_interval_single_trial=['1/40','1'] if row['all_guarantees_hold_in_one_global_orientation'] else ['0','39/40'])
                rows.append(row)
            assert len(hashes) <= 1, 'unpaired inputs'
    assert manifest['cases'] == cases and len(cases) == 10
    expected_runs = {(name, method) for name in cases
                     for method in ('prepare', 'bernstein', 'binomial', 'split-dkw')}
    assert runs.keys() <= expected_runs, 'unexpected case or method'
    assert all(method != 'prepare' and runs[(name, 'prepare')]['outcome'] != 'completed'
               for name, method in expected_runs-runs.keys()), 'unexplained omitted run'
    assert manifest['total_run_wall_seconds'] < 43200
    summaries = []
    for method in ('bernstein','binomial','split-dkw'):
        for n in protocol['sizes']:
            selected = [r for r in rows if r['method'] == method and r['n'] == n]
            summaries.append({'method': method, 'n': n, 'samples': len(selected),
                'accepted_certificates': sum(r['certificate_check_passed'] for r in selected),
                'fallbacks': sum(r['fallback_or_rejection_reason'] is not None for r in selected),
                'coverage_count_including_fallback': sum(r['all_guarantees_hold_in_one_global_orientation'] for r in selected),
                'width_target_count': sum(F(r['maximum_point_band_width']) <= F(9,10) for r in selected),
                'maximum_width_each_model': [r['maximum_point_band_width'] for r in selected],
                'mean_width_each_model': [r['mean_point_band_width'] for r in selected]})
    completed = all(r['outcome'] == 'completed' for r in manifest['runs'])
    forecast = {}
    for candidate in ('bernstein','binomial'):
        used = sum(r['wall_seconds'] for r in manifest['runs'] if r['method'] in ('prepare',candidate,'split-dkw'))
        forecast[candidate] = {'paired_confirmation_seconds_linear_pilot_projection': 8*used,
                               'with_pilot_total_seconds': 8*used+manifest['total_run_wall_seconds'],
                               'valid_projection': completed,
                               'not_a_runtime_guarantee': True}
    result = {'audit_passed': True, 'source_commit': manifest['source_commit'],
              'source_and_protocol_hashes_match': True, 'pilot_sample_count': 10,
              'run_manifest_path': run_manifest.name, 'run_manifest_sha256': sha(run_manifest),
              'resource_ledger_reconciled': True, 'preflight_seconds': preflight_seconds,
              'method_outputs_including_fallback': 30, 'all_runs_completed': completed,
              'confirmation_sample_count': 0, 'summaries': summaries, 'rows': rows,
              'relaxation_witnesses': witness_rows, 'confirmation_resource_forecast': forecast,
              'coverage_interval_scope': 'Exact two-sided binomial interval for each individual '
                'model/size/method (one trial); no pooled binomial model across heterogeneous densities; '
                'diagnostic only, never proof of uniform K coverage.',
              'trial_width_count_interval': 'For zero successes in one trial the exact 95% interval is [0,39/40].',
              'pilot_ledger_seconds': manifest['total_run_wall_seconds']}
    dump(dest/'pilot-audit.json', result)
    print(json.dumps({'audit_passed': True, 'summaries': summaries, 'forecast': forecast,
                      'all_relaxation_witness_pairs_feasible': all(all(r['exact_feasible']) for r in witness_rows)}))


if __name__ == '__main__':
    main()
