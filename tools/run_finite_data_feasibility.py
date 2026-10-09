"""Frozen S031 pilot runner, compressed shared certificates, retained failures.

Numerical packages live in the external environment, supplied with --deps.
The worker estimates from order.json.gz only. Truth parameters are passed to
the diagnostic function after estimation; latent coordinates are never passed.
"""
import argparse
import gc
import gzip
import hashlib
import json
import platform
from fractions import Fraction as F
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = ROOT/'notes/finite-data-feasibility-protocol.json'
SOURCE_FILES = ['tools/finite_data.py', 'tools/finite_data_core.py', 'tools/finite_data_lp.py',
                'tools/benchmark_finite_data.py', 'tools/finite_data_local_mass.py',
                'tools/test_finite_data_local_mass.py', 'tools/finite_data_resource.py',
                'tools/run_finite_data_feasibility.py',
                'notes/finite-data-local-mass-feasibility.md',
                'notes/finite-data-feasibility-comparison.md',
                'notes/finite-data-information-limit.md']
SOURCE_FILES.append('notes/finite-data-feasibility-prerequisites.md')


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as src:
        for part in iter(lambda: src.read(1024**2), b''):
            h.update(part)
    return h.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2, default=str)+'\n', encoding='utf-8', newline='\n')


def artifact(path, value, limit=512*1024**2):
    """Canonical compact JSON, deterministic gzip, bounded uncompressed bytes."""
    path = Path(path)
    existing = path.exists()
    h, count = hashlib.sha256(), 0
    target = None
    raw = None
    if not existing:
        raw = path.open('xb')
        target = gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0, compresslevel=6)
    try:
        for part in json.JSONEncoder(default=str, separators=(',', ':')).iterencode(value):
            part = part.encode('utf-8')
            count += len(part)
            if count > limit:
                raise ValueError('artifact exceeds supported uncompressed size')
            h.update(part)
            if target:
                target.write(part)
    finally:
        if target:
            target.close()
            raw.close()
    if existing:
        _, old_hash, _ = read_artifact(path, limit)
        if old_hash != h.hexdigest():
            raise ValueError('shared artifact differs; refusing overwrite')
    return {'path': path.name, 'sha256_json': h.hexdigest(), 'uncompressed_bytes': count,
            'sha256_gzip': sha(path), 'compressed_bytes': path.stat().st_size}


def read_artifact(path, limit=512*1024**2):
    with gzip.open(path, 'rb') as src:
        payload = src.read(limit+1)
    if len(payload) > limit:
        raise ValueError('oversize compressed JSON')
    return json.loads(payload), hashlib.sha256(payload).hexdigest(), len(payload)


def save_report(case, method, report, order_receipt):
    report.pop('input')
    if method == 'split-dkw':
        rank = report['confidence'].pop('rank_certificate')
    else:
        rank = report.pop('rank_certificate')
    rank_receipt = artifact(case/'rank.json.gz', rank)
    envelope = {'format': 'feasibility-shared-v1', 'method': method, 'order': order_receipt,
                'rank': rank_receipt, 'report': report}
    return artifact(case/(method+'.json.gz'), envelope)


def load_report(path):
    envelope, _, _ = read_artifact(path)
    if envelope['format'] != 'feasibility-shared-v1':
        raise ValueError('bad envelope')
    report = envelope['report']
    for kind in ('order', 'rank'):
        receipt = envelope[kind]
        name = receipt['path']
        if Path(name).name != name:
            raise ValueError('nonlocal artifact reference')
        p = Path(path).parent/name
        obj, digest, size = read_artifact(p, 64*1024**2 if kind == 'order' else 512*1024**2)
        if (digest != receipt['sha256_json'] or size != receipt['uncompressed_bytes'] or
                sha(p) != receipt['sha256_gzip']):
            raise ValueError('shared artifact hash mismatch')
        if kind == 'order':
            report['input'] = obj
        elif envelope['method'] == 'split-dkw':
            report['confidence']['rank_certificate'] = obj
        else:
            report['rank_certificate'] = obj
    return report, envelope


def diagnostics(report, method, family, coefficient):
    from benchmark_finite_data import truth_cell_ranges, transpose, cdf_errors
    k, bands = report['grid'], report['bands']
    avg, low, high = truth_cell_ranges(k, family, F(coefficient))
    cdf = cdf_errors(report, family, float(F(coefficient))) if method == 'split-dkw' else None
    errors, covered, mass_ok = [], [], []
    radius = F(bands['histogram_error_upper'])
    for swap in (False, True):
        a, l, h = ((transpose(avg, k), transpose(low, k), transpose(high, k)) if swap else (avg, low, high))
        err = max(max(abs(F(b)-x), abs(F(b)-y)) for b, x, y in zip(bands['histogram'], l, h))
        cc = all(F(x) <= y <= F(z) for x, y, z in zip(bands['cell_lower'], a, bands['cell_upper']))
        pc = all(F(x) <= y and z <= F(w) for x, y, z, w in
                 zip(bands['point_lower'], l, h, bands['point_upper']))
        mo = (all(F(x) <= y/(k*k) <= F(z) for x, y, z in
                  zip(report['mass']['lower'], a, report['mass']['upper']))
              if method != 'split-dkw' else None)
        covered.append(cc and pc and err <= radius and
                       (cdf is None or cdf[int(swap)] <= float(report['confidence']['cdf_radius'])))
        errors.append(str(err))
        mass_ok.append(mo)
    widths = [F(b)-F(a) for a, b in zip(bands['point_lower'], bands['point_upper'])]
    return {'maximum_point_band_width': str(max(widths)),
            'mean_point_band_width': str(sum(widths)/(k*k)),
            'fraction_cells_with_point_band_width_at_most_0_90': str(F(sum(w <= F(9,10) for w in widths), k*k)),
            'certified_global_error_for_the_actual_output_estimator': str(radius),
            'actual_supremum_error_in_each_global_orientation': errors,
            'all_guarantees_hold_in_one_global_orientation': any(covered),
            'coverage_each_orientation': covered, 'mass_coverage_each_orientation': mass_ok,
            'cdf_error_each_orientation': cdf, 'solver_status': bands['status'],
            'fallback_or_rejection_reason': None if bands['status'] == 'certified_outer_bounds' else bands['status'],
            'no_data_comparator': {'width': '1', 'histogram': '1', 'error_radius': '1/2'}}


def worker(case, method):
    case = Path(case)
    config = json.loads((case/'case.json').read_text(encoding='utf-8'))
    if method == 'prepare':
        from benchmark_finite_data import sample, observed_order
        start = time.perf_counter()
        points = sample(config['n'], config['seed'], config['family'], float(F(config['coefficient'])))
        sample_seconds = time.perf_counter()-start
        start = time.perf_counter()
        order = observed_order(points)
        construction = time.perf_counter()-start
        receipt = artifact(case/'order.json.gz', order, 64*1024**2)
        dump(case/'prepare.json', {'sample_seconds': sample_seconds,
              'order_construction_seconds': construction, 'order': receipt,
              'latent_points_sha256': hashlib.sha256(json.dumps(points, separators=(',', ':')).encode()).hexdigest()})
        return
    from finite_data import estimate as baseline, verify_report as verify_baseline
    from finite_data_local_mass import estimate as local, verify_report as verify_local
    order, _, _ = read_artifact(case/'order.json.gz', 64*1024**2)
    start = time.perf_counter()
    report = baseline(order, 8, calibration_method='split-dkw') if method == 'split-dkw' else local(order, 8, variant=method)
    estimate_seconds = time.perf_counter()-start
    start = time.perf_counter()
    row = diagnostics(report, method, config['family'], config['coefficient'])
    diagnostic_seconds = time.perf_counter()-start
    prep = json.loads((case/'prepare.json').read_text(encoding='utf-8'))
    start = time.perf_counter()
    receipt = save_report(case, method, report, prep['order'])
    serialization = time.perf_counter()-start
    del report, order
    gc.collect()
    start = time.perf_counter()
    reread, envelope = load_report(case/(method+'.json.gz'))
    (verify_baseline if method == 'split-dkw' else verify_local)(reread)
    verification = time.perf_counter()-start
    row.update(method=method, certificate_check_passed=True,
        estimation_seconds=estimate_seconds, estimation_includes_internal_check=True,
        verification_seconds=verification, diagnostic_seconds=diagnostic_seconds,
        serialization_seconds=serialization, order_construction_seconds=prep['order_construction_seconds'],
        input_order_sha256=prep['order']['sha256_json'], certificate=receipt,
        certificate_bytes=receipt['uncompressed_bytes']+envelope['rank']['uncompressed_bytes'],
        certificate_bytes_scope='envelope plus shared forcing certificate; input order recorded separately')
    dump(case/(method+'-metrics.json'), row)


def dependency_identity(deps):
    root = Path(deps)
    records = {}
    for name in ('numpy', 'scipy'):
        for p in sorted(root.glob(name+'-*.dist-info/RECORD')):
            records[p.parent.name] = sha(p)
    return {'python_version': sys.version, 'executable_sha256': sha(sys.executable),
            'python_dll_sha256': sha(Path(sys.executable).with_name('python313.dll')),
            'numerical_package_record_sha256': records, 'platform': platform.platform(),
            'thread_limits': {'OPENBLAS_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1', 'MKL_NUM_THREADS': '1'}}


def pilot(destination, deps):
    from finite_data_resource import supervise
    dest = Path(destination)
    dest.mkdir(parents=True, exist_ok=True)
    if (dest/'manifest.json').exists():
        raise ValueError('existing campaign; refusing sample reuse or overwrite')
    if not json.loads((dest/'resource-preflight-v2/probe.json').read_text())['passed']:
        raise ValueError('resource preflight required')
    protocol = json.loads(PROTOCOL.read_text())
    manifest = {'status': 'pilot_running', 'protocol_sha256': sha(PROTOCOL),
                'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'source_sha256': {p: sha(ROOT/p) for p in SOURCE_FILES},
                'dependencies': dependency_identity(deps), 'runs': [], 'cases': [],
                'total_run_wall_seconds': sum(v['wall_seconds'] for p in dest.glob('resource-preflight*/probe.json')
                    for v in json.loads(p.read_text()).values() if isinstance(v, dict) and 'wall_seconds' in v),
                'confirmation_samples': 0,
                'allocation': 'delta_m=delta_cell=1/40; k=8; B1/B2 separate; no output intersection',
                'confirmation_status': 'not_started_pending_pilot_decision'}
    dump(dest/'manifest.json', manifest)  # frozen before the first sample
    code = ('import runpy; sys.path[:0]=[sys.argv[1],sys.argv[2]]; '
            'sys.argv=sys.argv[3:]; runpy.run_path(sys.argv[0],run_name="__main__")')
    for n in protocol['sizes']:
        for model in protocol['models']:
            case_id = f"n{n}-m{model['index']}-t0"
            case = dest/case_id
            case.mkdir()
            cfg = dict(model, n=n, seed=protocol['pilot']['seed_base']+100000*n+1000*model['index'], trial_index=0)
            dump(case/'case.json', cfg)
            for method in ('prepare', 'bernstein', 'binomial', 'split-dkw'):
                if manifest['total_run_wall_seconds']+600 > 43200:
                    manifest['status'] = 'total_budget_stop'
                    dump(dest/'manifest.json', manifest)
                    return
                args = [ROOT/'tools', deps, Path(__file__).resolve(), 'worker', str(case), method]
                outcome = supervise(code, args, case/(method+'.log'))
                manifest['total_run_wall_seconds'] += outcome['wall_seconds']
                manifest['runs'].append(dict(outcome, case=case_id, method=method))
                dump(case/(method+'-resource.json'), outcome)
                if outcome['outcome'] != 'completed':
                    dump(case/(method+'-failure.json'), dict(outcome, fallback={
                        'histogram': '1', 'bands': ['1/2','3/2'], 'width': '1', 'error_radius': '1/2',
                        'coverage': 'deterministic_range_fallback', 'certificate_check_passed': False}))
                print(json.dumps({'case': case_id, 'method': method, **outcome}), flush=True)
                dump(dest/'manifest.json', manifest)
                if method == 'prepare' and outcome['outcome'] != 'completed':
                    break
            manifest['cases'].append(case_id)
            dump(dest/'manifest.json', manifest)
    manifest['status'] = 'pilot_complete_confirmation_gate_pending'
    dump(dest/'manifest.json', manifest)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    probe = sub.add_parser('probe')
    probe.add_argument('destination', type=Path)
    run = sub.add_parser('pilot')
    run.add_argument('destination', type=Path)
    run.add_argument('--deps', required=True)
    w = sub.add_parser('worker')
    w.add_argument('case', type=Path)
    w.add_argument('method', choices=['prepare','bernstein','binomial','split-dkw'])
    check = sub.add_parser('verify')
    check.add_argument('report', type=Path)
    args = p.parse_args()
    if args.command == 'probe':
        from finite_data_resource import probe as resource_probe
        print(json.dumps(resource_probe(args.destination)))
    elif args.command == 'pilot':
        pilot(args.destination, args.deps)
    elif args.command == 'worker':
        worker(args.case, args.method)
    else:
        report, envelope = load_report(args.report)
        if envelope['method'] == 'split-dkw':
            from finite_data import verify_report
        else:
            from finite_data_local_mass import verify_report
        verify_report(report)
        print('PASS: shared hashes, realizer, forcing, calibration, mass and LP certificate')


if __name__ == '__main__':
    main()
