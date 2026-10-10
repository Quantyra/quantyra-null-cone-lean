"""Frozen S043 numerical study, Windows-supervised; no Lean invocation."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
import platform
import subprocess
import time
import numpy as np
import scipy
from geometric_pair import (GRID, L, MIDPOINT, estimate, verify_report,
    validate_points, relation_count, reference_relation_count)
from finite_data_resource import supervise

PROTOCOL = ROOT/'notes/geometric-pair-numerical-protocol.json'
SOURCES = ['notes/geometric-pair-numerical-protocol.json',
    'notes/geometric-pair-launch-amendment.json',
    'notes/geometric-pair-numerical-design.md', 'tools/geometric_pair.py',
    'tools/test_geometric_pair.py', 'tools/run_geometric_pair_study.py',
    'tools/audit_geometric_pair_study.py', 'tools/finite_data_resource.py']
WORKER_BOOTSTRAP = ('import runpy; script=sys.argv.pop(1); '
                    'runpy.run_path(script,run_name="__main__")')


def dump(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as out:
        json.dump(value, out, indent=2, allow_nan=False)
        out.write('\n')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def protocol():
    return json.loads(PROTOCOL.read_text(encoding='utf-8'))


def plan(p):
    groups = []
    for phase_id, phase in enumerate(('primary', 'withheld', 'cost')):
        for n in p[phase+'_n']:
            for value in p[phase+'_thetas']:
                theta = F(value)
                repetitions = p['cost_replicates'] if phase == 'cost' else p['replicates']
                cases = []
                for rep in range(repetitions):
                    case_id = f'{phase}-n{n}-t{theta.numerator}_{theta.denominator}-r{rep:02d}'
                    cases.append({'id': case_id, 'phase': phase, 'n': n, 'theta': value,
                        'replicate': rep, 'seed': p['seed']+[phase_id, theta.numerator,
                            theta.denominator, n, rep]})
                groups.append({'id': len(groups), 'cases': cases})
    return groups


def flat_transform(uniforms):
    """The analytic inverse-CDF/area map; inputs have shape (batch,5)."""
    t = np.where(uniforms[:, 0] < .5, -1., 1.)*(1-np.cbrt(1-uniforms[:, 1]))
    radius = (1-np.abs(t))*np.sqrt(uniforms[:, 2])
    angle = 2*np.pi*uniforms[:, 3]
    return np.column_stack((t, radius*np.cos(angle), radius*np.sin(angle)))


def sample(case, p):
    rng = np.random.Generator(np.random.PCG64(np.random.SeedSequence(case['seed'])))
    theta, n = float(F(case['theta'])), case['n']
    accepted, size, drawn, envelope_pass, grid_reject = [], 0, 0, 0, 0
    limit = 8*n+4096
    while size < n:
        batch = min(p['proposal_batch'], limit-drawn)
        if batch <= 0:
            raise RuntimeError('frozen proposal budget exhausted')
        u = rng.random((batch, 5))
        a = flat_transform(u)
        keep = u[:, 4]*(1+.9*theta) <= 1+theta*(a[:, 0]**2-.1)
        rounded = np.rint(a[keep]*GRID).astype(np.int64)
        gap = GRID-np.abs(rounded[:, 0])
        inside = (gap > 0) & (rounded[:, 1]**2+rounded[:, 2]**2 < gap**2)
        good = rounded[inside]
        accepted.append(good)
        size += len(good)
        drawn += batch
        envelope_pass += len(rounded)
        grid_reject += int(np.count_nonzero(~inside))
    points = np.concatenate(accepted)[:n]
    validate_points(points)
    return points, {'proposals_drawn': drawn, 'envelope_accepted': envelope_pass,
        'grid_rejected': grid_reject, 'retained': n, 'unused_accepted': size-n,
        'proposal_limit': limit, 'batch': p['proposal_batch']}


def errors(report, theta):
    theta = F(theta)
    answer = {}
    for name, value, radius in (('midpoint', MIDPOINT, F(3, 80)),
            ('raw', F(report['raw']['theta']), F(report['raw']['radius'])),
            ('policy', F(report['theta']), F(report['radius']))):
        error = abs(value-theta)
        answer[name] = {'absolute_parameter_error': str(error),
            'geometric_upper': str(L*error), 'radius': str(radius),
            'upper_within_radius': L*error <= radius}
    return answer


def worker(destination, group_id):
    dest, p = Path(destination), protocol()
    group = plan(p)[group_id]
    for case in group['cases']:
        case_dir = dest/'cases'/case['id']
        case_dir.mkdir()
        dump(case_dir/'input.json', case)
        start = time.perf_counter()
        points, sampling = sample(case, p)
        sampled = time.perf_counter()
        # Retain inputs before the potentially expensive complete relation count.
        np.savez_compressed(case_dir/'coordinates.npz', points=points)
        stored = time.perf_counter()
        relations = relation_count(points, p['block'])
        counted = time.perf_counter()
        oracle_points = points if case['n'] == 128 else points[:64]
        oracle = reference_relation_count(oracle_points)
        if oracle != relation_count(oracle_points, p['block']):
            raise RuntimeError('scalar chronology oracle mismatch')
        report = estimate(case['n'], relations)
        if not verify_report(report):
            raise RuntimeError('rational certificate failed')
        end = time.perf_counter()
        dump(case_dir/'result.json', {'input': case, 'sampling': sampling,
            'coordinate_sha256': sha(case_dir/'coordinates.npz'),
            'coordinate_bytes': (case_dir/'coordinates.npz').stat().st_size,
            'scalar_oracle_n': len(oracle_points), 'scalar_oracle_count': oracle,
            'report': report, 'errors': errors(report, case['theta']),
            'sample_mean_t2': float(np.mean((points[:, 0]/GRID)**2)),
            'continuous_mean_t2': str(F(1, 10)+F(13, 700)*F(case['theta'])),
            'unordered_pairs_examined': case['n']*(case['n']-1)//2,
            'dense_directed_bitmatrix_bytes': (case['n']**2+7)//8,
            'seconds': {'sampling': sampled-start, 'save': stored-sampled,
                'all_pairs': counted-stored, 'oracle_and_report': end-counted,
                'total': end-start}})
        print(case['id'], 'complete', flush=True)


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def freeze(dest):
    if git('status', '--porcelain').strip():
        raise RuntimeError('freeze requires a clean worktree')
    head = git('rev-parse', 'HEAD').decode().strip()
    remote = git('ls-remote', 'origin', 'refs/heads/main').decode().split()[0]
    if head != remote:
        raise RuntimeError('freeze requires the pushed main HEAD')
    dest.mkdir(parents=True, exist_ok=False)
    (dest/'source').mkdir()
    (dest/'cases').mkdir()
    (dest/'workers').mkdir()
    files = []
    for rel in SOURCES:
        raw, current = git('show', f'{head}:{rel}'), (ROOT/rel).read_bytes()
        if raw.replace(b'\r\n', b'\n') != current.replace(b'\r\n', b'\n'):
            raise RuntimeError(f'worktree/source mismatch: {rel}')
        snapshot = dest/'source'/rel
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        snapshot.write_bytes(raw)
        files.append({'path': rel, 'git_sha256': hashlib.sha256(raw).hexdigest(),
            'worktree_sha256': hashlib.sha256(current).hexdigest()})
    p = protocol()
    dump(dest/'freeze.json', {'utc': datetime.now(timezone.utc).isoformat(),
        'head': head, 'remote_main': remote, 'sources': files,
        'protocol_sha256': sha(PROTOCOL), 'python': sys.version,
        'python_executable_sha256': sha(sys.executable), 'numpy': np.__version__,
        'scipy': scipy.__version__, 'platform': platform.platform(),
        'machine': platform.machine(), 'processor': platform.processor(),
        'planned_groups': len(plan(p)), 'planned_cases': sum(len(g['cases']) for g in plan(p)),
        'scope': 'local Python numerical experiment; accepted Lean runs only on GCP'})
    dump(dest/'plan.json', plan(p))
    return p


def execute(dest):
    dest = Path(dest).resolve()
    p = freeze(dest)
    limits = p['resource']
    started = time.perf_counter()
    outcomes, reason = [], 'completed'
    code = WORKER_BOOTSTRAP
    for group in plan(p):
        remaining = limits['execution_seconds']-(time.perf_counter()-started)
        if remaining <= 0:
            reason = 'total_time_limit'; break
        result = supervise(code, [__file__, 'worker', str(dest), str(group['id'])],
            dest/'workers'/f'{group["id"]:02d}.log',
            seconds=min(limits['worker_seconds'], remaining), rss_limit=limits['rss_bytes'],
            commit_limit=limits['commit_bytes'], poll_seconds=limits['poll_seconds'])
        result['group_id'] = group['id']
        dump(dest/'workers'/f'{group["id"]:02d}.json', result)
        outcomes.append(result)
        size = sum(f.stat().st_size for f in dest.rglob('*') if f.is_file())
        print(json.dumps({'group': group['id'], 'outcome': result['outcome'],
            'seconds': result['wall_seconds'], 'artifact_bytes': size}), flush=True)
        if result['outcome'] != 'completed':
            reason = result['outcome']; break
        if size > limits['artifact_bytes']:
            reason = 'artifact_limit'; break
    dump(dest/'execution.json', {'outcome': reason, 'groups_completed':
        sum(r['outcome'] == 'completed' for r in outcomes), 'groups_attempted': len(outcomes),
        'wall_seconds': time.perf_counter()-started, 'resource_limits': limits,
        'finished_utc': datetime.now(timezone.utc).isoformat()})
    return 0 if reason == 'completed' else 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['run', 'worker'])
    parser.add_argument('destination')
    parser.add_argument('group', nargs='?', type=int)
    args = parser.parse_args()
    if args.mode == 'worker':
        worker(args.destination, args.group)
    else:
        sys.exit(execute(args.destination))
