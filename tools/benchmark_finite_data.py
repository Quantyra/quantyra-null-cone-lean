"""Reproducible K-copula evaluation; latent data is used only for diagnostics."""
import argparse
import json
import math
import random
import time
import tracemalloc
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from finite_data import estimate
from finite_data_core import ranks


def density(u, v, family, c):
    if family == 'asymmetric':
        return 1+c*(2*u-1)*(6*v*v-6*v+1)
    return 1+c*(2*u-1)*(2*v-1)


def population_cdf(u, v, family, c):
    g = 2*v**3-3*v*v+v if family == 'asymmetric' else v*v-v
    return u*v+c*(u*u-u)*g


def sample(n, seed, family, c):
    rng = random.Random(seed)
    points = []
    while len(points) < n:
        u, v = rng.random(), rng.random()
        if 1.5*rng.random() < density(u, v, family, c):
            points.append((u, v))
    if len({p[0] for p in points}) != n or len({p[1] for p in points}) != n:
        raise RuntimeError('finite-precision coordinate tie; retain this failure')
    return points


def observed_order(points):
    n = len(points)
    return {'n': n, 'relations': [(i, j) for i, (u, v) in enumerate(points)
                                  for j, (x, y) in enumerate(points) if u < x and v < y]}


def cdf_errors(report, family, c):
    n = report['input']['n']
    empirical = np.zeros((n+1, n+1), dtype=np.int64)
    empirical[ranks(report['first']), ranks(report['second'])] = 1
    empirical = np.cumsum(np.cumsum(empirical, axis=0), axis=1)/n
    grid = np.arange(n+1, dtype=float)/n
    u, v = grid[:, None], grid[None, :]
    errors = []
    for swap in (0, 1):
        truth = population_cdf(v, u, family, c) if swap else population_cdf(u, v, family, c)
        # All jump corners and upper one-sided limits of constant-CDF cells.
        errors.append(max(float(np.max(np.abs(empirical-truth))),
                          float(np.max(np.abs(empirical[:-1, :-1]-truth[1:, 1:]))),
                          float(np.max(np.abs(empirical[-1, :-1]-truth[-1, 1:]))),
                          float(np.max(np.abs(empirical[:-1, -1]-truth[1:, -1])))))
    return errors


def truth_cell_ranges(k, family, c):
    averages, minima, maxima = [], [], []
    for i in range(k):
        for j in range(k):
            u0, u1, v0, v1 = F(i, k), F(i+1, k), F(j, k), F(j+1, k)
            avg_f = k*((u1*u1-u1)-(u0*u0-u0))
            def integral_g(v):
                return 2*v**3-3*v*v+v if family == 'asymmetric' else v*v-v
            avg_g = k*(integral_g(v1)-integral_g(v0))
            averages.append(1+c*avg_f*avg_g)
            vs = [v0, v1]
            if family == 'asymmetric' and v0 <= F(1, 2) <= v1:
                vs.append(F(1, 2))
            values = [density(u, v, family, c) for u in [u0, u1] for v in vs]
            minima.append(min(values))
            maxima.append(max(values))
    return averages, minima, maxima


def transpose(values, k):
    return [values[j*k+i] for i in range(k) for j in range(k)]


def evaluate(n, seed, family, coefficient, k, profile_memory=False):
    points = sample(n, seed, family, float(coefficient))
    started = time.perf_counter()
    order = observed_order(points)
    order_seconds = time.perf_counter()-started
    if profile_memory:
        tracemalloc.start()
    started = time.perf_counter()
    report = estimate(order, k)
    estimate_seconds = time.perf_counter()-started
    peak = None
    if profile_memory:
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
    started = time.perf_counter()
    cdf = cdf_errors(report, family, float(coefficient))
    averages, minima, maxima = truth_cell_ranges(k, family, coefficient)
    bands = report['bands']
    cell_coverage, point_coverage, coefficient_errors, joint = [], [], [], []
    for swap in (0, 1):
        avg, low, high = ((transpose(averages, k), transpose(minima, k), transpose(maxima, k))
                          if swap else (averages, minima, maxima))
        cc = all(a <= b <= c for a, b, c in zip(bands['cell_lower'], avg, bands['cell_upper']))
        pc = all(a <= b and c <= d for a, b, c, d in zip(
            bands['point_lower'], low, high, bands['point_upper']))
        error = max(max(abs(b-a), abs(b-c)) for a, b, c in zip(low, bands['histogram'], high))
        cell_coverage.append(cc)
        point_coverage.append(pc)
        coefficient_errors.append(float(error))
        joint.append(cc and pc and cdf[swap] <= float(report['confidence']['cdf_radius']) and
                     error <= bands['histogram_error_upper'])
    return {'n': n, 'seed': seed, 'family': family, 'coefficient': str(coefficient), 'grid': k,
            'cdf_radius': float(report['confidence']['cdf_radius']),
            'cdf_error': min(cdf), 'cdf_error_each_global_orientation': cdf,
            'cdf_covered': min(cdf) <= float(report['confidence']['cdf_radius']),
            'cell_averages_covered': any(cell_coverage), 'point_bands_covered': any(point_coverage),
            'all_guarantees_one_global_orientation': any(joint),
            'coefficient_error_after_global_swap': min(coefficient_errors),
            'histogram_error_upper': float(bands['histogram_error_upper']),
            'mean_point_band_width': float(sum(b-a for a, b in zip(
                bands['point_lower'], bands['point_upper']))/(k*k)),
            'mean_cell_band_width': float(sum(b-a for a, b in zip(
                bands['cell_lower'], bands['cell_upper']))/(k*k)),
            'forcing_class_edges': report['confidence']['rank_certificate']['class_edges'],
            'rank_trim_budget': float(report['confidence']['rank_certificate']['trim_budget']),
            'solver_status': bands['status'], 'order_seconds': order_seconds,
            'estimate_seconds': estimate_seconds, 'validation_seconds': time.perf_counter()-started,
            'python_traced_peak_bytes': peak, 'memory_profiled': profile_memory}


def wilson(successes, trials):
    z = 1.96
    p = successes/trials
    den = 1+z*z/trials
    mid = (p+z*z/(2*trials))/den
    half = z*math.sqrt(p*(1-p)/trials+z*z/(4*trials*trials))/den
    return [max(0, mid-half), min(1, mid+half)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--trials', type=int, default=8)
    parser.add_argument('--sizes', type=int, nargs='+', default=[128, 512])
    parser.add_argument('--grid', type=int, default=8)
    args = parser.parse_args()
    if args.output.exists() or not 1 <= args.trials <= 100 or any(n < 2 or n > 4096 for n in args.sizes):
        parser.error('choose a fresh output, 1-100 trials, and sizes 2-4096')
    models = [('flat', F(0)), ('fgm', F(-1, 2)), ('fgm', F(1, 2)),
              ('asymmetric', F(-1, 4)), ('asymmetric', F(1, 4))]
    results, summaries, profiles = [], [], []
    for n in args.sizes:
        for index, (family, c) in enumerate(models):
            group = []
            for trial in range(args.trials):
                seed = 2026100700+100000*n+1000*index+trial
                row = evaluate(n, seed, family, c, args.grid)
                results.append(row)
                group.append(row)
                print(json.dumps({'n': n, 'family': family, 'c': str(c), 'trial': trial,
                                  'covered': row['all_guarantees_one_global_orientation'],
                                  'seconds': round(row['estimate_seconds'], 3)}), flush=True)
            count = sum(x['all_guarantees_one_global_orientation'] for x in group)
            # Repeat the first seed once for memory, without counting it as an
            # independent trial or contaminating normal runtime measurements.
            profiles.append(evaluate(n, group[0]['seed'], family, c, args.grid, profile_memory=True))
            summaries.append({'n': n, 'family': family, 'coefficient': str(c), 'trials': args.trials,
                              'joint_coverage_count': count, 'joint_coverage_wilson_95': wilson(count, args.trials),
                              'mean_cdf_radius': sum(x['cdf_radius'] for x in group)/len(group),
                              'mean_cdf_error': sum(x['cdf_error'] for x in group)/len(group),
                              'mean_point_band_width': sum(x['mean_point_band_width'] for x in group)/len(group),
                              'mean_cell_band_width': sum(x['mean_cell_band_width'] for x in group)/len(group)})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({'schema': 1, 'requested_delta': '1/20',
                                      'memory_scope': 'Python-traced peak including tracked arrays; '
                                                      'not total RSS or untracked native solver allocations. '
                                                      'Profiles repeat one seed per case and are not independent trials.',
                                      'coverage_scope': 'Simulations in five specified K densities; '
                                                        'Wilson intervals are diagnostics, not a uniform proof',
                                      'trials': results, 'memory_profiles': profiles,
                                      'summaries': summaries}, indent=2)+'\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
