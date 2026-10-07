"""Compare two proved calibrations on the same genuine sampled orders."""
import argparse
import hashlib
import json
import platform
from fractions import Fraction as F
from pathlib import Path
from benchmark_finite_data import evaluate
from finite_data_core import calibration, calibration_radius


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--sizes', type=int, nargs='+', default=[512, 3072])
    args = parser.parse_args()
    if args.output.exists() or any(not 2 <= n <= 4096 for n in args.sizes):
        parser.error('fresh output and sizes 2..4096 required')
    models = [('flat', F(0)), ('fgm', F(1, 2)), ('asymmetric', F(1, 4))]
    source = Path(__file__).parent
    hashes = {name: hashlib.sha256((source/name).read_bytes()).hexdigest() for name in
              ['finite_data_core.py', 'finite_data_lp.py', 'finite_data.py',
               'benchmark_finite_data.py', 'compare_confidence_calibrations.py']}
    rows = []
    for n in args.sizes:
        for index, (family, coefficient) in enumerate(models):
            seed = 2026100700+100000*n+1000*index
            print(json.dumps({'started': True, 'n': n, 'family': family, 'seed': seed}), flush=True)
            row = evaluate(n, seed, family, coefficient, 8)
            budget = F(row['rank_trim_budget_exact'])
            old = min(F(1), budget+calibration_radius(calibration(n, F(1, 20)), 'grid'))
            new = F(row['cdf_radius_exact'])
            row.update({'legacy_cdf_radius_exact': str(old), 'legacy_cdf_radius': float(old),
                        'new_radius_below_no_data_prior': new < F(1, 8),
                        'radius_reduction_fraction': float(1-new/old)})
            rows.append(row)
            # Retain each completed case; incomplete runs are explicitly visible.
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps({'schema': 1, 'complete': len(rows) == len(args.sizes)*3,
                'python': platform.python_version(), 'source_sha256': hashes, 'delta': '1/20',
                'coverage_scope': 'Six deterministic-seed diagnostics, not a coverage-rate estimate. '
                                  'New reports independently checked inside estimate; legacy comparison '
                                  'recalibrates the identical rank certificate, without rerunning legacy LP.',
                'cases': rows}, indent=2)+'\n', encoding='utf-8', newline='\n')
            print(json.dumps(row), flush=True)


if __name__ == '__main__':
    main()
