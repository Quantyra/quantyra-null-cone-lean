"""Exact arithmetic audit of the S031 prose rate constants, not a proof checker.

No data generation, estimator execution, numerical dependency or Lean call.
The general inequalities and probability argument remain ordinary prose proofs.
"""
from fractions import Fraction as F
import argparse
import hashlib
import json
from pathlib import Path


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    root = Path(__file__).resolve().parents[1]
    hmax = F(1, 256)
    checks = {
        'inner_side_lower_factor': 1-16*hmax == F(15, 16),
        'expanded_depth_factor': 8-32*hmax == F(63, 8) and F(63, 8) > 7,
        'erosion_nonempty': F(15, 16)-64*hmax == F(11, 16) > 0,
        'rectangle_variance_factor': F(3, 2)*(2+64*hmax)**2 == F(243, 32) < 8,
        'predecessor_retention_margin': F(49, 2)-3-1 > 6,
        'successor_retention_margin': F(49, 2)-7 > 6,
        'bernstein_exponent_factor': F(16)/(2*(8+F(4, 3))) == F(6, 7),
        'bernstein_log_exponent': F(6, 7)*8 >= 6,
        'cell_average_error_constant': F(3072, 15)+F(6144, 225)+F(1024, 225) == F(53248, 225),
        'quadratic_strip_to_linear': 6*F(512, 15)**2*hmax == F(6144, 225),
        'sqrt_two_upper': F(3, 2)**2 > 2,
        'whole_square_error_constant': F(53248, 225)+4+24 == F(59548, 225) < 270,
        'all_n_rate_constant': 32*270**4 < 650**4,
        'small_mesh_fallback_constant': (2*650)**4 > 8*256**4,
        'probability_at_smallest_comparison_n': F(1, 8*4**3)+F(1, 4**15)+F(4, 4**5) < F(1, 20),
        'TV_large_branch': F(10, 9)*F(9, 10) == 1,
    }
    assert all(checks.values())
    note = root/'notes/finite-data-interior-degree-rate.md'
    result = {'passed': True, 'checks': checks, 'note_sha256': hashlib.sha256(note.read_bytes()).hexdigest(),
              'scope': 'Exact arithmetic of displayed constants only. Not Lean certification, '
                       'a statistical experiment, an implementation, or independent proof review.'}
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
