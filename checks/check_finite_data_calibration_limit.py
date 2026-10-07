"""Exact obstruction for this grid calibration, not an information lower bound."""
from fractions import Fraction as F
import json


def main():
    # Assume n<=4096, B>=0 and B+3eps+4/q<=1/8. For q<=32,
    # 4/q>=1/8, leaving eps=0 at best, which fails the probability bound.
    # For each remaining q range the displayed constant is a lower bound
    # on 2(q+1)^2 exp(-2n eps^2), even at the largest allowed eps/n.
    cases = [('33..64', 2*34**2, F(32, 9)),
             ('65..128', 2*66**2, F(8)),
             ('129..256', 2*130**2, F(98, 9)),
             ('257 and above', 2*258**2, F(128, 9))]
    results = []
    for q_range, multiplier, t in cases:
        # log(1-x)<=-x implies exp(-t)>=(1-t/s)^s for 0<=t<s.
        lower = multiplier*(1-t/512)**512
        assert lower > F(1, 20)
        results.append({'q_range': q_range, 'multiplier': multiplier,
                        't': str(t), 'lower_formula': 'multiplier*(1-t/512)^512',
                        'diagnostic_decimal_lower': float(lower),
                        'exact_lower_exceeds_delta': True})
    print(json.dumps({'status': 'PASS', 'n_max': 4096, 'delta': '1/20',
                      'no_data_cdf_error_upper': '1/8',
                      'no_data_density_error_upper': '1/2',
                      'conclusion': 'This grid/union-bound certificate cannot beat the flat '
                                    'CDF prior at this confidence within the implemented n range, '
                                    'even with zero forcing ambiguity. Other calibrations/methods '
                                    'are not excluded.', 'cases': results}, indent=2))


if __name__ == '__main__':
    main()
