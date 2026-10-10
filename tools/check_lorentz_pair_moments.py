"""Exact arithmetic checks for an ordinary S042 restricted-family calculation.

No sampled data, estimator benchmark or Lean certification. The geometric
moment and change-of-variable arguments are documented separately.
"""
from fractions import Fraction as F
from math import comb
import argparse
import hashlib
import json
from pathlib import Path
import time


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def integral_unit(a):
    return sum((F(x) / (i + 1) for i, x in enumerate(a)), F(0))


def whole(a):
    return sum((2 * F(x) / (i + 1) for i, x in enumerate(a) if i % 2 == 0), F(0))


def cap_integral(a, power):
    """Integral a(t)*[(1-t)^power-(-4t)_+^(power/2)] from -1 to 1."""
    assert power in (5, 7)
    polynomial = [F((-1) ** i * comb(power, i)) for i in range(power + 1)]
    cap = sum((x * (-1) ** i / (i + F(power, 2) + 1) for i, x in enumerate(a)), F(0))
    return whole(mul(a, polynomial)) - 2 ** power * cap


def calculate():
    # Time marginal in the unit half-duration rest diamond is 3/2*(1-|t|)^2.
    rest_time_second = 3 * integral_unit(mul([0, 0, 1], [1, -2, 1]))
    # Each spatial-coordinate second moment is R^2/4 conditionally on time.
    rest_space_second = F(3, 4) * integral_unit([1, -4, 6, -4, 1])
    assert rest_time_second == F(1, 10)
    assert rest_space_second == F(3, 20)
    # Rescale from half-duration 1 to total duration T: moments /4.
    assert rest_time_second / 4 == F(1, 40)
    assert rest_space_second / 4 == F(3, 80)
    f = [F(-1, 10), 0, 1]
    q0 = F(3, 40) * cap_integral([1], 5)
    q1 = F(3, 20) * cap_integral(f, 5)
    q2 = F(3, 8) * (
        cap_integral(mul(f, [17, 30, 25]), 5) / 400
        - F(3, 560) * cap_integral(f, 7)
    )
    assert (q0, q1, q2) == (F(4, 35), F(36, 1925), -F(151, 375375))
    c = 2 * q1 + 2 * q2  # minimum p'(theta), 0<=theta<=1/2, p=2q
    assert c == F(13738, 375375) and c > 0
    return {
        'status': 'PASS_EXACT_ARITHMETIC_ONLY',
        'random_samples': 0,
        'rest_time_second': str(rest_time_second),
        'rest_space_coordinate_second': str(rest_space_second),
        'ordered_pair_probability_coefficients': list(map(str, (q0, q1, q2))),
        'comparable_pair_derivative_lower': str(c),
        'geometric_forward_factor': '9/10',
        'geometric_to_pair_probability_factor': str(F(9, 10) / c),
        'pair_size': 2,
        'formal_certification': False,
        'scope': 'Checks arithmetic after stated geometric reductions; does not prove those reductions.',
    }


def quadrature():
    """A nonrigorous deterministic check before analytic radial integration."""
    from scipy.integrate import quad
    start = time.monotonic()
    results = []
    expected = [F(4, 35), F(36, 1925), -F(151, 375375)]
    for k in range(3):
        def outer(t):
            def integrand(r):
                mass = max(0, (1-t)**2-r*r)**1.5 / 8
                f = t*t - .1
                conditional = (1+t)**2/4 + (2*(1-t)**2+3*r*r)/80 - .1
                return 3*r*mass*([1, f+conditional, f*conditional][k])
            return quad(integrand, 0, 1-abs(t), epsabs=1e-12, epsrel=1e-12)[0]
        values = [quad(outer, a, b, epsabs=1e-11, epsrel=1e-11)
                  for a, b in [(-1, 0), (0, 1)]]
        actual = sum(v[0] for v in values)
        difference = abs(actual-float(expected[k]))
        assert difference < 1e-10
        results.append({'coefficient': k, 'quadrature': actual,
                        'exact': str(expected[k]), 'absolute_difference': difference,
                        'reported_outer_error_sum': sum(v[1] for v in values)})
    return {'status': 'PASS_DETERMINISTIC_QUADRATURE_DIAGNOSTIC', 'random_samples': 0,
            'results': results, 'elapsed_seconds': time.monotonic()-start,
            'scope': 'Numerical moment integral only; no rigorous enclosure or geometric proof.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quadrature', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate()
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.quadrature:
        result['quadrature'] = quadrature()
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered, encoding='utf-8')
    print(rendered, end='')
