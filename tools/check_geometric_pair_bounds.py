"""Exact arithmetic supporting the ordinary S042 pair-confidence audit.

No sampled data, benchmark, numerical integration or Lean invocation. Geometry,
change of variables and probability arguments are proved in the companion note;
this checks their rational consequences, not those analytic arguments.
"""
from fractions import Fraction as F
from itertools import permutations
from math import comb, factorial
from pathlib import Path
import argparse
import hashlib
import json
import runpy


def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for key, coefficient in polynomial.items():
            result[key] = result.get(key, F(0)) + coefficient
    return {key: coefficient for key, coefficient in result.items() if coefficient}


def scale(coefficient, polynomial):
    return {key: F(coefficient) * value for key, value in polynomial.items()}


def multiply(left, right):
    result = {}
    for (i, j), x in left.items():
        for (k, ell), y in right.items():
            key = (i + k, j + ell)
            result[key] = result.get(key, F(0)) + x * y
    return result


def integrate(polynomial, power=F(3, 2)):
    """Integral 6(b-a)*(ab)^power*polynomial(a,b) on 0<=a<=b<=1."""
    return sum((6 * coefficient /
                ((i + power + 1) * (i + power + 2) *
                 (i + j + 2 * power + 3))
                for (i, j), coefficient in polynomial.items()), F(0))


def ceiling(value):
    return -(-value.numerator // value.denominator)


def required_even_n(delta, variance, log_upper, method):
    # The corresponding sufficient bound is m >= rhs, n = 2m.
    if method == 'hoeffding':
        rhs = log_upper / (2 * delta ** 2)
    elif method == 'bernstein':
        rhs = 2 * (variance + delta / 3) * log_upper / delta ** 2
    else:
        raise ValueError(method)
    m = ceiling(rhs)
    assert m - 1 < rhs <= m
    return 2 * m


def calculate():
    one = {(0, 0): F(1)}
    a, b = {(1, 0): F(1)}, {(0, 1): F(1)}
    t = add(one, scale(-1, a), scale(-1, b))
    r = add(b, scale(-1, a))
    t2, r2 = multiply(t, t), multiply(r, r)
    ft, fr = add(t2, scale(F(-1, 10), one)), add(r2, scale(F(-3, 10), one))
    mt = add(scale(F(7, 40), one), scale(F(18, 40), t),
             scale(F(11, 40), t2), scale(F(3, 80), r2))
    one_minus_t = add(one, scale(-1, t))
    mr = add(scale(F(3, 40), multiply(one_minus_t, one_minus_t)),
             scale(F(19, 80), r2), scale(F(-3, 10), one))
    moments = [integrate(one, 0), integrate(t2, 0),
               integrate(multiply(t2, t2), 0), integrate(r2, 0),
               integrate(multiply(ft, ft), 0)]
    assert moments == [F(1), F(1, 10), F(1, 35), F(3, 10), F(13, 700)]
    q = [integrate(one), integrate(add(ft, mt)), integrate(multiply(ft, mt))]
    assert q == [F(4, 35), F(36, 1925), F(-151, 375375)]
    old_path = Path(__file__).with_name('check_lorentz_pair_moments.py')
    old_result = runpy.run_path(str(old_path))['calculate']()
    assert old_result['ordered_pair_probability_coefficients'] == list(map(str, q))
    c = 2 * q[1] + 2 * q[2]
    assert c == F(13738, 375375) and c > 0
    p0, pmax = 2 * q[0], 2 * (q[0] + q[1] / 2 + q[2] / 4)
    assert 0 < p0 < pmax < F(1, 2)
    variance = pmax * (1 - pmax)

    # Pi > 3.14; cubing proves the weight derivative is <= 27/100.
    pi_lower, rho_lower, weight_derivative_upper = F(157, 50), F(19, 20), F(27, 100)
    cube_product = 27 * (2 * pi_lower / 3) * rho_lower ** 2 * weight_derivative_upper ** 3
    assert cube_product > 1
    # sqrt(10) >= 3, so integral |t^2-1/10| dt <= 7/15+4/45.
    time_integral_upper = F(7, 15) + F(4, 45)
    assert time_integral_upper == F(5, 9)
    geometric_factor = weight_derivative_upper * time_integral_upper
    assert geometric_factor == F(3, 20)
    assert F(13, 700) < geometric_factor ** 2
    midpoint_radius = geometric_factor / 4
    assert midpoint_radius == F(3, 80)
    old_factor = F(old_result['geometric_forward_factor'])
    assert old_factor / geometric_factor == 6

    # Positive Taylor terms certify exp(369/100)>40, hence ln(40)<369/100.
    log_upper = F(369, 100)
    exponential_partial_sum = sum((log_upper ** k / factorial(k) for k in range(21)), F(0))
    assert exponential_partial_sum > 40
    rows = []
    for epsilon in (F(1, 40), F(1, 100), F(1, 200)):
        assert 0 < epsilon < midpoint_radius
        rows.append({
            'geometric_radius': str(epsilon),
            'old_factor_hoeffding_n': required_even_n(c * epsilon / old_factor, variance, log_upper, 'hoeffding'),
            'new_factor_hoeffding_n': required_even_n(c * epsilon / geometric_factor, variance, log_upper, 'hoeffding'),
            'new_factor_bernstein_n': required_even_n(c * epsilon / geometric_factor, variance, log_upper, 'bernstein'),
        })
    crossover_delta = c / 4
    crossovers = {method: required_even_n(crossover_delta, variance, log_upper, method)
                  for method in ('hoeffding', 'bernstein')}

    # Bounded sanity check of the pointwise all-permutations identity; the note
    # proves it for every n. No stochastic input or simulated observation.
    permutation_checks = []
    for n in range(2, 9):
        m = n // 2
        counts = {(i, j): 0 for i in range(n) for j in range(i + 1, n)}
        for permutation in permutations(range(n)):
            for k in range(m):
                edge = tuple(sorted((permutation[2 * k], permutation[2 * k + 1])))
                counts[edge] += 1
        assert set(counts.values()) == {F(m * factorial(n), comb(n, 2))}
        permutation_checks.append({'n': n, 'permutations': factorial(n),
                                   'occurrences_per_edge': next(iter(counts.values()))})

    candidates = []
    for name, ac, bc, expected_q, expected_f2 in [
        ('retained_time', F(1), F(0), q, F(13, 700)),
        ('spatial', F(0), F(-1), [F(4, 35), F(52, 1925), F(701, 375375)], F(37, 700)),
        ('density_box_vertex', F(2, 3), F(-4, 3), [F(4, 35), F(8, 165), F(548, 135135)], F(41, 315)),
    ]:
        shape, conditional = add(scale(ac, ft), scale(bc, fr)), add(scale(ac, mt), scale(bc, mr))
        cq = [integrate(one), integrate(add(shape, conditional)), integrate(multiply(shape, conditional))]
        assert cq == expected_q and integrate(shape, 0) == 0
        assert integrate(multiply(shape, shape), 0) == expected_f2
        candidates.append({'name': name, 'a': str(ac), 'b': str(bc),
                           'q_coefficients': list(map(str, cq)),
                           'pair_slope_lower': str(min(2 * cq[1], 2 * cq[1] + 2 * cq[2])),
                           'shape_second_moment': str(expected_f2)})
    # Vertex: max_r |f(t,r)| switches at |t|=1/4. Exact integration of the
    # two quadratics gives 23/18. The coarser weight derivative is <=3/7.
    def primitive(coefficients, x):
        return sum((coefficient * x ** (k + 1) / (k + 1)
                    for k, coefficient in enumerate(coefficients)), F(0))
    vertex_integral = 2 * (primitive([F(1), F(-8, 3), F(2, 3)], F(1, 4)) +
                           primitive([F(1, 3), F(0), F(2, 3)], F(1)) -
                           primitive([F(1, 3), F(0), F(2, 3)], F(1, 4)))
    assert vertex_integral == F(23, 18)
    assert 27 * 2 * F(1, 2) ** 2 * F(3, 7) ** 3 > 1
    vertex_factor = F(11, 20)
    assert F(3, 7) * vertex_integral < vertex_factor
    assert F(41, 315) < vertex_factor ** 2
    assert vertex_factor / F(16, 165) > geometric_factor / c
    candidates[-1]['geometric_factor_upper'] = str(vertex_factor)
    candidates[-1]['inverse_factor_upper'] = str(vertex_factor / F(16, 165))

    return {
        'status': 'PASS_EXACT_ARITHMETIC_ONLY',
        'scope': 'Rational consequences of the ordinary geometric/probability proof; analytic steps are not certified by this script.',
        'formal_certification': False, 'random_samples': 0, 'lean_invocations': 0,
        'flat_moments': dict(zip(['mass', 't2', 't4', 'r2', 'f2'], map(str, moments))),
        'q_coefficients': list(map(str, q)),
        'independent_radial_checker_agrees': True,
        'radial_checker_sha256': hashlib.sha256(old_path.read_bytes()).hexdigest(),
        'pair_slope_lower': str(c), 'pmax': str(pmax), 'bernoulli_variance_upper': str(variance),
        'weight_derivative_upper': str(weight_derivative_upper),
        'weight_derivative_cube_check': str(cube_product),
        'time_integral_upper': str(time_integral_upper),
        'geometric_factor': str(geometric_factor), 'geometric_inverse_factor': str(geometric_factor / c),
        'midpoint_geometric_radius': str(midpoint_radius),
        'sample_bound': {'alpha': '1/20', 'log_upper': str(log_upper),
                         'log_upper_proof': 'Positive exponential Taylor sum k=0..20 is greater than 40.',
                         'rows': rows, 'at_most_midpoint_even_n': crossovers,
                         'interpretation': 'Sufficient bounds, not necessary sample sizes, minimax lower bounds or measured performance. All-pairs proof uses effective m=floor(n/2), not n choose 2 independent observations.'},
        'permutation_identity_checks': permutation_checks,
        'quadratic_candidates': candidates,
        'decision': 'Retain time family; sharper pair slope alone does not improve the audited geometric error guarantee.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate()
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding='utf-8')
    print(rendered, end='')
