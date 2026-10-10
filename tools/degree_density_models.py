"""Evaluator-only polynomial models and exact full-cell extrema/integrals."""
from fractions import Fraction as F
from math import comb


def coefficients(family):
    linear = [F(-1), F(2)]
    if family == 'fgm': return linear, linear
    if family == 'asymmetric': return linear, list(map(F, [1, -6, 6]))
    if family == 'boundary8':
        v = [F((-1)**j*comb(8, j)) for j in range(9)]; v[-1] -= 1
        return v, v
    if family == 'legendre4':
        v = list(map(F, [1, -20, 90, -140, 70])); return v, v
    raise ValueError('unknown family')


def polynomial(coefs, t):
    value = 0
    for a in reversed(coefs): value = value*t+a
    return value


def density(u, v, family, coefficient):
    a, b = coefficients(family)
    return 1+coefficient*polynomial(a, u)*polynomial(b, v)


def primitive(coefs, t):
    return sum(a*t**(j+1)/F(j+1) for j, a in enumerate(coefs))


def factor_range(coefs, lo, hi):
    vals = [polynomial(coefs, lo), polynomial(coefs, hi)]
    if coefs == list(map(F, [1, -6, 6])) and lo <= F(1, 2) <= hi:
        vals.append(F(-1, 2))
    if coefs == list(map(F, [1, -20, 90, -140, 70])):
        x, y = 2*lo-1, 2*hi-1
        if x <= 0 <= y: vals.append(F(3, 8))
        # Nonzero critical locations are x=+/-sqrt(3/7), value -3/7.
        for a, b in [(x, y), (-y, -x)]:
            if b >= 0 and max(F(0), a)**2 <= F(3, 7) <= b*b:
                vals.append(F(-3, 7))
    return min(vals), max(vals)


def truth_cells(k, family, coefficient):
    a, b = coefficients(family); c = F(coefficient)
    avg, low, high = [], [], []
    for i in range(k):
        for j in range(k):
            l, r, s, t = F(i, k), F(i+1, k), F(j, k), F(j+1, k)
            values = [1+c*x*y for x in factor_range(a, l, r) for y in factor_range(b, s, t)]
            low.append(min(values)); high.append(max(values))
            avg.append(1+c*k*k*(primitive(a, r)-primitive(a, l))*(primitive(b, t)-primitive(b, s)))
    return avg, low, high


def transpose(values, k):
    return [values[j*k+i] for i in range(k) for j in range(k)]


def metrics(histogram, lower, upper, radius, truth, k, cell_lower=None, cell_upper=None):
    h, lo, hi = [list(map(F, v)) for v in [histogram, lower, upper]]
    radius = F(radius)
    out = []
    for swap in [False, True]:
        avg, low, high = [transpose(v, k) if swap else v for v in truth]
        error = max(max(abs(x-a), abs(x-b)) for x, a, b in zip(h, low, high))
        band = all(a <= b and c <= d for a, b, c, d in zip(lo, low, high, hi))
        cells = True if cell_lower is None else all(F(a) <= b <= F(c) for a, b, c in zip(cell_lower, avg, cell_upper))
        out.append({'swap': swap, 'sup_error': str(error), 'point_band_coverage': band,
                    'cell_average_coverage': cells, 'joint_density_coverage': band and cells and error <= radius})
    return {'orientations': out, 'quotient_sup_error': str(min(F(v['sup_error']) for v in out)),
            'joint_density_coverage': any(v['joint_density_coverage'] for v in out),
            'maximum_width': str(max(b-a for a, b in zip(lo, hi))),
            'mean_width': str(sum(b-a for a, b in zip(lo, hi))/(k*k)), 'radius': str(radius)}


def class_audit():
    cases = {'fgm': (F(1, 2), F(1), F(2), F(2)),
             'asymmetric': (F(1, 4), F(1), F(2), F(6)),
             'boundary8': (F(1, 8), F(1), F(8), F(8)),
             'legendre4': (F(1, 16), F(1), F(20), F(20))}
    result = {}
    for family, (c, bound, du, dv) in cases.items():
        a, b = coefficients(family)
        assert primitive(a, F(1)) == 0 and primitive(b, F(1)) == 0
        assert c*bound*bound <= F(1, 2) and c*c*(du*du+dv*dv) <= 4
        low, high = factor_range(a, F(0), F(1))
        assert -bound <= low <= high <= bound
        low, high = factor_range(b, F(0), F(1))
        assert -bound <= low <= high <= bound
        result[family] = {'maximum_abs_coefficient': str(c), 'gradient_squared_upper': str(c*c*(du*du+dv*dv)),
                          'zero_integrals': True, 'density_range_within_K': True}
    return result
