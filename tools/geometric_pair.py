"""Exact count-input estimator for the accepted restricted 2+1 family.

No sample coordinates, truth parameter or seed enter estimate(). Fractions
certify the polynomial inversion and a conservative 95% Bernstein radius.
"""
from fractions import Fraction as F
from math import factorial

P0 = F(8, 35)
PMAX = F(185489, 750750)
V = F(104849697629, 563625562500)
L = F(3, 20)
C = F(13738, 375375)
K = L / C
MIDPOINT = F(1, 4)
BASE_RADIUS = F(3, 80)
S95 = F(369, 100)
STEPS = 48
GRID = 2**24


def pair_probability(theta):
    theta = F(theta)
    return 2*(F(4, 35)+F(36, 1925)*theta-F(151, 375375)*theta**2)


def inverse_bracket(u):
    u = min(PMAX, max(P0, F(u)))
    if u == P0:
        return F(0), F(0)
    if u == PMAX:
        return F(1, 2), F(1, 2)
    lo, hi = F(0), F(1, 2)
    for _ in range(STEPS):
        mid = (lo+hi)/2
        if pair_probability(mid) <= u:
            lo = mid
        else:
            hi = mid
    return lo, hi


def noise_upper(n):
    m = n//2
    if m < 1:
        raise ValueError('noise bound requires n>=2')
    def polynomial(b):
        return m*b*b-2*S95*(V+b/3)
    lo, hi = F(0), F(1)
    while polynomial(hi) < 0:
        hi *= 2
    for _ in range(STEPS):
        mid = (lo+hi)/2
        if polynomial(mid) < 0:
            lo = mid
        else:
            hi = mid
    return hi


def validate_count(n, relations):
    if type(n) is not int or type(relations) is not int or n < 0:
        raise ValueError('n and R must be nonnegative integers')
    if not 0 <= relations <= n*(n-1)//2:
        raise ValueError('relation count outside strict-order range')


def estimate(n, relations):
    validate_count(n, relations)
    if n < 2:
        return {'n': n, 'relations': relations, 'branch': 'midpoint',
                'theta': str(MIDPOINT), 'radius': str(BASE_RADIUS), 'raw': None}
    u = F(2*relations, n*(n-1))
    lo, hi = inverse_bracket(u)
    theta, rounding = (lo+hi)/2, (hi-lo)/2
    b = noise_upper(n)
    radius = K*b+L*rounding
    inverse = radius <= BASE_RADIUS
    return {'n': n, 'relations': relations, 'branch': 'inverse' if inverse else 'midpoint',
            'theta': str(theta if inverse else MIDPOINT),
            'radius': str(radius if inverse else BASE_RADIUS),
            'raw': {'u': str(u), 'lo': str(lo), 'hi': str(hi), 'theta': str(theta),
                    'rounding': str(rounding), 'b_upper': str(b), 'radius': str(radius)}}


def verify_report(report):
    """Check rational inequalities, not equality to a regenerated report."""
    try:
        n, r = report['n'], report['relations']
        validate_count(n, r)
        if n < 2:
            return report == {'n': n, 'relations': r, 'branch': 'midpoint',
                              'theta': str(MIDPOINT), 'radius': str(BASE_RADIUS), 'raw': None}
        raw = report['raw']
        u, lo, hi, theta, rounding, b, radius = (F(raw[k]) for k in
            ('u', 'lo', 'hi', 'theta', 'rounding', 'b_upper', 'radius'))
        clipped = min(PMAX, max(P0, u))
        inverse = radius <= BASE_RADIUS
        return all((u == F(2*r, n*(n-1)),
            0 <= lo <= hi <= F(1, 2) and hi-lo <= F(1, 2**STEPS),
            pair_probability(lo) <= clipped <= pair_probability(hi),
            theta == (lo+hi)/2 and rounding == (hi-lo)/2,
            b > 0 and (n//2)*b*b >= 2*S95*(V+b/3),
            radius == K*b+L*rounding,
            report['branch'] == ('inverse' if inverse else 'midpoint'),
            F(report['theta']) == (theta if inverse else MIDPOINT),
            F(report['radius']) == (radius if inverse else BASE_RADIUS)))
    except (AssertionError, ValueError, KeyError, TypeError, ZeroDivisionError):
        return False


def validate_points(points):
    import numpy as np
    a = np.asarray(points)
    if a.dtype != np.dtype('int64') or a.ndim != 2 or a.shape[1] != 3:
        raise ValueError('coordinates require an n-by-3 int64 array')
    if np.any(a < -GRID) or np.any(a > GRID):
        raise ValueError('coordinates exceed fixed overflow-safe grid')
    gap = GRID-np.abs(a[:, 0])
    if np.any(gap <= 0) or np.any(a[:, 1]**2+a[:, 2]**2 >= gap**2):
        raise ValueError('point outside the open diamond')
    return a


def relation_count(points, block=512):
    """Exact chronology on dyadic coordinates; stream all unordered pairs.

    Each integer difference is at most 2**25. All three-square arithmetic
    stays in [-2**51,2**50], strictly inside signed int64. No null tolerance.
    A comparable unordered pair contributes one strict directed relation.
    """
    import numpy as np
    a = validate_points(points)
    if type(block) is not int or block < 1:
        raise ValueError('positive block size required')
    count = 0
    for i in range(0, len(a), block):
        left = a[i:i+block]
        for j in range(i, len(a), block):
            right = a[j:j+block]
            delta = left[:, None, 0]-right[None, :, 0]
            square = delta*delta
            for axis in (1, 2):
                delta = left[:, None, axis]-right[None, :, axis]
                square -= delta*delta
            mask = square > 0
            count += int(np.count_nonzero(np.triu(mask, 1) if i == j else mask))
    return count


def reference_relation_count(points):
    """Independent unbounded-Python-integer scalar oracle."""
    a = [[int(v) for v in row] for row in points]
    count = 0
    for i in range(len(a)):
        for j in range(i):
            dt, dx, dy = (a[i][k]-a[j][k] for k in range(3))
            count += dt*dt > dx*dx+dy*dy
    return count


def exact_log_certificate():
    # Positive exponential terms prove exp(369/100)>40, hence log(40)<369/100.
    partial = sum((S95**k/F(factorial(k)) for k in range(21)), F(0))
    return partial > 40
