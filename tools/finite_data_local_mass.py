"""S031 ordinary-proof local-mass candidates; exact standard-library checker.

See notes/finite-data-local-mass-feasibility.md. This is a separate report
schema; existing finite_data reports and accepted Lean sources are unchanged.
"""
from fractions import Fraction as F
from functools import lru_cache
from finite_data_core import (order_rows, realizer, ranks, certify_realizer,
                              forcing_certificate, verify_forcing_certificate,
                              exp_negative_upper, _epsilon_budget)
from finite_data_lp import solve, verify_bounds, LOW, HIGH


def parameters(n, k, delta, variant):
    if type(n) is not int or not 1 <= n <= 4096:
        raise ValueError('sample size outside support')
    if type(k) is not int or not 1 <= k <= 16 or not 0 < delta < 1:
        raise ValueError('invalid grid or delta')
    if variant not in ('bernstein', 'binomial'):
        raise ValueError('unknown candidate')


@lru_cache(maxsize=64)
def calibration(n, k, delta, variant):
    parameters(n, k, delta, variant)
    marginal, _ = _epsilon_budget(n, 4, delta/2)
    # epsilon=1 also gives a deterministic marginal bound if n is tiny.
    result = {'variant': variant, 'marginal_epsilon': marginal,
              'marginal_budget': delta/2, 'cell_budget': delta/2}
    if variant == 'bernstein':
        lo, hi, den = 0, 1000000, 1000000
        v = min(F(1), F(3, 2*k*k))
        while lo < hi:
            mid = (lo+hi)//2
            e = F(mid, den)
            if 2*k*k*exp_negative_upper(n*e*e/(2*(v+e/3))) <= delta/2:
                hi = mid
            else:
                lo = mid+1
        result['cell_epsilon'] = F(lo, den)
    else:
        result['endpoint_denominator'] = 2**20
    return result


def verify_calibration(n, k, delta, cal):
    parameters(n, k, delta, cal['variant'])
    em, dm, dc = (F(cal[name]) for name in
                  ('marginal_epsilon', 'marginal_budget', 'cell_budget'))
    if dm != delta/2 or dc != delta/2 or not 0 <= em <= 1:
        raise ValueError('wrong prespecified allocation')
    if em < 1 and 4*exp_negative_upper(2*n*em*em) > dm:
        raise ValueError('marginal failure exceeds budget')
    if cal['variant'] == 'bernstein':
        ec, v = F(cal['cell_epsilon']), min(F(1), F(3, 2*k*k))
        if not 0 <= ec <= 1 or (ec < 1 and
                2*k*k*exp_negative_upper(n*ec*ec/(2*(v+ec/3))) > dc):
            raise ValueError('cell failure exceeds budget')
    elif cal['endpoint_denominator'] != 2**20:
        raise ValueError('endpoint grid differs from frozen rule')


def count_brackets(first, second, degrees, k, em):
    """All arithmetic is integral/rational; closed outer tests are conservative."""
    n = len(first)
    x, y = ranks(first), ranks(second)
    lower, upper = [0]*(k*k), [n]*(k*k)
    lower_cut, upper_cut = [0]*(k*k), [0]*(k*k)
    for j in sorted({0, *degrees}):
        keep = [i for i, d in enumerate(degrees) if d <= j]
        s = F(j, n)+em
        inner_x, inner_y, outer_x, outer_y = [], [], [], []
        for a in range(k):
            il, ih = n*(F(a, k)+s), n*(F(a+1, k)-s)
            ol, oh = n*(F(a, k)-s), n*(F(a+1, k)+s)
            # Integer cutoffs remove Fraction work from the point/cell loops.
            il = il.numerator//il.denominator
            ih = ih.numerator//ih.denominator
            ol = -(-ol.numerator//ol.denominator)
            oh = oh.numerator//oh.denominator
            inner_x.append({i for i in keep if (a == 0 or x[i] > il)
                            and (a == k-1 or x[i] <= ih)})
            inner_y.append({i for i in keep if (a == 0 or y[i] > il)
                            and (a == k-1 or y[i] <= ih)})
            outer_x.append({i for i in keep if ol <= x[i] <= oh})
            outer_y.append({i for i in keep if ol <= y[i] <= oh})
        for a in range(k):
            for b in range(k):
                cell = a*k+b
                low = len(inner_x[a] & inner_y[b])
                high = min(n, len(outer_x[a] & outer_y[b])+n-len(keep))
                if low > lower[cell]:
                    lower[cell], lower_cut[cell] = low, j
                if high < upper[cell]:
                    upper[cell], upper_cut[cell] = high, j
    return {'lower_counts': lower, 'upper_counts': upper,
            'lower_cutoffs': lower_cut, 'upper_cutoffs': upper_cut}


def binomial_cdf_integer(n, x, p):
    """Return exact numerator/denominator of Pr[Bin(n,p)<=x]."""
    a, b = p.numerator, p.denominator
    if x < 0:
        return 0, 1
    if x >= n or a == 0:
        return 1, 1
    if a == b:
        return 0, 1
    if x > n//2:
        num, den = binomial_cdf_integer(n, n-x-1, 1-p)
        return den-num, den
    term = (b-a)**n
    total = term
    for t in range(x):
        term = term*(n-t)*a//((t+1)*(b-a))
        total += term
    return total, b**n


def lower_tail_ok(n, x, p, alpha):
    num, den = binomial_cdf_integer(n, x, p)
    return num*alpha.denominator <= alpha.numerator*den


def upper_tail_ok(n, x, p, alpha):
    num, den = binomial_cdf_integer(n, x-1, p)
    return (den-num)*alpha.denominator <= alpha.numerator*den


@lru_cache(maxsize=4096)
def binomial_lower(n, x, alpha, denominator=2**20):
    if x == 0:
        return F(0)
    lo, hi = 0, denominator
    while lo < hi:
        mid = (lo+hi+1)//2
        if upper_tail_ok(n, x, F(mid, denominator), alpha):
            lo = mid
        else:
            hi = mid-1
    return F(lo, denominator)


def mass_intervals(n, k, brackets, cal):
    lows, highs = [], []
    alpha = F(cal['cell_budget'])/(2*k*k)
    for low, high in zip(brackets['lower_counts'], brackets['upper_counts']):
        if cal['variant'] == 'bernstein':
            lows.append(max(F(0), F(low, n)-F(cal['cell_epsilon'])))
            highs.append(min(F(1), F(high, n)+F(cal['cell_epsilon'])))
        else:
            lows.append(binomial_lower(n, low, alpha))
            highs.append(1-binomial_lower(n, n-high, alpha))
    return {'lower': lows, 'upper': highs}


def verify_mass_intervals(n, k, brackets, cal, mass):
    if len(mass['lower']) != k*k or len(mass['upper']) != k*k:
        raise ValueError('wrong number of mass endpoints')
    alpha = F(cal['cell_budget'])/(2*k*k)
    for low, high, a, b in zip(brackets['lower_counts'], brackets['upper_counts'],
                                mass['lower'], mass['upper']):
        a, b = F(a), F(b)
        if not 0 <= a <= b <= 1:
            raise ValueError('invalid mass interval')
        if cal['variant'] == 'bernstein':
            ec = F(cal['cell_epsilon'])
            if a != max(F(0), F(low, n)-ec) or b != min(F(1), F(high, n)+ec):
                raise ValueError('incorrect Bernstein mass endpoint')
        elif ((a > 0 and (low == 0 or not upper_tail_ok(n, low, a, alpha))) or
              (b < 1 and (high == n or not lower_tail_ok(n, high, b, alpha)))):
            raise ValueError('binomial endpoint excludes too much probability')


def local_model(k, mass):
    m = k*k
    A, b, E, d = [], [], [], []
    for i in range(k):
        E.extend([[int(j//k == i) for j in range(m)],
                  [int(j % k == i) for j in range(m)]])
        d.extend([F(k), F(k)])
    for cell in range(m):
        row = [int(j == cell) for j in range(m)]
        A.extend([row, [-x for x in row]])
        b.extend([m*F(mass['upper'][cell]), -m*F(mass['lower'][cell])])
    for i in range(k):
        for j in range(k):
            for u, v in ((i+1, j), (i, j+1)):
                if u < k and v < k:
                    row = [0]*m
                    row[i*k+j], row[u*k+v] = 1, -1
                    A.extend([row, [-x for x in row]])
                    b.extend([F(2, k), F(2, k)])
    return {'k': k, 'A': A, 'b': b, 'E': E, 'd': d}


def estimate(order, k=8, delta=F(1, 20), variant='binomial'):
    delta = F(delta)
    parameters(order['n'], k, delta, variant)
    rows = order_rows(order['n'], order['relations'])
    first, second = realizer(rows)
    rank = forcing_certificate(rows, first)
    cal = calibration(len(rows), k, delta, variant)
    bracket = count_brackets(first, second, rank['unresolved_degrees'], k,
                             cal['marginal_epsilon'])
    mass = mass_intervals(len(rows), k, bracket, cal)
    result = solve(local_model(k, mass))
    if result['status'] == 'certified_outer_bounds':
        result['histogram'] = [(a+b)/2 for a, b in
                               zip(result['point_lower'], result['point_upper'])]
        result['histogram_error_upper'] = max(b-a for a, b in
                              zip(result['point_lower'], result['point_upper']))/2
    else:
        result['histogram'] = [F(1)]*(k*k)
        result['histogram_error_upper'] = F(1, 2)
    report = {'schema': 'local-mass-v1', 'input': order, 'grid': k, 'delta': delta,
              'first': first, 'second': second, 'rank_certificate': rank,
              'calibration': cal, 'brackets': bracket, 'mass': mass, 'bands': result}
    verify_report(report)
    return report


def verify_report(report):
    if report['schema'] != 'local-mass-v1':
        raise ValueError('wrong local-mass schema')
    order, k, delta = report['input'], report['grid'], F(report['delta'])
    n = order['n']
    cal, rank = report['calibration'], report['rank_certificate']
    verify_calibration(n, k, delta, cal)
    rows = order_rows(n, order['relations'])
    certify_realizer(rows, report['first'], report['second'])
    verify_forcing_certificate(rows, report['first'], rank)
    bracket = count_brackets(report['first'], report['second'], rank['unresolved_degrees'],
                             k, F(cal['marginal_epsilon']))
    if bracket != report['brackets']:
        raise ValueError('incorrect retained-count bracket')
    verify_mass_intervals(n, k, bracket, cal, report['mass'])
    result = report['bands']
    for key in ('histogram', 'cell_lower', 'cell_upper', 'point_lower', 'point_upper'):
        if len(result[key]) != k*k:
            raise ValueError('wrong band dimension')
    verify_bounds(local_model(k, report['mass']), result)
    expected = [(F(a)+F(b))/2 for a, b in
                zip(result['point_lower'], result['point_upper'])]
    radius = max(F(b)-F(a) for a, b in
                 zip(result['point_lower'], result['point_upper']))/2
    if [F(x) for x in result['histogram']] != expected or F(result['histogram_error_upper']) != radius:
        raise ValueError('incorrect midpoint or error radius')
    return True
