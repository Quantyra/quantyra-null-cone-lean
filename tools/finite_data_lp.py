"""Finite LP relaxation with exact rational outer certificates.

HiGHS suggests multipliers; arbitrary sign-valid multipliers give a bound
after exact box-residual correction. Solver success is not certification.
"""
from fractions import Fraction as F
from math import isfinite

LOW, HIGH = F(1, 2), F(3, 2)


def model(counts, n, radius):
    k = len(counts)-1
    if not 1 <= k <= 16:
        raise ValueError('estimation grid must be in [1,16]')
    variables = k*k
    equalities, eq_rhs, inequalities, rhs = [], [], [], []
    for i in range(k):
        equalities.append([int(j//k == i) for j in range(variables)])
        eq_rhs.append(F(k))
    for i in range(k):
        equalities.append([int(j % k == i) for j in range(variables)])
        eq_rhs.append(F(k))
    for p in range(k+1):
        for q in range(k+1):
            row = [int(i//k < p and i % k < q) for i in range(variables)]
            value = F(counts[p][q], n)
            inequalities += [row, [-x for x in row]]
            rhs += [k*k*(value+radius), k*k*(radius-value)]
    # Translation of two neighboring cells has distance exactly h.
    for i in range(k):
        for j in range(k):
            for u, v in [(i+1, j), (i, j+1)]:
                if u < k and v < k:
                    row = [0]*variables
                    row[i*k+j], row[u*k+v] = 1, -1
                    inequalities += [row, [-x for x in row]]
                    rhs += [F(2, k), F(2, k)]
    return {'k': k, 'A': inequalities, 'b': rhs, 'E': equalities, 'd': eq_rhs}


def rational_float(value):
    value = float(value)
    if not isfinite(value):
        raise ValueError('nonfinite solver value')
    return F(str(value))


def dual_lower_bound(lp, objective, y, z):
    """Weak duality with exact residual correction on the known box."""
    if len(y) != len(lp['A']) or len(z) != len(lp['E']) or any(v > 0 for v in y):
        raise ValueError('invalid dual multipliers')
    if len(objective) != lp['k']**2:
        raise ValueError('invalid objective')
    residual = [F(v) for v in objective]
    for rows, multipliers in [(lp['A'], y), (lp['E'], z)]:
        for row, multiplier in zip(rows, multipliers):
            if multiplier:
                for j, coefficient in enumerate(row):
                    if coefficient:
                        residual[j] -= coefficient*multiplier
    bound = sum(b*v for b, v in zip(lp['b'], y))+sum(d*v for d, v in zip(lp['d'], z))
    return bound+sum(r*(LOW if r >= 0 else HIGH) for r in residual)


def solve(lp):
    import numpy as np
    from scipy.optimize import linprog
    k, variables = lp['k'], lp['k']**2
    A, E = np.asarray(lp['A'], dtype=float), np.asarray(lp['E'], dtype=float)
    b, d = np.asarray(lp['b'], dtype=float), np.asarray(lp['d'], dtype=float)

    def optimize(objective):
        return linprog(objective, A_ub=A, b_ub=b, A_eq=E, b_eq=d,
                       bounds=(float(LOW), float(HIGH)), method='highs',
                       options={'primal_feasibility_tolerance': 1e-9,
                                'dual_feasibility_tolerance': 1e-9})

    # Select a central point by minimizing L1 deviation from the flat density.
    extended_A = np.hstack((A, np.zeros_like(A)))
    extended_E = np.hstack((E, np.zeros_like(E)))
    extra = np.zeros((2*variables, 2*variables))
    for j in range(variables):
        extra[2*j, j], extra[2*j, variables+j] = 1, -1
        extra[2*j+1, j], extra[2*j+1, variables+j] = -1, -1
    initial = linprog([0]*variables+[1]*variables,
                      A_ub=np.vstack((extended_A, extra)),
                      b_ub=np.concatenate((b, np.tile([1, -1], variables))),
                      A_eq=extended_E, b_eq=d,
                      bounds=[(float(LOW), float(HIGH))]*variables+[(0, 0.5)]*variables,
                      method='highs', options={'primal_feasibility_tolerance': 1e-9})
    if not initial.success:
        # No unproved numerical infeasibility is treated as mathematical fact.
        return {'status': 'solver_failed_conservative_fallback',
                'solver_status': int(initial.status), 'histogram': [F(1)]*variables,
                'cell_lower': [LOW]*variables, 'cell_upper': [HIGH]*variables,
                'point_lower': [LOW]*variables, 'point_upper': [HIGH]*variables,
                'certificates': []}
    histogram = [max(LOW, min(HIGH, rational_float(x))) for x in initial.x[:variables]]
    certificates, lower, upper = [], [], []
    for cell in range(variables):
        limits = []
        for sign in (1, -1):
            objective = [0]*variables
            objective[cell] = sign
            result = optimize(objective)
            y, z = [F(0)]*len(b), [F(0)]*len(d)
            if result.success:
                y = [min(F(0), rational_float(v)) for v in result.ineqlin.marginals]
                z = [rational_float(v) for v in result.eqlin.marginals]
            bound = dual_lower_bound(lp, objective, y, z)
            certificates.append({'cell': cell, 'sign': sign, 'y': y, 'z': z,
                                 'lower_bound': bound, 'solver_success': bool(result.success)})
            limits.append(bound)
        lo, hi = max(LOW, limits[0]), min(HIGH, -limits[1])
        if lo > hi:
            # The relaxation can be empty on an exceptional sample. Never claim
            # a guaranteed band from contradictory certified restrictions.
            return {'status': 'inconsistent_bounds_conservative_fallback',
                    'histogram': histogram, 'cell_lower': [LOW]*variables,
                    'cell_upper': [HIGH]*variables, 'point_lower': [LOW]*variables,
                    'point_upper': [HIGH]*variables, 'certificates': certificates}
        lower.append(lo)
        upper.append(hi)
    return {'status': 'certified_outer_bounds', 'histogram': histogram,
            'cell_lower': lower, 'cell_upper': upper,
            'point_lower': [max(LOW, x-F(2, k)) for x in lower],
            'point_upper': [min(HIGH, x+F(2, k)) for x in upper],
            'certificates': certificates}


def verify_bounds(lp, result):
    k = lp['k']
    if result['status'] != 'certified_outer_bounds':
        if any([F(v) for v in result[name]] != [endpoint]*(k*k)
               for name, endpoint in [('cell_lower', LOW), ('cell_upper', HIGH),
                                      ('point_lower', LOW), ('point_upper', HIGH)]):
            raise ValueError('fallback must retain the whole density range')
        return True
    proved = {}
    for cert in result['certificates']:
        cell, sign = cert['cell'], cert['sign']
        if type(cell) is not int or not 0 <= cell < k*k or sign not in (-1, 1):
            raise ValueError('invalid certificate objective')
        objective = [0]*(k*k)
        objective[cell] = sign
        y, z = [F(v) for v in cert['y']], [F(v) for v in cert['z']]
        bound = dual_lower_bound(lp, objective, y, z)
        if bound != F(cert['lower_bound']) or (cell, sign) in proved:
            raise ValueError('incorrect or repeated dual certificate')
        proved[cell, sign] = bound
    for cell in range(k*k):
        lo, hi = max(LOW, proved[cell, 1]), min(HIGH, -proved[cell, -1])
        if lo > hi or F(result['cell_lower'][cell]) != lo or F(result['cell_upper'][cell]) != hi:
            raise ValueError('incorrect outer cell bounds')
        if (F(result['point_lower'][cell]) != max(LOW, lo-F(2, k)) or
                F(result['point_upper'][cell]) != min(HIGH, hi+F(2, k))):
            raise ValueError('incorrect pointwise expansion')
    return True
