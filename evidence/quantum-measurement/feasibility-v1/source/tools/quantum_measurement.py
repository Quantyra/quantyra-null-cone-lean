"""S047 loss-only Pauli-Z reports; ordinary coverage argument in the model note.

The exact-binomial marginal implementation is reused. This executable and its
quantum model bridge are not asserted to be Lean verified.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isfinite

from marked_volume import Interval, exact_interval

ALPHA = F(1, 20)
DELTA = ALPHA / 4
LOWER_EFFICIENCY = F(1, 2)


@dataclass(frozen=True)
class Report:
    lower: F
    upper: F
    fallback: str = ""

    def __post_init__(self):
        if not 0 <= self.lower <= self.upper <= 1:
            raise ValueError("Invalid p report")

    @property
    def theta_radius(self):
        return self.upper - self.lower


def probabilities(p, plus, minus):
    p, plus, minus = map(F, (p, plus, minus))
    if not (0 <= p <= 1 and LOWER_EFFICIENCY <= plus <= 1
            and LOWER_EFFICIENCY <= minus <= 1):
        raise ValueError("Outside the frozen model")
    return (p*plus, (1-p)*minus, 1-p*plus-(1-p)*minus)


def _calibration(interval):
    return max(LOWER_EFFICIENCY, interval.lower), interval.upper


def project_box(rplus, rminus, eplus, eminus):
    """Closed-form report (2); inputs are probability intervals."""
    lp, up = _calibration(eplus)
    lm, um = _calibration(eminus)
    if up < lp or um < lm:
        return Report(F(0), F(1), "empty_calibration")
    low = max(F(0), rplus.lower/up, 1-rminus.upper/lm)
    high = min(F(1), rplus.upper/lp, 1-rminus.lower/um)
    if low > high:
        return Report(F(0), F(1), "empty_projection")
    return Report(low, high)


def baseline_box(rplus, rminus, eplus, eminus):
    """Generic one-variable linear feasibility after nuisance elimination.

    Solve a*p <= b separately, instead of calling the closed-form report.
    The feasible set and the full-range fallback match the candidate.
    """
    ep = _calibration(eplus)
    em = _calibration(eminus)
    if any(u < l for l, u in (ep, em)):
        return Report(F(0), F(1), "empty_calibration")
    inequalities = [(F(-1), F(0)), (F(1), F(1)),
                    (-ep[1], -rplus.lower), (ep[0], rplus.upper),
                    (em[1], em[1]-rminus.lower),
                    (-em[0], rminus.upper-em[0])]
    low, high = F(0), F(1)
    for slope, bound in inequalities:
        if slope > 0:
            high = min(high, bound/slope)
        elif slope < 0:
            low = max(low, bound/slope)
        elif bound < 0:
            return Report(F(0), F(1), "empty_projection")
    if low > high:
        return Report(F(0), F(1), "empty_projection")
    return Report(low, high)


def marginal_intervals(n, positive, negative, m, cal_positive, cal_negative):
    if (type(n) is not int or type(m) is not int or n < 0 or m < 0
            or any(type(k) is not int for k in
                   (positive, negative, cal_positive, cal_negative))
            or not 0 <= positive <= n or not 0 <= negative <= n-positive
            or not 0 <= cal_positive <= m or not 0 <= cal_negative <= m):
        raise ValueError("Invalid complete-record counts")
    return (exact_interval(positive, n, DELTA),
            exact_interval(negative, n, DELTA),
            exact_interval(cal_positive, m, DELTA),
            exact_interval(cal_negative, m, DELTA))


def joint_loglikelihood(point, counts):
    """Log likelihood and analytic gradient, omitting multinomial constants."""
    import numpy as np
    p, ep, em = point
    n, xp, xm, m, kp, km = counts
    x0 = n-xp-xm
    probs = np.array([p*ep, (1-p)*em, 1-p*ep-(1-p)*em,
                      ep, 1-ep, em, 1-em])
    freq = np.array([xp, xm, x0, kp, m-kp, km, m-km])
    jac = np.array([[ep, p, 0], [-em, 0, 1-p],
                    [em-ep, -p, -(1-p)], [0, 1, 0], [0, -1, 0],
                    [0, 0, 1], [0, 0, -1]])
    active = freq > 0
    if np.any(probs[active] <= 0):
        return float("-inf"), np.zeros(3)
    value = float(np.dot(freq[active], np.log(probs[active])))
    gradient = (freq[active]/probs[active]) @ jac[active]
    return value, gradient


def joint_fit(counts):
    """Three fixed SLSQP starts for the restricted joint likelihood.

    This is a point diagnostic, not a certified global MLE or confidence set.
    Record failures and select the best feasible finite returned candidate.
    """
    from scipy.optimize import minimize
    trials = []
    def objective(point):
        value, gradient = joint_loglikelihood(point, counts)
        return -value, -gradient
    for start in ((.25, .625, .875), (.5, .75, .75), (.75, .875, .625)):
        result = minimize(objective, start, jac=True, method="SLSQP",
                          bounds=((0, 1), (.5, 1), (.5, 1)),
                          options={"maxiter": 300, "ftol": 1e-10})
        x = tuple(float(v) for v in result.x)
        value, gradient = joint_loglikelihood(x, counts)
        feasible = (all(isfinite(v) for v in x) and 0 <= x[0] <= 1
                    and .5 <= x[1] <= 1 and .5 <= x[2] <= 1
                    and isfinite(value))
        # Each coordinate slice is concave. This bounds its possible
        # single-coordinate gain only, never a joint global gap.
        gap = None
        if feasible:
            limits = ((0, 1), (.5, 1), (.5, 1))
            gap = sum(max(float(g)*(lo-v), float(g)*(hi-v))
                      for g, v, (lo, hi) in zip(gradient, x, limits))
        trials.append(dict(point=x, loglikelihood=value if isfinite(value) else None,
                           success=bool(result.success), feasible=feasible,
                           status=int(result.status), message=str(result.message),
                           iterations=int(result.nit), coordinate_gap=gap))
    eligible = [r for r in trials if r["feasible"]]
    best = max(eligible, key=lambda r: r["loglikelihood"]) if eligible else None
    return dict(best=best, starts=trials,
                scope="restricted joint-likelihood point diagnostic; no global certificate")
