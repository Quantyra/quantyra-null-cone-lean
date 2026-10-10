"""Marked interval reports. Float proposals are checked with exact integer tails.

This executable has ordinary mathematical coverage support. Consult the formal
map before attributing Lean coverage to any implementation operation.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, comb, factorial, floor, isfinite, isqrt


@dataclass(frozen=True)
class Interval:
    lower: F
    upper: F
    adjustments: int = 0
    fallback: bool = False

    def __post_init__(self):
        if not 0 <= self.lower <= self.upper <= 1:
            raise ValueError("Invalid probability interval")


def marked_count(flags):
    """Each row is (anchor precedes event, event precedes anchor)."""
    n = x = 0
    for row in flags:
        if len(row) != 2 or any(type(bit) is not bool for bit in row):
            raise ValueError("Both exact Boolean chronological flags are required")
        n += 1
        x += row[0] and row[1]
    return x, n


def _validate(x, n):
    if type(x) is not int or type(n) is not int or not 0 <= x <= n:
        raise ValueError("Require integer 0 <= x <= n")


def binomial_tail_numerator(n, k, m, d, upper):
    """Exact numerator of P(K>=k) or P(K<=k), denominator d**n."""
    _validate(k, n)
    if type(m) is not int or type(d) is not int or not 0 <= m <= d or d <= 0:
        raise ValueError("Invalid rational binomial parameter")
    if m in (0, d):
        atom = n if m == d else 0
        return d**n if (atom >= k if upper else atom <= k) else 0
    start, stop = (k, n) if upper else (0, k)
    term = comb(n, start) * m**start * (d-m)**(n-start)
    total = term
    for j in range(start, stop):
        numerator = term * (n-j) * m
        denominator = (j+1) * (d-m)
        term, remainder = divmod(numerator, denominator)
        if remainder:
            raise ArithmeticError("Integer binomial recurrence failed")
        total += term
    return total


def tail_at_most(n, k, p, alpha, upper):
    return (binomial_tail_numerator(n, k, p.numerator, p.denominator, upper)
            * alpha.denominator <= alpha.numerator * p.denominator**n)


def verify_interval(x, n, report, delta=F(1, 20)):
    _validate(x, n)
    if not 0 < delta < 1:
        raise ValueError("Require 0 < delta < 1")
    if n == 0:
        return report.lower == 0 and report.upper == 1
    return ((report.lower == 0 if x == 0 else tail_at_most(n, x, report.lower, delta/2, True))
            and (report.upper == 1 if x == n else tail_at_most(n, x, report.upper, delta/2, False)))


@lru_cache(maxsize=8192)
def exact_interval(x, n, delta=F(1, 20), denominator=65536):
    """Outward grid approximation to Clopper-Pearson, exact checked before return."""
    _validate(x, n)
    if not 0 < delta < 1 or type(denominator) is not int or denominator <= 0:
        raise ValueError("Invalid calibration")
    if n == 0:
        return Interval(F(0), F(1))
    from scipy.stats import beta
    lo = 0.0 if x == 0 else float(beta.ppf(float(delta/2), x, n-x+1))
    hi = 1.0 if x == n else float(beta.isf(float(delta/2), x+1, n-x))
    if not (isfinite(lo) and isfinite(hi) and 0 <= lo <= hi <= 1):
        return Interval(F(0), F(1), fallback=True)
    ml, mu = floor(lo*denominator), ceil(hi*denominator)
    adjustments = 0
    while x > 0 and not tail_at_most(n, x, F(ml, denominator), delta/2, True):
        ml = max(0, ml-1)
        adjustments += 1
        if adjustments > 8:
            return Interval(F(0), F(1), adjustments, True)
    while x < n and not tail_at_most(n, x, F(mu, denominator), delta/2, False):
        mu = min(denominator, mu+1)
        adjustments += 1
        if adjustments > 8:
            return Interval(F(0), F(1), adjustments, True)
    return Interval(F(ml, denominator), F(mu, denominator), adjustments)


def analytic_interval(x, n):
    """95% Hoeffding comparison with exact rational radius >= sqrt(2/n).

    exp(4) >= sum_{j=0}^5 4**j/j! > 40, so 2*exp(-4) < 1/20.
    No float logarithm or square root is used to choose this radius.
    """
    _validate(x, n)
    if n == 0:
        return Interval(F(0), F(1))
    assert sum(F(4)**j/factorial(j) for j in range(6)) > 40
    d = 2**24
    m = isqrt((2*d*d)//n)
    if m*m*n < 2*d*d:
        m += 1
    radius = F(m, d)
    assert radius*radius*n >= 2
    center = F(x, n)
    return Interval(max(F(0), center-radius), min(F(1), center+radius))


def retention_interval(report, ratio):
    ratio = F(ratio)
    if ratio < 1:
        raise ValueError("Require retention ratio >= 1")
    l, u = report.lower, report.upper
    return Interval(l/(ratio-(ratio-1)*l), ratio*u/(1+(ratio-1)*u),
                    report.adjustments, report.fallback)


def detected_probability(physical, ratio, pattern):
    physical, ratio = F(physical), F(ratio)
    if not 0 <= physical <= 1 or ratio < 1:
        raise ValueError("Invalid physical probability or ratio")
    if pattern == "uniform":
        return physical
    if pattern == "lower_in_interval":
        return physical/(ratio-(ratio-1)*physical)
    if pattern == "higher_in_interval":
        return ratio*physical/(1+(ratio-1)*physical)
    raise ValueError("Unknown retention pattern")
