"""Falsification checks for logarithmic-grid rounding and analytic constants.

This finite, high-precision check supports notes/grid-scale-optimization.md.
It does not prove the universal inverse theorem or its probability inputs.
"""

from decimal import Decimal, localcontext, ROUND_FLOOR


CUTOFF = 65536


def floor_grid(n):
    value = Decimal(n) / (8 * Decimal(n).ln())
    return int(value.sqrt().to_integral_value(rounding=ROUND_FLOOR))


def transition(m):
    """First n >= cutoff whose grid has at least m cells per axis."""
    lo, hi = CUTOFF, max(CUTOFF + 1, m * m * 128)
    while floor_grid(hi) < m:
        hi *= 2
    while lo < hi:
        mid = (lo + hi) // 2
        if floor_grid(mid) >= m:
            hi = mid
        else:
            lo = mid + 1
    return lo


with localcontext() as context:
    context.prec = 100
    assert 8 * 712704**2 == 4063575932928 < 130**6
    coefficient = (Decimal(712704) * Decimal(8).sqrt()) ** (Decimal(1) / 3)
    assert coefficient < 130
    assert Decimal(2).ln() > Decimal("0.5")
    assert Decimal(1) / 131072 > (Decimal(1) / 8) ** 6
    assert Decimal(1) / (8 * 2**3) + Decimal(2) ** -15 < Decimal("0.1")

    samples = set(range(CUTOFF - 8, CUTOFF + 9))
    samples.update(10**power for power in range(5, 81))
    transitions = 0
    for m in range(floor_grid(CUTOFF) + 1, 201):
        n = transition(m)
        assert floor_grid(n - 1) == m - 1
        assert floor_grid(n) == m
        samples.update((n - 1, n, n + 1))
        transitions += 1

    for n in sorted(samples):
        count = Decimal(n)
        log_n = count.ln()
        if n < CUTOFF:
            assert 130 * (log_n / count) ** (Decimal(1) / 6) > 1
            continue
        m = Decimal(floor_grid(n))
        x = (count / (8 * log_n)).sqrt()
        assert m >= 16 and m >= x / 2
        assert m**2 <= count / (8 * log_n)
        occupancy = m**2 * (-count / (2 * m**2)).exp()
        vertices = 2 * (m + 1)**2 * (-2 * count / m**2).exp()
        occupancy_bound = Decimal(1) / (8 * count**3 * log_n)
        vertex_bound = count**-15 / log_n
        assert occupancy <= occupancy_bound
        assert vertices <= vertex_bound
        assert occupancy + vertices < Decimal("0.1")
        assert 87 / m <= 174 * Decimal(8).sqrt() * (log_n / count).sqrt()
        # Compare the new displayed N term with the original displayed term.
        assert 130 * (log_n / count) ** (Decimal(1) / 6) < (
            100 * count ** (-Decimal(1) / 12)
        )

    print(f"PASS: {len(samples)} sample sizes; {transitions} integer grid transitions; "
          "cutoff, both failure terms, floor factor and exact coefficient constant")
    print(f"Derived coefficient: {coefficient:.15f} < 130")
