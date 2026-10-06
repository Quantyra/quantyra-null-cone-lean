"""Exact-integer adversarial checks of the finite-order witness geometry.

This is a falsification check, not a proof or a simulation of iid success rates.
"""

SCALE = 1_000_003


def precedes(p, q):
    return p[0] < q[0] and p[1] < q[1]


def incomparable(p, q):
    return (p[0] < q[0] and p[1] > q[1]) or (
        p[0] > q[0] and p[1] < q[1]
    )


def check(m, seed, extreme=False):
    points = []
    for col in range(m):
        for row in range(m):
            label = col * m + row
            if extreme:
                ju = label + 1 if seed == 0 else SCALE - label - 1
                jv = SCALE - label - 1 if seed == 0 else label + 1
            else:
                ju = 1 + (label * 7919 + seed * 1543) % (SCALE - 1)
                jv = 1 + (label * 104729 + seed * 3571) % (SCALE - 1)
            points.append((col * SCALE + ju, row * SCALE + jv))
    assert len({p[0] for p in points}) == len(points)
    assert len({p[1] for p in points}) == len(points)
    a = points[1 * m + m - 2]
    b = points[(m - 2) * m + 1]
    w = points[(m - 1) * m + m - 3]
    assert incomparable(a, b) and incomparable(a, w)
    assert precedes(b, w)
    interior = [p for p in points if all(4 * SCALE <= t <= (m - 4) * SCALE for t in p)]
    first_column = points[:m]
    tested = 0
    for x in interior:
        for y in interior:
            if not (x[0] < y[0] and x[1] - y[1] >= 3 * SCALE):
                continue
            z = next(p for p in first_column if y[1] < p[1] < x[1])
            edges = [(x, y), (z, y), (a, y), (a, w), (a, b)]
            assert all(incomparable(p, q) for p, q in edges)
            assert all(p[0] < q[0] for p, q in edges)
            assert precedes(z, x) and precedes(z, a)
            assert precedes(y, w) and precedes(b, w)
            tested += 1
    assert tested > 0
    return tested


if __name__ == "__main__":
    total = 0
    cases = 0
    for m in (16, 24, 32):
        for seed in range(10):
            total += check(m, seed)
            cases += 1
        for seed in (0, 1):
            total += check(m, seed, extreme=True)
            cases += 1
    assert 4096 * 174 < 100**3
    assert 12 / 256 < 1 / 10
    print(f"PASS: {cases} exact-coordinate grids; {total} separated edges; constants checked")
