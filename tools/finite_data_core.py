"""Order-only reconstruction and exact, independently checkable certificates.

Golumbic implication-class deletion constructs a transitive orientation.
The returned two permutations are checked separately against every input pair.
All coverage calculations use rational upper bounds; no solver is needed here.
"""
from collections import deque
from fractions import Fraction as F
from math import isqrt
from functools import lru_cache


class InvalidOrder(ValueError):
    pass


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def order_rows(n, relations):
    if type(n) is not int or not 1 <= n <= 4096:
        raise InvalidOrder('n must be an integer in [1,4096]')
    rows = [0]*n
    for pair in relations:
        if len(pair) != 2 or any(type(v) is not int or not 0 <= v < n for v in pair):
            raise InvalidOrder('relation endpoints must be vertex integers')
        u, v = pair
        if u == v:
            raise InvalidOrder('the order must be strict')
        if rows[u] & (1 << v):
            raise InvalidOrder('duplicate relation')
        rows[u] |= 1 << v
    for u in range(n):
        for v in bits(rows[u]):
            if rows[v] & ((1 << u) | ~rows[u]):
                raise InvalidOrder('order is cyclic or missing a transitive relation')
    return rows


def incomparability(rows):
    n = len(rows)
    incoming = [0]*n
    for u, row in enumerate(rows):
        for v in bits(row):
            incoming[v] |= 1 << u
    return [((1 << n)-1) & ~(rows[i] | incoming[i] | (1 << i)) for i in range(n)]


def implication_class(graph, seed, with_trace=False):
    """Closure of directed seed under induced-P3 shared-endpoint forcing."""
    oriented = [0]*len(graph)
    incoming = [0]*len(graph)
    queue = deque()
    trace = []

    def add(arc, parent):
        u, v = arc
        if oriented[v] & (1 << u):
            raise InvalidOrder('incomparability graph is not transitively orientable')
        if not oriented[u] & (1 << v):
            oriented[u] |= 1 << v
            incoming[v] |= 1 << u
            queue.append(arc)
            trace.append((arc, parent))

    add(seed, None)
    while queue:
        u, v = queue.popleft()
        for w in bits(graph[u] & ~graph[v] & ~(1 << v) & ~oriented[u]):
            add((u, w), (u, v))
        for w in bits(graph[v] & ~graph[u] & ~(1 << u) & ~incoming[v]):
            add((w, v), (u, v))
    return (oriented, trace) if with_trace else oriented


def remove_class(graph, cls):
    for u, row in enumerate(cls):
        graph[u] &= ~row
        for v in bits(row):
            graph[v] &= ~(1 << u)


def realizer(rows):
    graph = incomparability(rows)
    orientation = [0]*len(rows)
    while any(graph):
        u = next(i for i, row in enumerate(graph) if row)
        v = next(bits(graph[u]))
        cls = implication_class(graph, (u, v))
        for i in range(len(rows)):
            orientation[i] |= cls[i]
        remove_class(graph, cls)
    reverse = [0]*len(rows)
    for u, row in enumerate(orientation):
        for v in bits(row):
            reverse[v] |= 1 << u

    def tournament_order(extra):
        tournament = [rows[i] | extra[i] for i in range(len(rows))]
        incoming_counts = [0]*len(rows)
        for row in tournament:
            for v in bits(row):
                incoming_counts[v] += 1
        if sorted(incoming_counts) != list(range(len(rows))):
            raise InvalidOrder('failed realizer tournament certificate')
        return sorted(range(len(rows)), key=incoming_counts.__getitem__)

    first, second = tournament_order(orientation), tournament_order(reverse)
    certify_realizer(rows, first, second)
    return first, second


def ranks(permutation):
    result = [0]*len(permutation)
    for i, vertex in enumerate(permutation):
        result[vertex] = i+1
    return result


def certify_realizer(rows, first, second):
    n = len(rows)
    if (any(type(v) is not int for v in first+second) or
            sorted(first) != list(range(n)) or sorted(second) != list(range(n))):
        raise InvalidOrder('realizer is not two vertex permutations')
    x, y = ranks(first), ranks(second)
    for u in range(n):
        expected = sum(1 << v for v in range(n) if x[u] < x[v] and y[u] < y[v])
        if expected != rows[u]:
            raise InvalidOrder('realizer intersection differs from input order')
    return True


def forcing_certificate(rows, first):
    """Largest ORIGINAL-graph implication class, plus unresolved vertex degrees.

    Deleted-edge classes construct the realizer; original classes justify a
    statement about EVERY realizer. They must not be confused.
    """
    original = incomparability(rows)
    remaining = original.copy()
    largest = [0]*len(rows)
    size = 0
    while any(remaining):
        u = next(i for i, row in enumerate(remaining) if row)
        cls = implication_class(original, (u, next(bits(remaining[u]))))
        new_size = sum(r.bit_count() for r in cls)
        if new_size > size:
            largest, size = cls, new_size
        remove_class(remaining, cls)
    covered = [0]*len(rows)
    pos = ranks(first)
    direction = None
    for u, row in enumerate(largest):
        for v in bits(row):
            agrees = pos[u] < pos[v]
            if direction is not None and agrees != direction:
                raise InvalidOrder('selected realizer violates original forcing class')
            direction = agrees
            covered[u] |= 1 << v
            covered[v] |= 1 << u
    degrees = [(original[i] & ~covered[i]).bit_count() for i in range(len(rows))]
    n = len(rows)
    candidates = [0]+sorted(set(degrees))
    budget, cutoff = min((F(sum(d > j for d in degrees)+2*j, n), j)
                         for j in candidates)
    anchor = next(((u, v) for u, row in enumerate(largest)
                   for v in bits(row)), None)
    trace = implication_class(original, anchor, with_trace=True)[1] if anchor else []
    return {'anchor': anchor, 'class_edges': size, 'forcing_tree': trace,
            'unresolved_degrees': degrees, 'trim_cutoff': cutoff,
            'trim_budget': min(F(1), budget)}


def exp_negative_upper(t, subdivisions=512):
    """exp(-t) <= (1+t/s)^(-s), from exp(t/s)>=1+t/s."""
    if t < 0:
        raise ValueError('negative exponent magnitude')
    return (1 + F(t)/subdivisions)**(-subdivisions)


@lru_cache(maxsize=512)
def _calibration(n, delta):
    if not 0 < delta < 1:
        raise ValueError('delta must lie strictly between zero and one')
    denominator = 1000000
    choices = []
    for q in sorted(set([max(1, min(4096, isqrt(n)))]+[2**i for i in range(13)])):
        lo, hi = 0, denominator
        while lo < hi:
            mid = (lo+hi)//2
            eps = F(mid, denominator)
            failure = 2*(q+1)**2 * exp_negative_upper(2*n*eps*eps)
            if failure <= delta:
                hi = mid
            else:
                lo = mid+1
        eps = F(lo, denominator)
        raw = min(F(1), 2*(q+1)**2*exp_negative_upper(2*n*eps*eps))
        # An exact outward rounding keeps JSON certificates compact.
        denominator_failure = 10**12*delta.denominator
        failure = F(-(-raw.numerator*denominator_failure//raw.denominator), denominator_failure)
        choices.append((3*eps+F(4, q), q, eps, failure))
    _, q, eps, failure = min(choices)
    return q, eps, failure


def calibration(n, delta):
    delta = F(delta)
    q, eps, failure = _calibration(n, delta)
    return {'q': q, 'epsilon': eps, 'failure_upper': failure, 'requested_delta': delta}


def corner_counts(first, second, k):
    x, y = ranks(first), ranks(second)
    n = len(x)
    return [[sum(k*x[i] <= p*n and k*y[i] <= q*n for i in range(n))
             for q in range(k+1)] for p in range(k+1)]


def confidence(first, second, rows, delta):
    cert = forcing_certificate(rows, first)
    cal = calibration(len(rows), delta)
    radius = min(F(1), cert['trim_budget']+3*cal['epsilon']+F(4, cal['q']))
    # A radius of one is deterministic, including when the union bound is weak.
    return {'rank_certificate': cert, 'calibration': cal, 'cdf_radius': radius,
            'failure_upper': F(0) if radius == 1 else cal['failure_upper']}


def verify_forcing_certificate(rows, first, cert):
    """Check supplied witness tree; does not call the orientation constructor."""
    graph = incomparability(rows)
    seen = set()
    covered = [0]*len(rows)
    direction = None
    pos = ranks(first)
    for arc, parent in cert['forcing_tree']:
        u, v = arc
        if not graph[u] & (1 << v) or (u, v) in seen or (v, u) in seen:
            raise InvalidOrder('invalid forcing arc')
        if parent is None:
            if seen or tuple(arc) != tuple(cert['anchor']):
                raise InvalidOrder('invalid forcing root')
        else:
            a, b = parent
            if (a, b) not in seen:
                raise InvalidOrder('forcing parent has not been established')
            if not ((a == u and b != v and not graph[b] & (1 << v)) or
                    (b == v and a != u and not graph[a] & (1 << u))):
                raise InvalidOrder('forcing witness is not an induced P3')
        agrees = pos[u] < pos[v]
        if direction is not None and agrees != direction:
            raise InvalidOrder('forcing orientation is inconsistent')
        direction = agrees
        seen.add((u, v))
        covered[u] |= 1 << v
        covered[v] |= 1 << u
    degrees = [(graph[i] & ~covered[i]).bit_count() for i in range(len(rows))]
    cutoff = cert['trim_cutoff']
    if type(cutoff) is not int or not 0 <= cutoff < len(rows):
        raise InvalidOrder('invalid trim cutoff')
    budget = min(F(1), F(sum(d > cutoff for d in degrees)+2*cutoff, len(rows)))
    if cert['class_edges'] != len(seen) or degrees != cert['unresolved_degrees'] or budget != F(cert['trim_budget']):
        raise InvalidOrder('rank certificate counts differ')
    return True
