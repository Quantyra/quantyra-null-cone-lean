"""Exact categorical model geometry and an independent continuous-LP audit.

All Fraction calculations are exact. SciPy LP checks are numerical cross-checks,
not substitutes for the ordinary proof in beam-profile-bridge.md. The data check
reads only the previously inspected Merged_small fixture.
"""

import argparse
from fractions import Fraction as F
import hashlib
from importlib.metadata import version
from itertools import product
import json
from pathlib import Path
import platform

import h5py
import hdf5plugin
import numpy as np
from scipy.optimize import linprog


HERE = Path(__file__).resolve().parent
DIRECTIONS = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1),
              (2, 1), (2, -1), (-2, 1), (-2, -1), (1, 2), (1, -2), (-1, 2), (-1, -2)]


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def hull(points):
    points = sorted(set(points))
    if len(points) <= 1:
        return points
    lower, upper = [], []
    for chain, iterator in [(lower, points), (upper, reversed(points))]:
        for point in iterator:
            while len(chain) >= 2 and cross(chain[-2], chain[-1], point) <= 0:
                chain.pop()
            chain.append(point)
    return lower[:-1] + upper[:-1]


def contains(polygon, point):
    if len(polygon) == 1:
        return point == polygon[0]
    if len(polygon) == 2:
        a, b = polygon
        return (cross(a, b, point) == 0 and
                all(min(a[j], b[j]) <= point[j] <= max(a[j], b[j]) for j in range(2)))
    return all(cross(a, b, point) >= 0 for a, b in zip(polygon, polygon[1:] + polygon[:1]))


def null_polygon(lo, hi, ratio, delta, epsilon):
    if not (0 <= delta < lo <= hi and 2 * hi + delta < 1 and ratio >= 1 and 0 <= epsilon < 1):
        raise ValueError("Model parameters are outside the proved range")
    points = []
    for a, d, w in product([lo, hi], [-delta, delta], product([1 / ratio, F(1)], repeat=3)):
        p = (a, a + d, 1 - 2 * a - d)
        mass = [w[j] * p[j] for j in range(3)]
        total = sum(mass)
        clean = [x / total for x in mass]
        for contaminant in range(3):
            points.append(tuple((1 - epsilon) * clean[j] + epsilon * (j == contaminant)
                                for j in range(2)))
    return hull(points)


def conditional_endpoints(lo, hi, ratio, delta, epsilon):
    a, b, c = lo, lo - delta, 1 - 2 * lo + delta
    lower_a = (1 - epsilon) * a / (a + ratio * (c + epsilon * b))
    lower_b = (1 - epsilon) * b / (b + ratio * (c + epsilon * a))
    a, b, c = hi, hi + delta, 1 - 2 * hi - delta
    upper_a = (ratio * (a + epsilon * b) + epsilon * c) / (ratio * (a + epsilon * b) + c)
    upper_b = (ratio * (b + epsilon * a) + epsilon * c) / (ratio * (b + epsilon * a) + c)
    return lower_a, upper_a, lower_b, upper_b


def minimum_contamination(lo, hi, ratio, delta, observed):
    clean = null_polygon(lo, hi, ratio, delta, F(0))
    # Edge normals of this Minkowski sum cover all nonzero mixing proportions,
    # including a degenerate clean polygon (point or line segment).
    enlarged = null_polygon(lo, hi, ratio, delta, F(1, 2))
    required = F(0)
    for a, b in zip(enlarged, enlarged[1:] + enlarged[:1]):
        normal = (b[1] - a[1], a[0] - b[0])  # Outward for CCW vertices.
        support_clean = max(sum(normal[j] * p[j] for j in range(2)) for p in clean)
        support_simplex = max(F(0), *normal)
        excess = sum(normal[j] * observed[j] for j in range(2)) - support_clean
        gap = support_simplex - support_clean
        if gap:
            required = max(required, excess / gap)
        elif excess > 0:
            raise ValueError("Observed point is outside the probability simplex")
    return required


def q_vector(category):
    out = np.zeros(9)
    out[3 + category] = out[6 + category] = 1
    return out


def lifted_constraints(lo, hi, ratio, delta, epsilon):
    # Independent formulation: x=(y0,y1,y2,cA,cB,cC,eA,eB,eC).
    # Scaled generated masses are (y1,y1+y2,y0-2y1-y2).
    rows = []
    for category, coefficients in enumerate([(0, 1, 0), (0, 1, 1), (1, -2, -1)]):
        upper = np.zeros(9)
        upper[:3] = -np.asarray(coefficients)
        upper[3 + category] = 1
        lower = np.zeros(9)
        lower[:3] = coefficients
        lower[3 + category] = -float(ratio)
        rows.extend([upper, lower])
    rows.extend([np.array([float(lo), -1, 0, 0, 0, 0, 0, 0, 0]),
                 np.array([-float(hi), 1, 0, 0, 0, 0, 0, 0, 0]),
                 np.array([-float(delta), 0, 1, 0, 0, 0, 0, 0, 0]),
                 np.array([-float(delta), 0, -1, 0, 0, 0, 0, 0, 0])])
    if epsilon is not None:
        rows.append(np.array([0, 0, 0] + [-float(epsilon)] * 3 + [1 - float(epsilon)] * 3))
    return np.array(rows)


def solve_lp(objective, constraints, equality, rhs):
    bounds = [(0, None), (0, None), (None, None)] + [(0, None)] * 6
    result = linprog(objective, A_ub=constraints, b_ub=np.zeros(len(constraints)),
                     A_eq=equality, b_eq=rhs, bounds=bounds, method="highs")
    if not result.success:
        raise RuntimeError(f"LP failed: {result.status}, {result.message}")
    residual = max(0., float(np.max(constraints @ result.x)),
                   float(np.max(np.abs(equality @ result.x - rhs))),
                   -float(np.min(result.x[[0, 1, 3, 4, 5, 6, 7, 8]])))
    if residual > 1e-9:
        raise RuntimeError(f"LP feasibility residual: {residual}")
    return float(result.fun), residual


def run_audit(protocol):
    grid = protocol["model_grid"]
    cases, max_error, max_residual, checks = [], 0., 0., 0
    total_q = sum(q_vector(j) for j in range(3))
    for band, r, d, e in product(grid["bands"], grid["relative_retention_bounds"],
                                grid["balance_errors"], grid["contamination_bounds"]):
        lo, hi = map(F, band)
        ratio, delta, epsilon = map(F, [r, d, e])
        polygon = null_polygon(lo, hi, ratio, delta, epsilon)
        endpoints = conditional_endpoints(lo, hi, ratio, delta, epsilon)
        constraints = lifted_constraints(lo, hi, ratio, delta, epsilon)
        case_error = 0.
        for category in range(2):
            hull_values = [p[category] / (p[category] + 1 - sum(p)) for p in polygon]
            assert min(hull_values) == endpoints[2 * category]
            assert max(hull_values) == endpoints[2 * category + 1]
            denominator = np.array([q_vector(category) + q_vector(2)])
            for index, sign in enumerate([1, -1]):
                value, residual = solve_lp(sign * q_vector(category), constraints, denominator, np.ones(1))
                error = abs(sign * value - float(endpoints[2 * category + index]))
                case_error, max_residual = max(case_error, error), max(max_residual, residual)
                checks += 1
        for direction in DIRECTIONS:
            exact = max(sum(F(direction[j]) * p[j] for j in range(2)) for p in polygon)
            objective = -sum(direction[j] * q_vector(j) for j in range(2))
            value, residual = solve_lp(objective, constraints, np.array([total_q]), np.ones(1))
            case_error, max_residual = max(case_error, abs(-value - float(exact))), max(max_residual, residual)
            checks += 1
        if epsilon == delta == 0:
            old_lo = lo / (lo + ratio * (1 - 2 * lo))
            old_hi = ratio * hi / (ratio * hi + 1 - 2 * hi)
            assert endpoints == (old_lo, old_hi, old_lo, old_hi)
        if case_error > 1e-9:
            raise RuntimeError(f"Continuous LP disagrees with exact geometry: {case_error}")
        max_error = max(max_error, case_error)
        cases.append({"band": band, "R": r, "delta": d, "epsilon": e,
                      "polygon": [[str(x) for x in p] for p in polygon],
                      "conditional_endpoints": list(map(str, endpoints)), "max_LP_error": case_error})

    observed = (F(5, 19), F(4, 19), F(10, 19))
    epsilon = F(20, 171)
    null_clean = (F(45, 151), F(36, 151), F(70, 151))
    contaminated = tuple((1 - epsilon) * null_clean[j] + epsilon * (j == 2) for j in range(3))
    assert contaminated == observed
    lo, hi, ratio = F(9, 32), F(11, 32), F(5, 4)
    sensitivity = []
    for delta in map(F, ["0", "1/100", "1/50", "3/100", "1/25", "1/20"]):
        exact = minimum_contamination(lo, hi, ratio, delta, observed)
        assert 0 <= exact < 1
        assert contains(null_polygon(lo, hi, ratio, delta, exact), observed[:2])
        if exact > 0:
            assert not contains(null_polygon(lo, hi, ratio, delta, exact / 2), observed[:2])
        objective = np.array([0.] * 6 + [1.] * 3)
        value, residual = solve_lp(objective, lifted_constraints(lo, hi, ratio, delta, None),
                                   np.array([q_vector(j) for j in range(3)]), np.array(list(map(float, observed))))
        error = abs(value - float(exact))
        assert error <= 1e-9
        max_error, max_residual, checks = max(max_error, error), max(max_residual, residual), checks + 1
        sensitivity.append({"delta": str(delta), "minimum_contamination": str(exact),
                            "decimal": float(exact), "LP_error": error})
    assert sensitivity[0]["minimum_contamination"] == "20/171"
    return {"cases": cases, "continuous_LP_checks": checks, "max_LP_error": max_error,
            "max_LP_feasibility_residual": max_residual,
            "same_law_witness": {"observed_law": list(map(str, observed)), "null_clean_law": list(map(str, null_clean)),
                                 "contamination": str(epsilon), "contamination_category": "C", "exact_identity": True},
            "contamination_sensitivity": sensitivity}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    protocol_path = HERE / "beam-profile-protocol.json"
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    data_path = args.cache_dir / protocol["development_input"]["name"]
    reference_path = HERE / protocol["reference_result"]["path"]
    assert digest(data_path) == protocol["development_input"]["sha256"]
    assert digest(reference_path) == protocol["reference_result"]["sha256"]
    result = {"scope": protocol["scope"], "protocol_sha256": digest(protocol_path),
              "script_sha256": digest(Path(__file__)), "derivation_sha256": digest(HERE / "beam-profile-bridge.md"),
              "versions": {"python": platform.python_version(), **{name: version(name) for name in
                           ["numpy", "scipy", "h5py", "hdf5plugin"]}}, "model_audit": run_audit(protocol)}
    with h5py.File(data_path, "r") as f:
        rows = f["MergedClusters"][()]
    from_positions = np.isfinite(rows["x_dut_3"])
    from_hits = rows["n_hits_dut_3"] > 0
    assert np.array_equal(from_positions, from_hits)
    observed_count = int(np.count_nonzero(from_positions))
    reference_count = json.loads(reference_path.read_text())["reference_rebuild"]["reference_complete_tuples"]
    lower = max(F(0), F(observed_count - reference_count, observed_count))
    result["development_cardinality"] = {
        "input_sha256": digest(data_path), "reference_result_sha256": digest(reference_path),
        "observed_DUT3_clusters": observed_count, "complete_reference_tuples": reference_count,
        "two_presence_counts_agree": True, "unmatched_fraction_lower_bound": str(lower),
        "unmatched_fraction_lower_bound_decimal": float(lower),
        "exceeds_benchmark_same_law_threshold": lower > F(20, 171),
        "interpretation": "A finite-record one-to-one matching bound for this operational feed and reference cohort. Not a physical noise rate or a calibrated superpopulation contamination probability."}
    result["claim_boundary"] = "The operational bridge and model bounds are checked, but no practical advantage or physical calibration is established. Reserved event outcomes are not read."
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"model_cases": len(result["model_audit"]["cases"]),
                      **{k: v for k, v in result["model_audit"].items() if k != "cases"},
                      "development_cardinality": result["development_cardinality"]}, indent=2))


if __name__ == "__main__":
    main()
