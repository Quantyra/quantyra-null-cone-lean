"""Categorical specialization of Tudball et al.; asymptotic reference only."""
from pathlib import Path
import hashlib
import importlib.util
import json
import platform
import time

import numpy as np
import scipy
from scipy.stats import beta, norm

HERE = Path(__file__).resolve().parent


def sibling(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def ratio_interval(p, n, ratio, constraint_failure):
    """Global feasible a/b interval; positive proportions required."""
    x, y, _ = np.asarray(p, dtype=float).T
    critical = norm.isf(constraint_failure / 2)
    k = critical**2 / (np.asarray(n) + critical**2)
    root = np.sqrt(np.maximum(0, k*x*y*(x+y-k)))
    lower = np.zeros_like(x)
    upper = np.full_like(x, np.inf)
    np.divide(y*(y-k), x*y+root, out=lower, where=y>k)
    np.divide(x*y+root, x*(x-k), out=upper, where=x>k)
    lower = np.maximum(lower, 1/ratio)
    upper = np.minimum(upper, ratio)
    return lower, upper, lower > upper


def optimizer_weights(lower, upper, ratio, target, maximum):
    if target == "past":
        r = upper if maximum else lower
    elif target == "future":
        r = lower if maximum else upper
    elif target == "pooled":
        r = np.maximum(lower, np.minimum(1., upper))
    else:
        raise ValueError(target)
    b = np.minimum(ratio, ratio/r) if maximum else np.maximum(1., 1/r)
    c = np.ones_like(r) * (1 if maximum else ratio)
    return np.column_stack((r*b, b, c))


def objective_variance(p, weights, f):
    denominator = np.sum(p*weights, axis=1)
    q = np.sum(p*weights*f, axis=1) / denominator
    variance = np.sum(p*weights**2*(f-q[:, None])**2, axis=1) / denominator**2
    return q, variance


def intervals(counts, ratio, constraint_failure, objective_tail, target):
    counts = np.asarray(counts, dtype=float)
    n = counts.sum(axis=1)
    guard = (n < 2) | np.any(counts <= 0, axis=1)
    # Safe placeholders are never used to make guarded decisions.
    p = np.where(guard[:, None], 1., counts)
    p /= p.sum(axis=1)[:, None]
    lower, upper, empty = ratio_interval(p, np.maximum(n, 2), ratio, constraint_failure)
    lower = np.where(empty, 1., lower)
    upper = np.where(empty, 1., upper)
    f = {"past": np.array([1., 0., 0.]), "future": np.array([0., 1., 0.]),
         "pooled": np.array([.5, .5, 0.])}[target]
    endpoints = []
    for maximum in (False, True):
        weights = optimizer_weights(lower, upper, ratio, target, maximum)
        q, var = objective_variance(p, weights, f)
        sign = 1 if maximum else -1
        endpoints.append(q + sign*norm.isf(objective_tail)*np.sqrt(var/np.maximum(n, 2)))
    ci_lower = np.maximum(1/8, endpoints[0])
    ci_upper = np.minimum(3/8, endpoints[1])
    ci_lower = np.where(empty | guard, 1/8, ci_lower)
    ci_upper = np.where(empty | guard, 3/8, ci_upper)
    return ci_lower, ci_upper, empty & ~guard, guard


def flags(counts, ratio, nominal, tolerance, allocation, target):
    lo, hi, empty, guard = intervals(counts, ratio, **allocation, target=target)
    # Tiny numerical margin favors unresolved, rather than accidental flags.
    reject = (hi < nominal-tolerance-1e-12) | (lo > nominal+tolerance+1e-12)
    return reject, reject | empty, empty, guard


def main():
    start = time.perf_counter()
    protocol_bytes = (HERE/"auxiliary-protocol.json").read_bytes()
    protocol = json.loads(protocol_bytes)
    result_bytes = (HERE/"results.json").read_bytes()
    assert hashlib.sha256(result_bytes).hexdigest() == protocol["input_results_sha256"]
    old = json.loads(result_bytes)
    assert hashlib.sha256((HERE/"counts.npz").read_bytes()).hexdigest() == old["counts_sha256"]
    data = np.load(HERE/"counts.npz", allow_pickle=False)
    pilot = sibling("pilot")
    old_protocol = json.loads((HERE/"protocol.json").read_text(encoding="utf-8"))
    families = len(old["rows"]) * len(protocol["allocations"]) * len(protocol["target_representations"]) * 2
    rows = []
    for old_row in old["rows"]:
        counts = data[old_row["sample_key"]]
        rep = len(counts)
        candidate = pilot.decisions(counts, old_row["R"], old_row["nominal"],
                                    old_protocol["tolerance"], old_protocol["false_flag_budget"])["balanced_conditional"]
        allowance = np.sqrt(2*np.log(families/.01)/rep)
        comparison = {}
        for label, allocation in protocol["allocations"].items():
            for target in protocol["target_representations"]:
                regular, flag_empty, empty, guard = flags(counts, old_row["R"], old_row["nominal"],
                                                         old_protocol["tolerance"], allocation, target)
                gains = {}
                for convention, decisions in (("unresolved_on_empty", regular), ("flag_on_empty", flag_empty)):
                    gains[convention] = {
                        "flag_probability_mc": float(np.mean(decisions)),
                        "candidate_paired_gain_mc": float(np.mean(candidate.astype(int)-decisions.astype(int))),
                        "family_adjusted_gain_lower": float(np.mean(candidate.astype(int)-decisions.astype(int))-allowance)}
                comparison[label+"/"+target] = {"conventions": gains, "empty_probability_mc": float(empty.mean()),
                                               "guard_count": int(guard.sum())}
        minimum_gain = min(v["family_adjusted_gain_lower"] for c in comparison.values() for v in c["conventions"].values())
        successes = int(candidate.sum())
        power_lower = float(beta.ppf(.01, successes, rep-successes+1)) if successes else 0.
        old_gains_pass = min(old_row["family_adjusted_paired_gain_lower"].values()) >= .1
        gate = bool(not old_row["truth_inside_band"] and old_row["R"]>1 and power_lower>=.8 and minimum_gain>=.1 and old_gains_pass)
        rows.append({k: old_row[k] for k in ("sample_key", "v", "R", "detector", "n", "nominal", "truth_inside_band")} |
                    {"candidate_probability_mc": float(candidate.mean()), "candidate_power_lower99": power_lower,
                     "comparators": comparison, "minimum_adjusted_gain": minimum_gain,
                     "passes_secondary_gate": gate})
    result = {"protocol_sha256": hashlib.sha256(protocol_bytes).hexdigest(),
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "original_results_sha256": hashlib.sha256(result_bytes).hexdigest(),
              "counts_sha256": old["counts_sha256"],
              "environment": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__},
              "comparison_family_size": families, "rows": rows,
              "secondary_gate_passes": sum(row["passes_secondary_gate"] for row in rows),
              "strongest_finite_comparison_complete": False, "physical_validation_complete": False,
              "seconds": time.perf_counter()-start}
    (HERE/"auxiliary-results.json").write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf-8", newline="\n")
    null = [row for row in rows if row["truth_inside_band"]]
    print(json.dumps({"rows": len(rows), "gate_passes": result["secondary_gate_passes"],
                      "passing": [{k: row[k] for k in ("sample_key", "R", "n", "detector", "minimum_adjusted_gain")} for row in rows if row["passes_secondary_gate"]],
                      "max_null_flag_mc": max(v["flag_probability_mc"] for row in null for c in row["comparators"].values() for v in c["conventions"].values()),
                      "total_guards": sum(c["guard_count"] for row in rows for c in row["comparators"].values()),
                      "seconds": result["seconds"]}, indent=2))


if __name__ == "__main__":
    main()
