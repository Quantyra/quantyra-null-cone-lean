"""S049 bounded source-model screen; no Lean and no simulation of physical data."""
from __future__ import annotations

import ast
import hashlib
import json
import math
from pathlib import Path
import platform
import sys
import types

import numpy as np
import scipy
from scipy.optimize import brentq, minimize_scalar

ROOT = Path(__file__).resolve().parent
VENDOR = ROOT / "vendor" / "18662495"


def verify_inputs():
    manifest = json.loads((VENDOR / "manifest.json").read_text(encoding="utf-8-sig"))
    for item in manifest:
        raw = (VENDOR / item["file"]).read_bytes()
        assert len(raw) == item["bytes"], item["file"]
        assert hashlib.sha256(raw).hexdigest() == item["sha256"], item["file"]
        assert "md5:" + hashlib.md5(raw).hexdigest() == item["original_checksum"]
    return len(manifest)


def load_original_numerics():
    """Execute unchanged numerical AST nodes; omit plotting setup/main only.

    Matplotlib is not installed in the analysis environment. No source file is
    edited. Whitelist the inspected imports, constants, classes and functions.
    This adapter is explicitly distinct from executing the authors' plot script.
    """
    path = VENDOR / "experiment_analytical.py"
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    nodes = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
            nodes.append(node)
        elif isinstance(node, ast.ImportFrom) and node.module in {"dataclasses", "typing", "scipy.optimize"}:
            nodes.append(node)
        elif isinstance(node, ast.Import) and all(x.name == "numpy" for x in node.names):
            nodes.append(node)
        elif isinstance(node, ast.Assign) and all(isinstance(x, ast.Name) and x.id in {"RECOVERY_EXPONENT", "RECOVERY_THRESHOLD"} for x in node.targets):
            nodes.append(node)
    module = types.ModuleType("s049_original_numerics")
    sys.modules[module.__name__] = module
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(path), "exec"), module.__dict__)
    return module


def renewal_probability(q, prefix):
    """prefix is recovery at ages 1..m-1, followed by full recovery forever."""
    assert 0 <= q <= 1 and all(0 <= r <= 1 for r in prefix)
    if q == 0:
        return 0.0
    survival = 1.0
    mean_prefix = 0.0
    for r in prefix:
        mean_prefix += survival
        survival *= 1 - q*r
    return 1 / (mean_prefix + survival/q)


def stationary_probability(q, prefix):
    """Independent finite-state stationary calculation, including full tail."""
    recoveries = np.array([*prefix, 1.0])
    size = len(recoveries)
    transition = np.zeros((size, size))
    for j, r in enumerate(recoveries):
        transition[j, 0] += q*r
        transition[j, min(j+1, size-1)] += 1-q*r
    equations = transition.T - np.eye(size)
    equations[-1, :] = 1
    rhs = np.zeros(size)
    rhs[-1] = 1
    pi = np.linalg.solve(equations, rhs)
    assert np.min(pi) >= -1e-12
    assert np.max(np.abs(pi @ transition - pi)) < 1e-12
    return float(pi @ (q*recoveries))


def geometric_probability(q, prefix):
    if q == 0:
        return 0.0
    def residual(p):
        mean_r = (1-p)**len(prefix)
        mean_r += sum(r*p*(1-p)**j for j, r in enumerate(prefix))
        return p-q*mean_r
    return brentq(residual, 0, q, xtol=5e-15)


def recovery_prefix(dead_ns, reset_ns, pulse_hz, cutoff):
    prefix = []
    for j in range(1, 10000):
        t_ns = j/pulse_hz*1e9
        if t_ns <= dead_ns:
            r = 0.0
        elif reset_ns == 0:
            r = 1.0
        else:
            r = -math.expm1(math.log(0.05)*((t_ns-dead_ns)/reset_ns)**4)
        if r >= cutoff:
            return prefix
        prefix.append(r)
    raise AssertionError("Recovery tail not reached")


def synthetic_check(protocol):
    rows = []
    worst_matrix_gap = 0.0
    for q in protocol["synthetic"]["q"]:
        for d in protocol["synthetic"]["blind_pulses"]:
            p = renewal_probability(q, [0]*d)
            matrix_p = stationary_probability(q, [0]*d)
            assert abs(p-q/(1+d*q)) < 1e-12
            worst_matrix_gap = max(worst_matrix_gap, abs(matrix_p-p))
            gp = geometric_probability(q, [0]*d)
            rows.append({"q": q, "blind_pulses": d, "renewal_p": p,
                         "matrix_p": matrix_p, "geometric_p": gp,
                         "geometric_relative_count_bias": gp/p-1})
        for prefix in protocol["synthetic"]["recovery_prefixes"]:
            p = renewal_probability(q, prefix)
            matrix_p = stationary_probability(q, prefix)
            worst_matrix_gap = max(worst_matrix_gap, abs(matrix_p-p))
    assert worst_matrix_gap < protocol["synthetic"]["arithmetic_check_tolerance"]
    case = protocol["synthetic"]["decision_counterexample"]
    p = renewal_probability(case["q"], [0]*case["blind_pulses"])
    geometric_inverse = p/(1-p)**case["blind_pulses"]
    renewal_inverse = p/(1-case["blind_pulses"]*p)
    return {"hard_dead_time_rows": rows, "soft_recovery_checks": 24,
            "max_stationary_disagreement": worst_matrix_gap,
            "decision_example": {**case, "observed_p": p,
                "geometric_inverse_q": geometric_inverse,
                "renewal_inverse_q": renewal_inverse,
                "geometric_below_threshold": geometric_inverse < case["threshold_q"],
                "renewal_below_threshold": renewal_inverse < case["threshold_q"]}}


def physical_check(protocol, original):
    recovery = protocol["recovery"]
    dead, reset, f = recovery["dead_ns"], recovery["reset95_ns"], recovery["pulse_hz"]
    coarse, fine = [recovery_prefix(dead, reset, f, c) for c in recovery["cutoffs"]]
    params = original.Data(tau_dead=dead*1e-9, tau_rst=reset*1e-9, f=f, eta=0.89)
    assert abs(original.sigmoid_recovery((dead+reset)*1e-9, params)-0.95) < 1e-12
    original_checks = []
    for b in protocol["synthetic"]["q"]:
        old = b*original.get_qeff_sps(b*f, params)
        copied = geometric_probability(b*params.eta, coarse)
        assert abs(old-copied) < 1e-10
        original_checks.append(abs(old-copied))
    raw = np.loadtxt(VENDOR / "snspd1.txt", delimiter=",", skiprows=1)
    data = raw[np.argsort(raw[:, 0])]
    counts, efficiency, sigma = data.T
    flux = counts/efficiency
    assert np.all(np.diff(flux) > 0)
    ntrain = len(data)//2
    train = slice(0, ntrain)
    test = slice(ntrain, None)
    methods = {
        "published_geometric_cutoff_0999": (geometric_probability, coarse),
        "geometric_converged": (geometric_probability, fine),
        "established_renewal": (renewal_probability, fine),
        "independent_stationary_renewal": (stationary_probability, fine),
        "hard_dead_time_renewal": (renewal_probability, [0]*int(dead*1e-9*f)),
    }
    reports = []
    for scale in protocol["physical_check"]["common_flux_scale_sensitivity"]:
        reference_flux = flux*scale
        observed_efficiency = counts/reference_flux
        observed_sigma = sigma/scale
        for name, (probability, prefix) in methods.items():
            def efficiencies(eta):
                return np.array([f*probability(eta*x/f, prefix)/x for x in reference_flux])
            def objective(eta):
                residual = (efficiencies(eta)[train]-observed_efficiency[train])/observed_sigma[train]
                return float(residual @ residual)
            fit = minimize_scalar(objective, bounds=protocol["physical_check"]["eta0_bounds"],
                                  method="bounded", options={"xatol": 1e-13})
            assert fit.success
            predicted = efficiencies(fit.x)
            inferred = np.array([brentq(lambda q: f*probability(q, prefix)-c,
                                       0, 1, xtol=5e-15)*f/fit.x for c in counts])
            err = inferred/reference_flux-1
            residual = predicted-observed_efficiency
            reports.append({"method": name, "common_flux_scale": scale,
                            "fitted_eta0": float(fit.x),
                            "test_efficiency_rmse": float(np.sqrt(np.mean(residual[test]**2))),
                            "test_flux_relative_rmse": float(np.sqrt(np.mean(err[test]**2))),
                            "test_flux_max_abs_relative_error": float(np.max(np.abs(err[test]))),
                            "test_max_abs_residual_over_supplied_sigma": float(np.max(np.abs(residual[test]/observed_sigma[test]))),
                            "rows": [{"split": "train" if i<ntrain else "test",
                                      "count_hz": float(c), "reference_flux_hz": float(x),
                                      "observed_efficiency": float(y), "supplied_sigma": float(s),
                                      "predicted_efficiency": float(yp), "inferred_flux_hz": float(xp),
                                      "relative_flux_error": float(e)}
                                     for i, (c,x,y,s,yp,xp,e) in enumerate(zip(counts, reference_flux, observed_efficiency,
                                                                              observed_sigma, predicted, inferred, err))]})
    return {"observations": len(data), "training_rows": ntrain, "withheld_rows": len(data)-ntrain,
            "coarse_recovery_prefix": coarse, "converged_recovery_prefix": fine,
            "original_code_max_probability_disagreement": max(original_checks),
            "reports": reports,
            "warning": "Retrospective descriptive predictions, not confidence or independent physical validation."}


def main():
    protocol_bytes = (ROOT / "protocol.json").read_bytes()
    protocol = json.loads(protocol_bytes)
    result = {"protocol_sha256": hashlib.sha256(protocol_bytes).hexdigest(),
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "environment": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__},
              "verified_original_files": verify_inputs(),
              "synthetic": synthetic_check(protocol),
              "physical": physical_check(protocol, load_original_numerics()),
              "practical_goal_complete": False}
    output = ROOT / "results.json"
    output.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf-8")
    print(json.dumps({"output": str(output), "verified_files": result["verified_original_files"],
                      "max_matrix_disagreement": result["synthetic"]["max_stationary_disagreement"],
                      "physical_rows": result["physical"]["observations"],
                      "nominal_reports": [{k:v for k,v in row.items() if k != "rows"}
                                          for row in result["physical"]["reports"] if row["common_flux_scale"] == 1]}, indent=2))


if __name__ == "__main__":
    main()
