"""Development audit of pulse location after freeing age-dependent proportions."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

import numpy as np
from scipy.io import loadmat
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import lidar_range_screen as parent
import lidar_range_audit as audit


class Model:
    def __init__(self, n, m, pulse, width, groups):
        self.n, self.m, self.pulse, self.width = n, m, pulse, width
        self.groups = np.asarray(groups, dtype=int)
        self.rows, self.k = n.shape
        self.ng = int(self.groups.max()) + 1
        self.total = int(n.sum())
        self.phases = np.arange(self.k, dtype=float)
        self.totn, self.totm = n.sum(axis=1), m.sum(axis=1)
        assert np.all(self.totn > 0)

    def evaluate(self, x, dense=False):
        a = np.exp(x[:self.rows])
        b = np.exp(x[self.rows:2*self.rows]) * self.width
        taus = x[2*self.rows:]
        ll = 0.0
        grad = np.zeros_like(x)
        for group in range(self.ng):
            rows = np.flatnonzero(self.groups == group)
            tau = taus[group] / self.width + 0.5
            f = self.pulse.bin_mass(self.phases, tau)
            df = self.pulse.bin_mass_derivative(self.phases, tau) / self.width
            n, m = self.n[rows], self.m[rows]
            if not dense:
                support = (f > 0) | (df != 0)
                n = np.column_stack([n[:, support], self.totn[rows]-n[:, support].sum(axis=1)])
                m = np.column_stack([m[:, support], self.totm[rows]-m[:, support].sum(axis=1)])
                f, df = np.r_[f[support], 0.0], np.r_[df[support], 0.0]
            signal = a[rows, None] * f
            z = signal + b[rows, None]
            p = -np.expm1(-z)
            weight = n / p - m
            ll += float(np.sum(n*np.log(p) - (m-n)*z))
            grad[rows] = np.sum(weight*signal, axis=1)
            grad[self.rows+rows] = np.sum(weight*b[rows, None], axis=1)
            grad[2*self.rows+group] = np.sum(weight*a[rows, None]*df)
        return -ll/self.total, -grad/self.total


def fit(model, pilot, protocol, common=None):
    settings = protocol["numerics"]
    count = model.rows
    if common is None:
        base = np.r_[np.full(count, np.log(pilot[0])), np.full(count, np.log(pilot[2])), pilot[1]]
    else:
        base = np.r_[common["parameters"][:2*count], np.repeat(common["tau_ns"][0], model.ng)]
    bounds = [(-20,5)]*count + [(-25,2)]*count + [
        (pilot[1]-settings["delay_radius_ns"], pilot[1]+settings["delay_radius_ns"])]*model.ng
    solutions = []
    for offset in settings["delay_offsets_ns"]:
        x = base.copy()
        x[2*count:] += offset * (np.array([1,-1]) if model.ng == 2 else np.ones(1))
        solutions.append(minimize(model.evaluate, x, jac=True, bounds=bounds, method="L-BFGS-B",
                                  options={k: settings[k] for k in ("maxiter","ftol","gtol")}))
    best = min(solutions, key=lambda result: result.fun)
    x = best.x.copy()
    x[:count] += 0.011
    x[count:2*count] -= 0.017
    x[2*count:] += 0.000013
    analytic = model.evaluate(x)[1]
    errors = []
    for k in range(len(x)):
        h = 1e-7 if k >= 2*count else 1e-5
        d = np.zeros(len(x)); d[k] = h
        errors.append(abs((model.evaluate(x+d)[0]-model.evaluate(x-d)[0])/(2*h)-analytic[k]))
    compact = model.evaluate(best.x)
    dense = model.evaluate(best.x, dense=True)
    dense_errors = [abs(compact[0]-dense[0])*model.total, float(np.max(np.abs(compact[1]-dense[1])))]
    assert max(errors) < 5e-7
    assert dense_errors[0] < 1e-7 and dense_errors[1] < 1e-10
    result = {
        "parameters": best.x.tolist(), "a": np.exp(best.x[:count]).tolist(),
        "b_per_ns": np.exp(best.x[count:2*count]).tolist(), "tau_ns": best.x[2*count:].tolist(),
        "negative_mean_loglik": float(best.fun), "detections": model.total,
        "success": bool(best.success), "message": str(best.message), "iterations": int(best.nit),
        "normalized_score_max": float(np.max(np.abs(compact[1]))),
        "gradient_difference_max": max(errors), "dense_ll_difference": dense_errors[0],
        "dense_normalized_score_difference": dense_errors[1],
        "bound_parameter_indices": [k for k,(lo,hi) in enumerate(bounds) if min(best.x[k]-lo,hi-best.x[k]) < 1e-5],
        "starts": [{"tau_ns": r.x[2*count:].tolist(), "negative_mean_loglik": float(r.fun),
                    "success": bool(r.success), "iterations": int(r.nit)} for r in solutions]
    }
    if common is not None:
        nested = model.evaluate(base)[0]
        assert abs(nested-common["negative_mean_loglik"]) < 1e-12
        assert best.fun <= nested+1e-10
        result["nesting_difference"] = float(nested-common["negative_mean_loglik"])
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache-dir", required=True, type=Path)
    parser.add_argument("--upstream-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    path = HERE/"lidar-history-protocol.json"
    protocol = json.loads(path.read_text())
    original = json.loads((HERE/"lidar-range-protocol.json").read_text())
    parents = {}
    for name in ["lidar-range-protocol.json", "lidar_range_screen.py", "lidar_range_audit.py",
                 "lidar-range-results.json", "lidar-range-audit.json", "lidar-source-manifest.json"]:
        frozen = subprocess.check_output(["git","show",f'{protocol["parent_commit"]}:applications/detector-calibration/{name}'],cwd=HERE)
        working = (HERE/name).read_bytes()
        # This older manifest has a CRLF working copy and an LF Git blob.
        # Preserve it; all executable and result dependencies remain byte-exact.
        if name == "lidar-source-manifest.json":
            assert frozen.replace(b"\r\n",b"\n") == working.replace(b"\r\n",b"\n")
        else:
            assert frozen == working
        parents[name] = {"working_sha256": parent.sha(HERE/name),
                         "git_sha256": parent.hashlib.sha256(frozen).hexdigest()}
    for key in ["high_flux", "pulse"]:
        assert parent.sha(args.cache_dir/original[key]["path"]) == original[key]["sha256"]
    _, models, upstream_hashes = parent.source_modules(args.upstream_root, original)
    high = parent.Record(args.cache_dir/original["high_flux"]["path"], 1000000)
    calibration = loadmat(args.cache_dir/original["pulse"]["path"], variable_names=["smoothPulseShape","binRes"])
    smooth = calibration["smoothPulseShape"].ravel()
    raw_width = float(calibration["binRes"].item())*1e9
    old = json.loads((HERE/"lidar-range-results.json").read_text())
    previous_audit = json.loads((HERE/"lidar-range-audit.json").read_text())
    K = original["native_period_bins"]
    width = high.period/K
    edges = protocol["age_edges_ns"] + [np.inf]
    groups = np.array([int(a >= protocol["delay_split_ns"]) for a in edges[:-1]])
    result = {"protocol_sha256": parent.sha(path), "executable_sha256": parent.sha(__file__),
              "parent_hashes": parents, "upstream_hashes": upstream_hashes,
              "synthetic_audit": audit.synthetic_audit(), "variants": [],
              "range_benefit_demonstrated": False}
    for vi, variant in enumerate(old["variants"]):
        mass = smooth-smooth.min() if variant["pulse"] == "smooth_min_subtracted" else smooth.copy()
        pulse = models.EmpiricalPulse(mass/mass.sum(), raw_width/width, K)
        row = {"pulse": variant["pulse"], "windows": []}
        for wi, previous in enumerate(variant["high_flux"]):
            window = previous["window_frames"]
            n, m = audit.integer_cells(high, window, K, edges)
            un, um = audit.integer_cells(high, window, K, [edges[0],np.inf])
            assert np.array_equal(n.sum(axis=0),un[0]) and np.array_equal(m.sum(axis=0),um[0])
            native = previous["native_discrete"]
            pilot = [native["joint_mle_a"], native["joint_mle_tau_ns"], native["joint_mle_b_per_ns"]]
            common_model = Model(n,m,pulse,width,np.zeros(len(n),dtype=int))
            split_model = Model(n,m,pulse,width,groups)
            common = fit(common_model,pilot,protocol)
            split = fit(split_model,pilot,protocol,common)
            guard_tau = previous_audit["variants"][vi]["high_flux"][wi]["guard_205"]["tau_ns"]
            item = {"window_frames": window, "age_partition_equal": True,
                    "counts_by_age": n.sum(axis=1).tolist(), "open_slots_by_age": m.sum(axis=1).tolist(),
                    "common_delay": common, "two_delays": split,
                    "early_minus_mature_mm": (split["tau_ns"][0]-split["tau_ns"][1])*parent.C_MM_PER_NS,
                    "common_minus_native_hard_mm": (common["tau_ns"][0]-pilot[1])*parent.C_MM_PER_NS,
                    "common_minus_guard_205_mm": (common["tau_ns"][0]-guard_tau)*parent.C_MM_PER_NS,
                    "split_minus_common_loglik": (common["negative_mean_loglik"]-split["negative_mean_loglik"])*common_model.total}
            if wi == 1:
                trained = np.array(row["windows"][0]["two_delays"]["parameters"])
                item["trained_split_minus_optimized_common_loglik"] = (common["negative_mean_loglik"]-split_model.evaluate(trained)[0])*split_model.total
            row["windows"].append(item)
            print(json.dumps({"pulse": row["pulse"], "window": window,
                              "early_minus_mature_mm": item["early_minus_mature_mm"],
                              "common_minus_guard_mm": item["common_minus_guard_205_mm"],
                              "split_gain": item["split_minus_common_loglik"],
                              "forward_gain": item.get("trained_split_minus_optimized_common_loglik")}),flush=True)
        result["variants"].append(row)
    contrasts = np.array([w["early_minus_mature_mm"] for v in result["variants"] for w in v["windows"]])
    gains = [v["windows"][1]["trained_split_minus_optimized_common_loglik"] for v in result["variants"]]
    result["timing_history_lead_gate_pass"] = bool(np.all(np.abs(contrasts)>=0.2) and np.all(np.sign(contrasts)==np.sign(contrasts[0])) and min(gains)>0)
    result["limits"] = "Retrospective reused development data, working pulse template and local optimization; history contrasts do not identify physical cause or calibrate absolute range. No new accuracy or error-control claim."
    args.output.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"output":str(args.output),"sha256":parent.sha(args.output),"lead_gate":result["timing_history_lead_gate_pass"]}),flush=True)


if __name__ == "__main__":
    main()
