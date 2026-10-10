"""Independently evaluate new fits with the pinned upstream row likelihood."""

import argparse
import json
from pathlib import Path
import sys

import numpy as np
from scipy.io import loadmat

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import lidar_range_screen as parent
import lidar_range_audit as exposure
import lidar_history_screen as candidate


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache-dir", type=Path, required=True)
    parser.add_argument("--upstream-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    protocol = json.loads((HERE/"lidar-history-protocol.json").read_text())
    original = json.loads((HERE/"lidar-range-protocol.json").read_text())
    result = json.loads((HERE/"lidar-history-results.json").read_text())
    assert result["protocol_sha256"] == parent.sha(HERE/"lidar-history-protocol.json")
    assert result["executable_sha256"] == parent.sha(HERE/"lidar_history_screen.py")
    for key in ("high_flux","pulse"):
        assert parent.sha(args.cache_dir/original[key]["path"]) == original[key]["sha256"]
    upstream, models, _ = parent.source_modules(args.upstream_root, original)
    high = parent.Record(args.cache_dir/original["high_flux"]["path"], 1000000)
    calibration = loadmat(args.cache_dir/original["pulse"]["path"], variable_names=["smoothPulseShape","binRes"])
    smooth = calibration["smoothPulseShape"].ravel()
    raw_width = float(calibration["binRes"].item())*1e9
    K = original["native_period_bins"]
    width = high.period/K
    edges = protocol["age_edges_ns"]+[np.inf]
    phases = np.arange(K,dtype=float)
    records = []
    for variant in result["variants"]:
        mass = smooth-smooth.min() if variant["pulse"] == "smooth_min_subtracted" else smooth.copy()
        pulse = models.EmpiricalPulse(mass/mass.sum(), raw_width/width, K)
        for window in variant["windows"]:
            n,m = exposure.integer_cells(high,window["window_frames"],K,edges)
            for name in ("common_delay","two_delays"):
                fit = window[name]
                groups = np.array([int(a>=205) if name=="two_delays" else 0 for a in edges[:-1]])
                model = candidate.Model(n,m,pulse,width,groups)
                x = np.array(fit["parameters"])
                total_ll = 0.0
                score = np.zeros(len(x))
                for j in range(len(n)):
                    group = groups[j]
                    theta = np.array([fit["a"][j], fit["tau_ns"][group]/width+.5, fit["b_per_ns"][j]*width])
                    ll, row_score = upstream.loglik_and_score(n[j],m[j],theta,phases,K,1.0,1.0,5,pulse)
                    total_ll += ll
                    score[j] = row_score[0]*theta[0]
                    score[len(n)+j] = row_score[2]*theta[2]
                    score[2*len(n)+group] += row_score[1]/width
                value, grad = model.evaluate(x)
                ll_error = abs(total_ll+value*model.total)
                score_error = float(np.max(np.abs(score/model.total+grad)))
                assert ll_error < 1e-7 and score_error < 1e-10
                records.append({"pulse":variant["pulse"],"window":window["window_frames"],"model":name,
                                "upstream_loglik_difference":float(ll_error),"upstream_normalized_score_difference":score_error})
    report = {"result_sha256":parent.sha(HERE/"lidar-history-results.json"),
              "audit_executable_sha256":parent.sha(__file__),"upstream_row_likelihood_checks":records,
              "status":"pass","physical_accuracy_validated":False}
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"status":"pass","fits":len(records),"max_loglik_difference":max(r["upstream_loglik_difference"] for r in records),
                      "max_score_difference":max(r["upstream_normalized_score_difference"] for r in records),"sha256":parent.sha(args.output)}))


if __name__ == "__main__":
    main()
