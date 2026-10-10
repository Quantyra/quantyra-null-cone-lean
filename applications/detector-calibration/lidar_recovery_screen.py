"""Development-only event-age check; see the frozen protocol and argument.

No upstream code is executed. Exact continuous-time model scores are not
reported as calibrated physical p-values for quantized timestamps.
"""

import argparse
import hashlib
import json
from pathlib import Path
import platform

import numpy as np
import scipy
from scipy.io import loadmat

HERE = Path(__file__).resolve().parent


def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def phase_primitive(time, period, left, right):
    cycles = np.floor(time / period)
    return cycles * (right - left) + np.clip(time - cycles * period - left, 0, right - left)


def phase_length(left, right, period, pleft, pright):
    # Translate each interval by a whole number of periods to reduce cancellation.
    shift = np.floor(left / period) * period
    return (phase_primitive(right - shift, period, pleft, pright)
            - phase_primitive(left - shift, period, pleft, pright))


def exposure(times, window, age_edges, phase_edges, period):
    starts = times
    stops = np.r_[times[1:], window[1]]
    out = np.zeros((len(age_edges) - 1, len(phase_edges) - 1))
    for j, (a, b) in enumerate(zip(age_edges[:-1], age_edges[1:])):
        lo = np.maximum(starts + a, window[0])
        hi = np.minimum(np.minimum(starts + b, stops), window[1])
        keep = hi > lo
        lo, hi = lo[keep], hi[keep]
        for k, (p, q) in enumerate(zip(phase_edges[:-1], phase_edges[1:])):
            out[j, k] = phase_length(lo, hi, period, p, q).sum()
    return out


def counts(times, window, age_edges, phase_edges, period):
    gaps = np.diff(times)
    phase = np.remainder(times[1:], period)
    select = ((times[1:] >= window[0]) & (times[1:] < window[1])
              & (gaps >= age_edges[0]) & (gaps < age_edges[-1])
              & (phase >= phase_edges[0]) & (phase < phase_edges[-1]))
    # Explicit half-open range mask excludes numpy.histogram2d's closed last edge.
    matrix = np.histogram2d(gaps[select], phase[select], bins=[age_edges, phase_edges])[0].astype(np.int64)
    assert int(matrix.sum()) == int(select.sum())
    return matrix, gaps[select]


def log_score(n, e, intensity):
    return float(np.sum(n * np.log(intensity) - e * intensity))


def direct_phase_length(left, right, period, pleft, pright):
    """Independent explicit intersection of absolute periodic intervals."""
    total = 0.0
    for cycle in range(int(np.floor(left / period)) - 1, int(np.floor(right / period)) + 2):
        total += max(0.0, min(right, cycle * period + pright) - max(left, cycle * period + pleft))
    return total


def audit_geometry(times, period, age_edges, phase_edges, windows):
    rng = np.random.default_rng(490198)
    max_error = 0.0
    cases = 0
    # Random translated intervals include wraparound and multiple whole periods.
    for _ in range(300):
        left = rng.uniform(-3 * period, 1e8)
        right = left + rng.uniform(0, 8 * period)
        k = int(rng.integers(len(phase_edges) - 1))
        p, q = phase_edges[k:k+2]
        fast = float(phase_length(np.array([left]), np.array([right]), period, p, q)[0])
        slow = direct_phase_length(left, right, period, p, q)
        max_error = max(max_error, abs(fast - slow))
        cases += 1
    # Actual record intervals, including analysis-boundary censoring.
    ids = np.unique(np.r_[0, len(times) - 1, rng.integers(0, len(times), size=100)])
    for idx in ids:
        stop = times[idx + 1] if idx + 1 < len(times) else windows[-1][1]
        for window in windows:
            for a, b in zip(age_edges[:-1], age_edges[1:]):
                lo = max(times[idx] + a, window[0])
                hi = min(times[idx] + b, stop, window[1])
                if hi <= lo:
                    continue
                for p, q in zip(phase_edges[:-1], phase_edges[1:]):
                    fast = float(phase_length(np.array([lo]), np.array([hi]), period, p, q)[0])
                    max_error = max(max_error, abs(fast - direct_phase_length(lo, hi, period, p, q)))
                    cases += 1
    assert max_error < 1e-6
    partitions = []
    for window in windows:
        fine = exposure(times, window, age_edges, phase_edges, period)
        united = exposure(times, window, age_edges, phase_edges[[0, -1]], period)
        error = float(np.max(np.abs(fine.sum(axis=1) - united[:, 0])))
        assert error < 1e-5
        partitions.append(error)
    return {"independent_interval_cases": cases, "maximum_absolute_error_ns": max_error,
            "phase_partition_errors_ns": partitions}


def run_scenario(times, period, protocol, perturbation):
    # The same deterministic timestamp transformation is applied to both halves.
    times = times + perturbation * np.where(np.arange(len(times)) % 2 == 0, 1, -1)
    assert np.all(np.diff(times) > 0)
    ages = np.asarray(protocol["age_edges_ns"], dtype=float)
    phases = np.asarray(protocol["phase_edges_ns"], dtype=float)
    windows = [np.asarray(protocol[key], dtype=float) * period for key in ["train_frames", "evaluation_frames"]]
    matrices = [counts(times, w, ages, phases, period) for w in windows]
    exposures = [exposure(times, w, ages, phases, period) for w in windows]
    n0, n1 = [v[0] for v in matrices]
    e0, e1 = exposures
    pseudo = protocol["alternative_pseudocount"]
    rate = (n0 + pseudo) / (e0 + pseudo / protocol["alternative_prior_rate_per_ns"])
    alternative_score = log_score(n1, e1, rate)
    minimum = float(matrices[1][1].min())
    lower, upper = protocol["hard_cutoff_interval_ns"]
    if minimum < lower:
        raise ValueError("Hard null has no support at its minimum permitted cutoff")
    cutoff = min(minimum, upper)
    null_exposure = exposure(times, windows[1], np.array([cutoff, ages[-1]]), phases, period)[0]
    null_counts = n1.sum(axis=0)
    null_rates = null_counts / null_exposure
    null_score = log_score(null_counts, null_exposure, null_rates)
    # Check the analytic global maximum against a deterministic grid and endpoints.
    lower_scores = []
    for d in np.unique(np.r_[np.linspace(lower, cutoff, 9), cutoff]):
        ed = exposure(times, windows[1], np.array([d, ages[-1]]), phases, period)[0]
        lower_scores.append(log_score(null_counts, ed, null_counts / ed))
    assert np.max(lower_scores) <= null_score + 1e-7
    assert np.all(np.diff(lower_scores) >= -1e-7)
    diagnostic = []
    for j, (a, b) in enumerate(zip(ages[:-1], ages[1:])):
        diagnostic.append({"age_ns": [a, b], "train_count": int(n0[j].sum()),
                           "evaluation_count": int(n1[j].sum()),
                           "train_rate_per_ns": float(n0[j].sum() / e0[j].sum()),
                           "evaluation_rate_per_ns": float(n1[j].sum() / e1[j].sum())})
    return {"alternating_timestamp_perturbation_ns": perturbation,
            "training_counts": n0.tolist(), "evaluation_counts": n1.tolist(),
            "training_exposure_ns": e0.tolist(), "evaluation_exposure_ns": e1.tolist(),
            "trained_intensity_per_ns": rate.tolist(), "null_cutoff_supremum_ns": cutoff,
            "null_evaluation_rate_per_ns": null_rates.tolist(),
            "alternative_evaluation_log_score": alternative_score,
            "optimized_null_evaluation_log_score": null_score,
            "log_score_advantage": alternative_score - null_score,
            "diagnostic_gate_pass": bool(alternative_score - null_score > np.log(100)),
            "null_grid_log_scores": lower_scores,
            "age_rate_summaries": diagnostic}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError("Preserve the existing result; select a new output path")
    protocol_path = HERE / "lidar-recovery-protocol.json"
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    source = args.cache_dir / protocol["input"]["relative_path"]
    assert sha(source) == protocol["input"]["sha256"]
    data = loadmat(source, variable_names=["frameNum", "detTime", "tr", "binRes"])
    frame = np.asarray(data["frameNum"]).reshape(-1)
    selected = (frame >= 0) & (frame < protocol["evaluation_frames"][1])
    phase = np.asarray(data["detTime"]).reshape(-1)[selected]
    frame = frame[selected]
    # No phase or response outcome beyond the selected frame prefix is used.
    period = float(np.asarray(data["tr"]).item()) * 1e9
    times = frame * period + phase
    assert np.all(np.diff(times) > 0)
    gap_error = float(np.max(np.abs(np.diff(times) - (np.diff(frame) * period + np.diff(phase)))))
    assert gap_error < 1e-5
    windows = [np.asarray(protocol[key], dtype=float) * period for key in ["train_frames", "evaluation_frames"]]
    audit = audit_geometry(times, period, np.array(protocol["age_edges_ns"]), np.array(protocol["phase_edges_ns"]), windows)
    scenarios = [run_scenario(times, period, protocol, v) for v in protocol["timestamp_perturbation_ns"]]
    result = {"story": "S049", "protocol_sha256": sha(protocol_path),
              "executable_sha256": sha(__file__),
              "argument_sha256": sha(HERE / protocol["ordinary_argument"]),
              "source_sha256": sha(source),
              "versions": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__},
              "period_ns": period, "development_detections": int(len(times)),
              "raw_phase_outside_period_preserved": int(np.sum((phase < 0) | (phase >= period))),
              "maximum_gap_formula_disagreement_ns": gap_error,
              "geometry_audit": audit, "scenarios": scenarios,
              "all_diagnostic_gates_pass": all(s["diagnostic_gate_pass"] for s in scenarios),
              "boundary": "Development diagnostic only. No ranging comparison, physical confidence certificate, causal recovery diagnosis or final withheld validation. Timestamp perturbations are not exhaustive uncertainty bounds."}
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output), "sha256": sha(args.output), "geometry_audit": audit,
                      "log_score_advantages": [s["log_score_advantage"] for s in scenarios],
                      "all_diagnostic_gates_pass": result["all_diagnostic_gates_pass"]}))


if __name__ == "__main__":
    main()
