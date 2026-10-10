"""Independent count/score and source-coordinate audit of the frozen screen."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

import numpy as np
from scipy.io import loadmat

HERE = Path(__file__).resolve().parent
FREEZE = "4f70f9299bc3bdf5fb1fddecc36609d3a555e666"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def recount(ages, phases, times, window, age_edges, phase_edges):
    rows = np.searchsorted(age_edges, ages, side="right") - 1
    cols = np.searchsorted(phase_edges, phases, side="right") - 1
    keep = ((times >= window[0]) & (times < window[1]) & (rows >= 0)
            & (rows < len(age_edges)-1) & (cols >= 0) & (cols < len(phase_edges)-1))
    out = np.zeros((len(age_edges)-1, len(phase_edges)-1), dtype=np.int64)
    np.add.at(out, (rows[keep], cols[keep]), 1)
    return out, ages[keep]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache-dir", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    result_path = HERE / "lidar-recovery-results.json"
    result = json.loads(result_path.read_text())
    protocol = json.loads((HERE / "lidar-recovery-protocol.json").read_text())
    frozen = {}
    for name, key in [("lidar-recovery-protocol.json", "protocol_sha256"),
                      ("lidar_recovery_screen.py", "executable_sha256"),
                      ("lidar-recovery-argument.md", "argument_sha256")]:
        payload = subprocess.check_output(["git", "show", f"{FREEZE}:applications/detector-calibration/{name}"], cwd=HERE)
        frozen[name] = hashlib.sha256(payload).hexdigest()
        assert frozen[name] == digest(HERE / name) == result[key]
    source = args.cache_dir / protocol["input"]["relative_path"]
    assert digest(source) == result["source_sha256"] == protocol["input"]["sha256"]
    data = loadmat(source, variable_names=["frameNum", "detTime"])
    all_frames = data["frameNum"].ravel()
    keep = (all_frames >= 0) & (all_frames < 1000000)
    frame, phase = all_frames[keep], data["detTime"].ravel()[keep]
    period = result["period_ns"]
    age_edges = np.array(protocol["age_edges_ns"])
    phase_edges = np.array(protocol["phase_edges_ns"])
    spec = importlib.util.spec_from_file_location("screen", HERE / "lidar_recovery_screen.py")
    screen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(screen)
    rows = []
    for scenario in result["scenarios"]:
        shift = scenario["alternating_timestamp_perturbation_ns"] * np.where(np.arange(len(frame)) % 2 == 0, 1, -1)
        times = frame * period + phase + shift
        absolute_age, absolute_phase = np.diff(times), np.remainder(times[1:], period)
        stable_age = np.diff(frame) * period + np.diff(phase + shift)
        stable_phase = np.remainder(phase[1:] + shift[1:], period)
        originals, stable = [], []
        for key, field in [("train_frames", "training_counts"), ("evaluation_frames", "evaluation_counts")]:
            window = np.array(protocol[key]) * period
            orig, _ = recount(absolute_age, absolute_phase, times[1:], window, age_edges, phase_edges)
            fixed, ages = recount(stable_age, stable_phase, times[1:], window, age_edges, phase_edges)
            assert np.array_equal(orig, scenario[field])
            originals.append(orig)
            stable.append((fixed, ages))
        n0, n1 = originals
        e0, e1 = (np.array(scenario[k]) for k in ["training_exposure_ns", "evaluation_exposure_ns"])
        alt_rates = (n0 + 0.5) / (e0 + 0.5 / 0.015)
        # Scalar loop evaluates the score independently from the array implementation.
        alt_score = sum(int(n) * np.log(float(r)) - float(e) * float(r)
                        for n, e, r in zip(n1.flat, e1.flat, alt_rates.flat))
        assert abs(alt_score - scenario["alternative_evaluation_log_score"]) < 1e-8
        # Additional numeric sensitivity: preserve original within-frame phases and
        # compute gaps using frame differences. This changes exact-boundary labels
        # that absolute floating-point addition/modulo can place on either side.
        s0, s1 = stable[0][0], stable[1][0]
        rates = (s0 + 0.5) / (e0 + 0.5 / 0.015)
        d = min(float(stable[1][1].min()), protocol["hard_cutoff_interval_ns"][1])
        null_e = screen.exposure(times, np.array(protocol["evaluation_frames"]) * period,
                                 np.array([d, age_edges[-1]]), phase_edges, period)[0]
        null_n = s1.sum(axis=0)
        stable_score = float(np.sum(s1 * np.log(rates) - e1 * rates)
                             - np.sum(null_n * (np.log(null_n / null_e) - 1)))
        rows.append({"perturbation_ns": scenario["alternating_timestamp_perturbation_ns"],
                     "independent_counts_match": True, "score_error": float(alt_score - scenario["alternative_evaluation_log_score"]),
                     "source_coordinate_count_l1_changes": [int(np.abs(o-s[0]).sum()) for o,s in zip(originals,stable)],
                     "source_coordinate_log_score_advantage": stable_score,
                     "source_coordinate_gate_pass": bool(stable_score > np.log(100)),
                     "maximum_gap_coordinate_difference_ns": float(np.max(np.abs(absolute_age-stable_age))),
                     "maximum_phase_coordinate_difference_ns": float(np.max(np.abs(absolute_phase-stable_phase))),
                     "maximum_circular_phase_coordinate_difference_ns": float(np.max(np.abs(
                         np.remainder(absolute_phase-stable_phase+period/2, period)-period/2)))})
    out = {"freeze": FREEZE, "frozen_hashes": frozen, "result_sha256": digest(result_path),
           "audit_executable_sha256": digest(__file__), "source_sha256": digest(source), "scenarios": rows,
           "interpretation": "Frozen screen counts/scores reproduce. Source-coordinate counts expose floating-point boundary sensitivity, retained here without overwriting the original. Recomputed scores are an additional numeric sensitivity using the original exposure arrays; they do not bound all physical timestamp rounding. Prior full-prefix gap summaries motivated this retrospective protocol, so even under exact timestamps these scores are not a prospectively calibrated 1% test. The frozen argument's conditional theorem assumes a fixed protocol or appropriate selection adjustment. No reserved outcomes read."}
    args.output.write_text(json.dumps(out, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
