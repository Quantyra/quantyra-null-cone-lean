"""Independent provenance, arithmetic and saved-prediction audit for S049."""
import hashlib
import json
import math
from pathlib import Path
import subprocess

import numpy as np

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
PREFIX = "applications/detector-calibration/"
FREEZE = "59dd082"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    results_raw = (ROOT / "results.json").read_bytes()
    result = json.loads(results_raw)
    protocol_raw = (ROOT / "protocol.json").read_bytes()
    frozen_protocol = subprocess.check_output(["git", "show", FREEZE+":"+PREFIX+"protocol.json"], cwd=REPO)
    assert protocol_raw == frozen_protocol
    assert result["protocol_sha256"] == sha(protocol_raw)
    assert result["script_sha256"] == sha((ROOT / "screen.py").read_bytes())
    manifest = json.loads((ROOT / "vendor/18662495/manifest.json").read_text(encoding="utf-8-sig"))
    for item in manifest:
        local = (ROOT / "vendor/18662495" / item["file"]).read_bytes()
        committed = subprocess.check_output(["git", "show", FREEZE+":"+PREFIX+"vendor/18662495/"+item["file"]], cwd=REPO)
        assert sha(local) == sha(committed) == item["sha256"], item["file"]
    case = result["synthetic"]["decision_example"]
    assert abs(case["observed_p"]-1/4) < 1e-15
    assert abs(case["geometric_inverse_q"]-4/9) < 1e-15
    assert case["geometric_below_threshold"] is True
    assert case["renewal_below_threshold"] is False
    for row in result["synthetic"]["hard_dead_time_rows"]:
        q, d = row["q"], row["blind_pulses"]
        assert abs(row["renewal_p"]-q/(1+d*q)) < 1e-12
        p = row["geometric_p"]
        assert abs(p-q*(1-p)**d) < 1e-12
    physical = result["physical"]
    assert physical["observations"] == 8 and physical["training_rows"] == physical["withheld_rows"] == 4
    raw = np.loadtxt(ROOT / "vendor/18662495/snspd1.txt", delimiter=",", skiprows=1)
    raw = raw[np.argsort(raw[:, 0])]
    for report in physical["reports"]:
        residuals, errors = [], []
        for i, row in enumerate(report["rows"]):
            assert row["split"] == ("train" if i < 4 else "test")
            assert row["count_hz"] == raw[i, 0]
            expected_flux = raw[i, 0]/raw[i, 1]*report["common_flux_scale"]
            assert math.isclose(row["reference_flux_hz"], expected_flux, rel_tol=1e-14)
            err = row["inferred_flux_hz"]/row["reference_flux_hz"]-1
            assert abs(err-row["relative_flux_error"]) < 1e-14
            if i >= 4:
                errors.append(err)
                residuals.append(row["predicted_efficiency"]-row["observed_efficiency"])
        assert abs(math.sqrt(sum(e*e for e in errors)/4)-report["test_flux_relative_rmse"]) < 1e-14
        assert abs(math.sqrt(sum(e*e for e in residuals)/4)-report["test_efficiency_rmse"]) < 1e-14
    nominal = {r["method"]:r for r in physical["reports"] if r["common_flux_scale"] == 1}
    exact = nominal["established_renewal"]["test_flux_relative_rmse"]
    matrix = nominal["independent_stationary_renewal"]["test_flux_relative_rmse"]
    geometric = nominal["published_geometric_cutoff_0999"]["test_flux_relative_rmse"]
    assert abs(exact-matrix) < 1e-12
    assert exact > geometric
    assert result["practical_goal_complete"] is False
    audit = {"status": "pass", "freeze_commit": subprocess.check_output(["git", "rev-parse", FREEZE], cwd=REPO, text=True).strip(),
             "results_sha256": sha(results_raw), "vendor_local_and_git_files_checked": len(manifest),
             "hard_dead_time_rows_checked": 30, "physical_predictions_checked": 120,
             "renewal_matches_independent_stationary_solve": True,
             "observed_renewal_improvement_over_published_comparator": False,
             "goal_complete": False,
             "limitations": "Checks arithmetic, source identity and descriptive metrics; does not certify physical assumptions or finite-sample coverage."}
    (ROOT / "audit.json").write_text(json.dumps(audit, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(audit, indent=2))


if __name__ == "__main__":
    main()
