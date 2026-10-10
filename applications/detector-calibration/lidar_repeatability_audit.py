"""Independent scalar recomputation of calibration and paired residual metrics."""

import argparse
import hashlib
import json
import math
from pathlib import Path

HERE=Path(__file__).resolve().parent
C=149.896229


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    if args.output.exists():raise FileExistsError(args.output)
    path=HERE/"lidar-repeatability-results.json"
    data=json.loads(path.read_text())
    assert data["protocol_sha256"]==sha(HERE/"lidar-repeatability-protocol.json")
    assert data["executable_sha256"]==sha(HERE/"lidar_repeatability_screen.py")
    comparisons=[];diagnostics=[];maximum=0.;checked=0
    for condition in data["conditions"]:
        for variant in condition["variants"]:
            blocks=variant["blocks"];summary=variant["summary"]
            assert [b["window_frames"] for b in blocks]==[[i*10000,(i+1)*10000] for i in range(100)]
            assert all(b["partition_checks"]=="pass" for b in blocks)
            losses={}
            for name,reported in summary["methods"].items():
                fits=[block["fits"][name] for block in blocks]
                delays=[fit["tau_ns"] for fit in fits]
                center=math.fsum(delays[:50])/50
                residual=[(tau-center)*C for tau in delays[50:]]
                mean=math.fsum(residual)/50
                msr=math.fsum(v*v for v in residual)/50
                variance=math.fsum((v-mean)**2 for v in residual)/49
                fraction=sum(abs(v)<=1 for v in residual)/50
                values=[(center,reported["calibration_mean_tau_ns"]),(mean,reported["evaluation_mean_residual_mm"]),
                        (msr,reported["evaluation_mean_squared_residual_mm2"]),
                        (variance,reported["evaluation_centered_variance_mm2"]),(fraction,reported["evaluation_fraction_within_1mm"])]
                values.extend(zip(residual,reported["evaluation_residuals_mm"]))
                maximum=max(maximum,max(abs(a-b) for a,b in values))
                assert abs(msr-49/50*variance-mean*mean)<1e-12
                assert abs(math.fsum((tau-center)*C for tau in delays[:50])/50)<1e-10
                losses[name]=[v*v for v in residual]
                checked+=len(values)
                if name!="native_one_step":
                    diagnostics.extend({"success":fit["success"],"score":fit["normalized_score_max"],
                                        "finite_difference":fit["gradient_difference_max"],"on_bound":fit.get("on_bound",False),
                                        "start_delay_span_ns":max(s["tau_ns"] for s in fit["starts"])-min(s["tau_ns"] for s in fit["starts"])} for fit in fits)
            best=min((name for name in losses if name!="calibrated_history"),key=lambda name:math.fsum(losses[name])/50)
            assert best==summary["best_comparator"]
            for name,reported in summary["paired_comparisons"].items():
                paired=[a-b for a,b in zip(losses["calibrated_history"],losses[name])]
                mean=math.fsum(paired)/50
                se=math.sqrt(math.fsum((v-mean)**2 for v in paired)/49/50)
                improvement=1-math.fsum(losses["calibrated_history"])/math.fsum(losses[name])
                values=list(zip(paired,reported["paired_squared_residual_differences_mm2"]))+[
                    (mean,reported["mean_difference_mm2"]),(se,reported["descriptive_mean_se_mm2"]),
                    (improvement,reported["history_fractional_msr_reduction"])]
                maximum=max(maximum,max(abs(a-b) for a,b in values));checked+=len(values)
            gain=1-math.fsum(losses["calibrated_history"])/math.fsum(losses[best])
            assert (gain>=.2)==summary["history_beats_best_by_20_percent"]
            comparisons.append({"holdoff_ns":condition["holdoff_ns"],"pulse":variant["pulse"],"best_comparator":best,
                                "history_fractional_msr_reduction":gain,"development_gate_pass":gain>=.2})
    assert maximum<1e-10
    assert data["principal_development_gate_pass"]==all(r["development_gate_pass"] for r in comparisons if r["holdoff_ns"]==198)
    report={"result_sha256":sha(path),"audit_executable_sha256":sha(Path(__file__)),"status":"pass",
            "scalar_values_checked":checked,"max_independent_metric_difference":maximum,
            "fit_count":len(diagnostics),"successful_fit_count":sum(d["success"] for d in diagnostics),
            "profile_fits_on_bounds":sum(d["on_bound"] for d in diagnostics),
            "max_normalized_score":max(d["score"] for d in diagnostics),
            "max_gradient_difference":max(d["finite_difference"] for d in diagnostics),
            "max_start_delay_span_ns":max(d["start_delay_span_ns"] for d in diagnostics),
            "comparisons":comparisons,"physical_accuracy_validated":False}
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps(report))


if __name__=="__main__":main()
