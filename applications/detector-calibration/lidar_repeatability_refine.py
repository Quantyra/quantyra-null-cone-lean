"""Audit seven numerical exceptions without changing the comparison.

Select every failed fit or normalized score above 1e-5 from the exact frozen
result below. Profile signal/background numerically in a fixed +/-2 ps delay
neighborhood, including the original fit. Retain one-sided derivatives because
the unsubtracted trimmed pulse can have a derivative jump at its support edge.
This is a local numerical audit, not global optimality or a new study gate.
"""

import argparse
import copy
import json
from pathlib import Path
import sys

import numpy as np
from scipy.io import loadmat
from scipy.optimize import minimize,minimize_scalar

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import lidar_range_screen as parent
import lidar_range_audit as exposure
import lidar_repeatability_screen as comparison

RESULT_SHA="30071b482cff23c01f0f98f3a5904def126525c471bbe82e207105487b5e914b"


def refine(model,old):
    x=np.array(old["parameters"]) if "parameters" in old else np.array([np.log(old["a"]),old["tau_ns"],np.log(old["b_per_ns"])])
    original=model.evaluate(x)
    candidates=[(original[0],x.copy(),"original")]
    def at_tau(tau):
        def objective(ab):
            xx=np.array([ab[0],tau,ab[1]])
            val,grad=model.evaluate(xx)
            return val,grad[[0,2]]
        r=minimize(objective,x[[0,2]],jac=True,method="BFGS",options={"gtol":1e-10,"maxiter":300})
        xx=np.array([r.x[0],tau,r.x[1]])
        candidates.append((float(r.fun),xx,"profile"))
        return float(r.fun)
    scalar=minimize_scalar(at_tau,method="bounded",bounds=(x[1]-.002,x[1]+.002),
                           options={"xatol":1e-13,"maxiter":200})
    for delta in [-.002,-.0001,-1e-6,-1e-8,0.,1e-8,1e-6,.0001,.002]:at_tau(x[1]+delta)
    best_value,best_x,kind=min(candidates,key=lambda item:item[0])
    side=[]
    for delta in [-1e-7,-1e-9,0.,1e-9,1e-7]:
        xx=best_x.copy();xx[1]+=delta
        val,grad=model.evaluate(xx)
        side.append({"delta_tau_ns":delta,"objective_difference":float(val-best_value),"delay_derivative":float(grad[1])})
    return {"old_tau_ns":old["tau_ns"],"refined_tau_ns":float(best_x[1]),
            "change_mm":float((best_x[1]-old["tau_ns"])*parent.C_MM_PER_NS),
            "objective_improvement":float(original[0]-best_value),"selected":kind,
            "bounded_scalar_success":bool(scalar.success),"bounded_scalar_message":str(scalar.message),
            "refined_normalized_score_max":float(np.max(np.abs(model.evaluate(best_x)[1]))),
            "profile_evaluations":len(candidates)-1,"one_sided_delay_checks":side}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--cache-dir",required=True,type=Path)
    parser.add_argument("--upstream-root",required=True,type=Path)
    parser.add_argument("--output",required=True,type=Path)
    args=parser.parse_args()
    if args.output.exists():raise FileExistsError(args.output)
    path=HERE/"lidar-repeatability-results.json"
    assert parent.sha(path)==RESULT_SHA
    original=json.loads((HERE/"lidar-range-protocol.json").read_text())
    result=json.loads(path.read_text());revised=copy.deepcopy(result)
    assert result["executable_sha256"]==parent.sha(HERE/"lidar_repeatability_screen.py")
    for name,digest in result["dependency_hashes"].items():assert parent.sha(HERE/name)==digest
    _,models,_=parent.source_modules(args.upstream_root,original)
    p=args.cache_dir/original["pulse"]["path"]
    assert parent.sha(p)==original["pulse"]["sha256"]
    calibration=loadmat(p,variable_names=["smoothPulseShape","binRes"])
    smooth=calibration["smoothPulseShape"].ravel();raw_width=float(calibration["binRes"].item())*1e9
    report={"parent_result_sha256":RESULT_SHA,"executable_sha256":parent.sha(__file__),"exceptions":[],"recomputed_comparisons":[],"physical_accuracy_validated":False}
    for condition in revised["conditions"]:
        holdoff=condition["holdoff_ns"];prefix="history" if holdoff==198 else "control"
        protocol=json.loads((HERE/f"lidar-{prefix}-protocol.json").read_text())
        prior=json.loads((HERE/f"lidar-{prefix}-results.json").read_text())
        data_path=args.cache_dir/(original["high_flux"]["path"] if holdoff==198 else protocol["archive"]["members"][0]["name"])
        assert parent.sha(data_path)==condition["file_sha256"]
        record=parent.Record(data_path,1000000);K=original["native_period_bins"];width=record.period/K
        edges=protocol["age_edges_ns"]+[np.inf];guard=protocol["delay_split_ns"]
        groups=np.array([int(a>=guard) for a in edges[:-1]])
        for vi,variant in enumerate(condition["variants"]):
            mass=smooth-smooth.min() if variant["pulse"]=="smooth_min_subtracted" else smooth.copy()
            pulse=models.EmpiricalPulse(mass/mass.sum(),raw_width/width,K)
            cal=prior["variants"][vi]["windows"][0]
            for block in variant["blocks"]:
                for name,fit in block["fits"].items():
                    if name=="native_one_step" or (fit["success"] and fit["normalized_score_max"]<=1e-5):continue
                    if name in ["native_joint","guarded"]:
                        lo=guard if name=="guarded" else (block["dead_bins_D"]+1)*width
                        n,m=exposure.integer_cells(record,block["window_frames"],K,[lo,np.inf])
                        model=exposure.Model(n,m,pulse,width,False)
                    else:
                        n,m=exposure.integer_cells(record,block["window_frames"],K,edges)
                        split=name=="calibrated_history"
                        model=comparison.Profile(n,m,pulse,width,cal["two_delays" if split else "common_delay"],groups,split)
                    detail=refine(model,fit)
                    report["exceptions"].append({"holdoff_ns":holdoff,"pulse":variant["pulse"],"window":block["window_frames"],"method":name,**detail})
                    fit["tau_ns"]=detail["refined_tau_ns"]
            summary=comparison.metrics(variant["blocks"],50)
            # A separate scalar implementation also recomputes the key ratio.
            import math
            scores={}
            for name in summary["methods"]:
                tau=[b["fits"][name]["tau_ns"] for b in variant["blocks"]]
                center=math.fsum(tau[:50])/50
                scores[name]=math.fsum(((v-center)*parent.C_MM_PER_NS)**2 for v in tau[50:])/50
                assert abs(scores[name]-summary["methods"][name]["evaluation_mean_squared_residual_mm2"])<1e-10
            best=min((n for n in scores if n!="calibrated_history"),key=scores.get)
            gain=1-scores["calibrated_history"]/scores[best]
            assert best==summary["best_comparator"]
            report["recomputed_comparisons"].append({"holdoff_ns":holdoff,"pulse":variant["pulse"],"best_comparator":best,
                                                    "mean_squared_residuals_mm2":scores,"history_fractional_msr_reduction":gain,
                                                    "development_gate_pass":gain>=.2})
    assert len(report["exceptions"])==7
    report["max_delay_change_mm"]=max(abs(e["change_mm"]) for e in report["exceptions"])
    report["limits"]="Local nuisance-profile audit. A clipped pulse endpoint can have nonzero one-sided score at a local minimum. Original fits and solver messages remain preserved; no global optimum or physical calibration claimed."
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"sha256":parent.sha(args.output),"max_delay_change_mm":report["max_delay_change_mm"],"comparisons":report["recomputed_comparisons"]}))


if __name__=="__main__":main()
