"""Matched-calibration development repeatability at 10000-period budgets."""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

import numpy as np
from scipy.io import loadmat
from scipy.optimize import minimize

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import lidar_range_screen as parent
import lidar_range_audit as exposure


class Profile:
    def __init__(self,n,m,pulse,width,calibration,groups,split):
        self.n,self.m,self.pulse,self.width=n,m,pulse,width
        self.a=np.array(calibration["a"]);self.b=np.array(calibration["b_per_ns"])*width
        self.groups=np.asarray(groups,dtype=int)
        self.delta=np.array([calibration["tau_ns"][0]-calibration["tau_ns"][1],0.]) if split else np.zeros(2)
        self.phases=np.arange(n.shape[1],dtype=float)
        self.totn,self.totm=n.sum(axis=1),m.sum(axis=1)
        self.total=int(n.sum());self.K=n.shape[1]

    def evaluate(self,x,dense=False):
        A,B=np.exp(x[0]),np.exp(x[2])
        ll=0.;gradient=np.zeros(3)
        for group in range(2):
            rows=np.flatnonzero(self.groups==group)
            f=self.pulse.bin_mass(self.phases,(x[1]+self.delta[group])/self.width+.5)
            df=self.pulse.bin_mass_derivative(self.phases,(x[1]+self.delta[group])/self.width+.5)/self.width
            n,m=self.n[rows],self.m[rows]
            if not dense:
                support=(f>0)|(df!=0)
                n=np.column_stack([n[:,support],self.totn[rows]-n[:,support].sum(axis=1)])
                m=np.column_stack([m[:,support],self.totm[rows]-m[:,support].sum(axis=1)])
                f,df=np.r_[f[support],0.],np.r_[df[support],0.]
            signal=A*self.a[rows,None]*f
            background=B*self.b[rows,None]
            z=signal+background;p=-np.expm1(-z)
            weight=n/p-m
            ll+=float(np.sum(n*np.log(p)-(m-n)*z))
            gradient+=np.array([np.sum(weight*signal),np.sum(weight*A*self.a[rows,None]*df),np.sum(weight*background)])
        return -ll/self.total,-gradient/self.total


def fit_profile(model,tau,settings):
    bounds=[(-5,5),(tau-settings["delay_radius_ns"],tau+settings["delay_radius_ns"]),(-5,5)]
    solutions=[]
    for offset in settings["delay_offsets_ns"]:
        solutions.append(minimize(model.evaluate,np.array([0.,tau+offset,0.]),jac=True,method="L-BFGS-B",bounds=bounds,
                                  options={key:settings[key] for key in ["maxiter","ftol","gtol"]}))
    best=min(solutions,key=lambda r:r.fun)
    compact=model.evaluate(best.x);dense=model.evaluate(best.x,dense=True)
    ll_error=abs(compact[0]-dense[0])*model.total
    score_error=float(np.max(np.abs(compact[1]-dense[1])))
    assert ll_error<1e-7 and score_error<1e-10
    check=best.x+np.array([.011,.000013,-.017]);analytical=model.evaluate(check)[1]
    errors=[]
    for k,h in enumerate([1e-5,1e-7,1e-5]):
        d=np.zeros(3);d[k]=h
        errors.append(abs((model.evaluate(check+d)[0]-model.evaluate(check-d)[0])/(2*h)-analytical[k]))
    assert max(errors)<1e-6
    return {"tau_ns":float(best.x[1]),"parameters":best.x.tolist(),"success":bool(best.success),
            "message":str(best.message),"negative_mean_loglik":float(best.fun),"iterations":int(best.nit),
            "normalized_score_max":float(np.max(np.abs(compact[1]))),"gradient_difference_max":max(errors),
            "dense_loglik_difference":float(ll_error),"dense_score_difference":score_error,
            "on_bound":bool(any(min(best.x[k]-lo,hi-best.x[k])<1e-5 for k,(lo,hi) in enumerate(bounds))),
            "starts":[{"tau_ns":float(r.x[1]),"negative_mean_loglik":float(r.fun),"success":bool(r.success)} for r in solutions]}


def upstream_check(model,fit,upstream):
    x=np.array(fit["parameters"]);A,B=np.exp(x[0]),np.exp(x[2])
    ll=0.;score=np.zeros(3)
    for j,group in enumerate(model.groups):
        theta=np.array([A*model.a[j],(x[1]+model.delta[group])/model.width+.5,B*model.b[j]])
        row_ll,row_score=upstream.loglik_and_score(model.n[j],model.m[j],theta,model.phases,model.K,1.,1.,5,model.pulse)
        ll+=row_ll
        score+=row_score*np.array([theta[0],1/model.width,theta[2]])
    compact=model.evaluate(x)
    errors=[float(abs(ll+compact[0]*model.total)),float(np.max(np.abs(score/model.total+compact[1])))]
    assert errors[0]<1e-7 and errors[1]<1e-10
    return errors


def metrics(blocks,calibration_count):
    names=["native_joint","native_one_step","guarded","calibrated_common","calibrated_history"]
    summaries={};losses={}
    for name in names:
        tau=np.array([row["fits"][name]["tau_ns"] for row in blocks])
        center=float(tau[:calibration_count].mean())
        train=(tau[:calibration_count]-center)*parent.C_MM_PER_NS
        residual=(tau[calibration_count:]-center)*parent.C_MM_PER_NS
        assert abs(train.mean())<1e-10
        losses[name]=residual**2
        summaries[name]={"calibration_mean_tau_ns":center,"training_mean_residual_mm":float(train.mean()),
                         "evaluation_mean_residual_mm":float(residual.mean()),
                         "evaluation_centered_variance_mm2":float(np.var(residual,ddof=1)),
                         "evaluation_mean_squared_residual_mm2":float(np.mean(residual**2)),
                         "evaluation_fraction_within_1mm":float(np.mean(np.abs(residual)<=1)),
                         "evaluation_residuals_mm":residual.tolist()}
    best=min(names[:-1],key=lambda name:losses[name].mean())
    comparisons={}
    for name in names[:-1]:
        paired=losses["calibrated_history"]-losses[name]
        comparisons[name]={"history_fractional_msr_reduction":float(1-losses["calibrated_history"].mean()/losses[name].mean()),
                           "paired_squared_residual_differences_mm2":paired.tolist(),
                           "mean_difference_mm2":float(paired.mean()),"descriptive_mean_se_mm2":float(paired.std(ddof=1)/np.sqrt(len(paired)))}
    return {"methods":summaries,"best_comparator":best,"paired_comparisons":comparisons,
            "history_beats_best_by_20_percent":bool(comparisons[best]["history_fractional_msr_reduction"]>=.2)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--cache-dir",type=Path,required=True)
    parser.add_argument("--upstream-root",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    if args.output.exists():raise FileExistsError(args.output)
    start=time.monotonic()
    protocol_path=HERE/"lidar-repeatability-protocol.json"
    protocol=json.loads(protocol_path.read_text())
    original=json.loads((HERE/"lidar-range-protocol.json").read_text())
    dependencies={}
    for name in ["lidar_range_screen.py","lidar_range_audit.py","lidar-range-protocol.json",
                 "lidar-history-protocol.json","lidar-history-results.json","lidar-control-protocol.json","lidar-control-results.json"]:
        frozen=subprocess.check_output(["git","show",f'{protocol["parent_commit"]}:applications/detector-calibration/{name}'],cwd=HERE)
        assert frozen==(HERE/name).read_bytes()
        dependencies[name]=parent.sha(HERE/name)
    upstream,models,hashes=parent.source_modules(args.upstream_root,original)
    pulse_path=args.cache_dir/original["pulse"]["path"]
    assert parent.sha(pulse_path)==original["pulse"]["sha256"]
    calibration=loadmat(pulse_path,variable_names=["smoothPulseShape","binRes"])
    smooth=calibration["smoothPulseShape"].ravel();raw_width=float(calibration["binRes"].item())*1e9
    K=original["native_period_bins"]
    result={"protocol_sha256":parent.sha(protocol_path),"executable_sha256":parent.sha(__file__),
            "dependency_hashes":dependencies,"upstream_hashes":hashes,"conditions":[],"physical_benefit_demonstrated":False}
    for holdoff,prefix in [(198,"history"),(180,"control")]:
        condition_protocol=json.loads((HERE/f"lidar-{prefix}-protocol.json").read_text())
        prior=json.loads((HERE/f"lidar-{prefix}-results.json").read_text())
        name=original["high_flux"]["path"] if holdoff==198 else condition_protocol["archive"]["members"][0]["name"]
        expected=original["high_flux"]["sha256"] if holdoff==198 else prior["input"]["file_sha256"]
        assert parent.sha(args.cache_dir/name)==expected
        record=parent.Record(args.cache_dir/name,1000000)
        width=record.period/K
        indices=record.frames*K+np.floor(record.phase/width+.5).astype(np.int64);gaps=np.diff(indices)
        edges=condition_protocol["age_edges_ns"]+[np.inf]
        guard=condition_protocol["delay_split_ns"]
        groups=np.array([int(a>=guard) for a in edges[:-1]])
        condition={"holdoff_ns":holdoff,"file_sha256":expected,"variants":[]}
        for vi,variant in enumerate(prior["variants"]):
            mass=smooth-smooth.min() if variant["pulse"]=="smooth_min_subtracted" else smooth.copy()
            pulse=models.EmpiricalPulse(mass/mass.sum(),raw_width/width,K)
            frozen_cal=variant["windows"][0]
            profile_tau=frozen_cal["two_delays"]["tau_ns"][1]
            row={"pulse":variant["pulse"],"blocks":[]}
            for left in range(0,1000000,protocol["block_frames"]):
                window=[left,left+protocol["block_frames"]]
                selected=(indices[1:]>=left*K)&(indices[1:]<window[1]*K)
                D=min(int(gaps[selected].min())-1,int(np.floor((holdoff+2)/width)))
                assert D>=int(np.floor(holdoff/width))
                nh,mh=exposure.integer_cells(record,window,K,[(D+1)*width,np.inf])
                assert nh.sum()==int(selected.sum())
                phases=np.arange(K,dtype=float)
                pilot=upstream.robust_pilot(nh[0],mh[0],phases,K,1.,1.,5,pulse)
                one=upstream.one_step(pilot,nh[0],mh[0],(window[1]-window[0])*K,phases,K,1.,1.,5,pulse)
                ordinary=[pilot[0],(pilot[1]-.5)*width,pilot[2]/width]
                fits={"native_joint":exposure.fit(exposure.Model(nh,mh,pulse,width,False),ordinary,protocol),
                      "native_one_step":{"tau_ns":float((one[1]-.5)*width),"source_function":"unmodified one_step"}}
                ng,mg=exposure.integer_cells(record,window,K,[guard,np.inf])
                fits["guarded"]=exposure.fit(exposure.Model(ng,mg,pulse,width,False),ordinary,protocol)
                n,m=exposure.integer_cells(record,window,K,edges)
                un,um=exposure.integer_cells(record,window,K,[edges[0],np.inf])
                assert np.array_equal(n.sum(axis=0),un[0]) and np.array_equal(m.sum(axis=0),um[0])
                assert np.array_equal(n[groups==1].sum(axis=0),ng[0]) and np.array_equal(m[groups==1].sum(axis=0),mg[0])
                checks={}
                for method,field,split in [("calibrated_common","common_delay",False),("calibrated_history","two_delays",True)]:
                    model=Profile(n,m,pulse,width,frozen_cal[field],groups,split)
                    tau=frozen_cal[field]["tau_ns"][-1]
                    fits[method]=fit_profile(model,tau,protocol["numerics"])
                    if left in [0,490000,500000,990000]:checks[method]=upstream_check(model,fits[method],upstream)
                row["blocks"].append({"window_frames":window,"dead_bins_D":D,"detections":int(selected.sum()),
                                      "fits":fits,"partition_checks":"pass","upstream_profile_checks":checks})
                if len(row["blocks"])%25==0:
                    print(json.dumps({"holdoff":holdoff,"pulse":row["pulse"],"blocks":len(row["blocks"]),"elapsed_seconds":time.monotonic()-start}),flush=True)
            row["summary"]=metrics(row["blocks"],50)
            condition["variants"].append(row)
            print(json.dumps({"holdoff":holdoff,"pulse":row["pulse"],"best_comparator":row["summary"]["best_comparator"],
                              "gate":row["summary"]["history_beats_best_by_20_percent"],
                              "msr":{k:v["evaluation_mean_squared_residual_mm2"] for k,v in row["summary"]["methods"].items()}}),flush=True)
        result["conditions"].append(condition)
    result["principal_development_gate_pass"]=all(v["summary"]["history_beats_best_by_20_percent"] for v in result["conditions"][0]["variants"])
    result["elapsed_seconds"]=time.monotonic()-start
    result["limits"]="Adaptive development repeatability relative to method-specific calibration means, using previously inspected prefixes. No physical ground truth, calibrated confidence or final risk/accuracy claim."
    args.output.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"sha256":parent.sha(args.output),"principal_gate":result["principal_development_gate_pass"]}),flush=True)


if __name__=="__main__":main()
