"""Match the observation model when auditing a recovery-induced delay change."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

import numpy as np
from scipy.io import loadmat
from scipy.optimize import minimize

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import lidar_range_screen as parent


def integer_cells(record,window,K,edges):
    width=record.period/K
    index=record.frames*K+np.floor(record.phase/width+0.5).astype(np.int64)
    gaps=np.diff(index)
    event=(index[1:]>=window[0]*K)&(index[1:]<window[1]*K)
    counts=[];opened=[]
    for a,b in zip(edges[:-1],edges[1:]):
        lo=int(np.ceil(a/width-1e-10))
        hi=int(np.ceil(b/width-1e-10)) if np.isfinite(b) else None
        selected=event&(gaps>=lo)
        if hi is not None:
            selected &= gaps<hi
        n=np.bincount((index[1:]%K)[selected],minlength=K)
        start=np.maximum(index+lo,window[0]*K)
        stop=np.minimum(np.r_[index[1:]+1,window[1]*K],window[1]*K)
        if hi is not None:
            stop=np.minimum(stop,index+hi)
        mask=stop>start
        start,stop=start[mask],stop[mask]
        cycles=(stop//K-start//K).sum()
        left=np.bincount(start%K,minlength=K)
        right=np.bincount(stop%K,minlength=K)
        m=cycles+np.cumsum(left)-np.cumsum(right)
        assert np.all(m>=n)
        assert int(m.sum())==int((stop-start).sum())
        counts.append(n);opened.append(m)
    return np.array(counts),np.array(opened)


class Model:
    def __init__(self,n,m,pulse,width,profile):
        self.n,self.m=n,m
        self.pulse,self.width=pulse,width
        self.total=int(n.sum())
        self.active=n.sum(axis=1)>0
        # Nonempty early rows have positive fitted factors; empty rows are
        # profiled to zero. The last row fixes the common amplitude scale.
        self.free=np.flatnonzero(self.active & (np.arange(len(n))<len(n)-1)) if profile else np.array([],dtype=int)
        self.profile=profile
        self.phases=np.arange(n.shape[1],dtype=float)
        self.totn=n.sum(axis=1);self.totm=m.sum(axis=1)

    def evaluate(self,x):
        a,b=np.exp(x[0]),np.exp(x[2])*self.width
        tau=x[1]/self.width+0.5
        f=self.pulse.bin_mass(self.phases,tau)
        df=self.pulse.bin_mass_derivative(self.phases,tau)/self.width
        support=(f>0)|(df!=0)
        # Collapse all exactly background-only phases without changing likelihood.
        ns=np.column_stack([self.n[:,support],self.totn-self.n[:,support].sum(axis=1)])
        ms=np.column_stack([self.m[:,support],self.totm-self.m[:,support].sum(axis=1)])
        fs=np.r_[f[support],0.0];dfs=np.r_[df[support],0.0]
        lam=a*fs+b
        g=np.ones(len(self.n))
        if self.profile:
            g[~self.active]=0
            g[self.free]=np.exp(x[3:])
        z=g[:,None]*lam[None,:]
        p=-np.expm1(-z)
        safe=np.maximum(p,1e-300)
        ll=float(np.sum(ns*np.log(safe)-(ms-ns)*z))
        weight=ns/safe-ms
        dl=np.column_stack([a*fs,a*dfs,np.full(len(fs),b)])
        grad=list(np.sum(g[:,None]*weight,axis=0)@dl)
        grad.extend(np.sum(weight*z,axis=1)[self.free])
        return -ll/self.total,-np.array(grad)/self.total


def fit(model,pilot,protocol):
    base=np.array([np.log(pilot[0]),pilot[1],np.log(pilot[2])])
    if len(model.free):
        f=model.pulse.bin_mass(model.phases,pilot[1]/model.width+0.5)
        integral=model.m@(pilot[0]*f+pilot[2]*model.width)
        initial=np.log(np.maximum(model.totn[model.free]/integral[model.free],1e-6))
        base=np.r_[base,initial]
    bounds=[(-15,5),(pilot[1]-.4,pilot[1]+.4),(-25,2)]+[(-15,5)]*len(model.free)
    results=[]
    for offset in protocol["numerics"]["delay_offsets_ns"]:
        x=base.copy();x[1]+=offset
        results.append(minimize(model.evaluate,x,jac=True,bounds=bounds,method="L-BFGS-B",options={
            "maxiter":protocol["numerics"]["maxiter"],"ftol":protocol["numerics"]["ftol"],"gtol":protocol["numerics"]["gtol"]}))
    best=min(results,key=lambda r:r.fun)
    x=best.x.copy();x[0]+=.011;x[1]+=.000013;x[2]-=.017
    analytical=model.evaluate(x)[1]
    errors=[]
    for k in range(len(x)):
        h=1e-7 if k==1 else 1e-5
        d=np.zeros(len(x));d[k]=h
        numerical=(model.evaluate(x+d)[0]-model.evaluate(x-d)[0])/(2*h)
        errors.append(abs(numerical-analytical[k]))
    g=np.ones(len(model.n))
    if model.profile:
        g[~model.active]=0;g[model.free]=np.exp(best.x[3:])
    return {"tau_ns":float(best.x[1]),"a":float(np.exp(best.x[0])),"b_per_ns":float(np.exp(best.x[2])),
            "g":g.tolist(),"detections":model.total,"negative_mean_loglik":float(best.fun),
            "success":bool(best.success),"message":str(best.message),"iterations":int(best.nit),
            "normalized_score_max":float(np.max(np.abs(model.evaluate(best.x)[1]))),
            "gradient_difference_max":max(errors),
            "starts":[{"tau_ns":float(r.x[1]),"negative_mean_loglik":float(r.fun),"success":bool(r.success),"iterations":int(r.nit)} for r in results]}


def synthetic_audit():
    r=parent.Record.__new__(parent.Record)
    r.period=100.;r.frames=np.array([0,2,4,6]);r.phase=np.array([1.,1.,9.,10.])
    r.gap=np.diff(r.frames)*100+np.diff(r.phase)
    K=25;edges=[196,204,216,np.inf];window=[0,8]
    n,m=integer_cells(r,window,K,edges)
    en,em=np.zeros_like(n),np.zeros_like(m)
    events=(r.frames*K+np.floor(r.phase/4+.5)).astype(int)
    for previous,next_event in zip(events,np.r_[events[1:],window[1]*K]):
        for slot in range(previous+1,min(next_event+1,window[1]*K)):
            age=(slot-previous)*4
            j=np.searchsorted(edges,age,side="right")-1
            if 0<=j<len(n):
                em[j,slot%K]+=1
                if slot==next_event and next_event<window[1]*K:
                    en[j,slot%K]+=1
    assert np.array_equal(n,en) and np.array_equal(m,em)
    return {"synthetic_integer_enumeration":"pass","cells":int(n.size)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--cache-dir",required=True,type=Path)
    parser.add_argument("--upstream-root",required=True,type=Path)
    parser.add_argument("--output",required=True,type=Path)
    args=parser.parse_args()
    if args.output.exists():raise FileExistsError(args.output)
    apath=HERE/"lidar-range-audit-protocol.json"
    audit=json.loads(apath.read_text());protocol=json.loads((HERE/"lidar-range-protocol.json").read_text())
    old=json.loads((HERE/"lidar-range-results.json").read_text())
    assert parent.sha(HERE/"lidar-range-results.json")==audit["parent_result_sha256"]
    for name,key in [("lidar-range-protocol.json","protocol_sha256"),("lidar_range_screen.py","executable_sha256"),("lidar-range-argument.md","argument_sha256")]:
        frozen=subprocess.check_output(["git","show",f'{audit["parent_freeze"]}:applications/detector-calibration/{name}'],cwd=HERE)
        assert parent.hashlib.sha256(frozen).hexdigest()==parent.sha(HERE/name)==old[key]
    upstream,models,hashes=parent.source_modules(args.upstream_root,protocol)
    for key in ["high_flux","low_flux","pulse"]:
        assert parent.sha(args.cache_dir/protocol[key]["path"])==protocol[key]["sha256"]
    high=parent.Record(args.cache_dir/protocol["high_flux"]["path"],1000000)
    low=parent.Record(args.cache_dir/protocol["low_flux"]["path"],1000000)
    data=loadmat(args.cache_dir/protocol["pulse"]["path"],variable_names=["smoothPulseShape","binRes"])
    smooth=data["smoothPulseShape"].ravel();raw_width=float(data["binRes"].item())*1e9
    K=protocol["native_period_bins"]
    result={"audit_protocol_sha256":parent.sha(apath),"audit_executable_sha256":parent.sha(__file__),
            "parent_result_sha256":parent.sha(HERE/"lidar-range-results.json"),"synthetic_audit":synthetic_audit(),
            "variants":[],"range_benefit_demonstrated":False}
    for variant in old["variants"]:
        mass=smooth-smooth.min() if variant["pulse"]=="smooth_min_subtracted" else smooth.copy()
        mass=mass/mass.sum()
        row={"pulse":variant["pulse"],"high_flux":[]}
        width=low.period/K;pulse=models.EmpiricalPulse(mass,raw_width/width,K)
        n,m=integer_cells(low,protocol["low_flux_window_frames"],K,[protocol["low_flux_guard_ns"],np.inf])
        previous=variant["low_flux_provisional_reference"]
        row["low_flux_provisional_reference"]=fit(Model(n,m,pulse,width,False),[previous["a"],previous["tau_ns"],previous["b_per_ns"]],audit)
        for old_window in variant["high_flux"]:
            window=old_window["window_frames"];width=high.period/K
            pulse=models.EmpiricalPulse(mass,raw_width/width,K)
            native=old_window["native_discrete"]
            pilot=[native["joint_mle_a"],native["joint_mle_tau_ns"],native["joint_mle_b_per_ns"]]
            # A direct equality audit against the independently structured parent.
            direct_n,direct_m,D=high.discrete(window,K)
            n0,m0=integer_cells(high,window,K,[(D+1)*width,np.inf])
            assert np.array_equal(n0[0],direct_n) and np.array_equal(m0[0],direct_m)
            edges=protocol["profile_age_edges_ns"]+[np.inf]
            n,m=integer_cells(high,window,K,edges)
            union_n,union_m=integer_cells(high,window,K,[edges[0],np.inf])
            assert np.array_equal(n.sum(axis=0),union_n[0]) and np.array_equal(m.sum(axis=0),union_m[0])
            recovered=fit(Model(n,m,pulse,width,True),pilot,audit)
            ng,mg=integer_cells(high,window,K,[205,np.inf])
            guarded=fit(Model(ng,mg,pulse,width,False),pilot,audit)
            item={"window_frames":window,"hard_exposure_counts_equal":True,"age_partition_equal":True,
                  "profiled_recovery":recovered,"guard_205":guarded,
                  "recovery_minus_native_hard_mm":(recovered["tau_ns"]-native["joint_mle_tau_ns"])*parent.C_MM_PER_NS,
                  "guard_minus_native_hard_mm":(guarded["tau_ns"]-native["joint_mle_tau_ns"])*parent.C_MM_PER_NS}
            row["high_flux"].append(item)
            print(json.dumps({"pulse":row["pulse"],"window":window,"recovery_change_mm":item["recovery_minus_native_hard_mm"],
                              "guard_change_mm":item["guard_minus_native_hard_mm"]}),flush=True)
        result["variants"].append(row)
    corrections=np.array([w["recovery_minus_native_hard_mm"] for v in result["variants"] for w in v["high_flux"]])
    result["matched_model_correction_gate_pass"]=bool(np.all(np.abs(corrections)>=.2) and np.all(np.sign(corrections)==np.sign(corrections[0])))
    result["limits"]="Adaptive development audit, quantized working likelihood, local optimization. Low-flux reference is provisional. No independent target calibration, performance superiority or physical coverage established."
    args.output.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"output":str(args.output),"sha256":parent.sha(args.output),"gate":result["matched_model_correction_gate_pass"]}))


if __name__=="__main__":main()
