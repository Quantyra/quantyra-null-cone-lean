"""Bounded ranging consequence of the recovery diagnostic.

Endpoint integration is exact for the stated continuous pulse model. It does
not remove physical timestamp quantization or calibrate the working model.
The pinned MIT upstream code is read from an external cache and hash checked.
"""

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import platform
import sys
import time

import numpy as np
import scipy
from scipy.interpolate import PchipInterpolator
from scipy.io import loadmat
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
C_MM_PER_NS = 149.896229


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Pulse:
    def __init__(self, mass, width, period):
        self.mass = np.asarray(mass) / np.sum(mass)
        self.width, self.period = float(width), float(period)
        self.length = len(mass) * width
        self.cdf = PchipInterpolator(np.arange(len(mass)+1)*width, np.r_[0,np.cumsum(self.mass)])
        self.pdf, self.slope = self.cdf.derivative(), self.cdf.derivative(2)

    def shape(self, phase, tau):
        x = np.remainder(np.asarray(phase)-tau, self.period)
        inside = (x > 0) & (x < self.length)
        f, dt = np.zeros_like(x), np.zeros_like(x)
        f[inside] = self.pdf(x[inside])
        dt[inside] = -self.slope(x[inside])
        return f, dt

    def primitive(self, time):
        cycles = np.floor(time / self.period)
        x = time-cycles*self.period
        return cycles+self.cdf(np.clip(x,0,self.length))


class Exposure:
    def __init__(self, lo_phase, duration, period):
        self.period = float(period)
        self.lo_phase = np.asarray(lo_phase)
        self.duration = np.asarray(duration)
        upper = self.lo_phase+self.duration
        self.cycles = float(np.floor(upper/period).sum())
        end = np.remainder(upper,period)
        points, ids = np.unique(np.r_[self.lo_phase,end],return_inverse=True)
        weights = np.bincount(ids,weights=np.r_[-np.ones(len(end)),np.ones(len(end))])
        nonzero = weights != 0
        self.points, self.weights = points[nonzero], weights[nonzero]
        self.prefix = np.r_[0,np.cumsum(self.weights)]
        self.total = float(self.duration.sum())

    def integral(self,pulse,tau):
        tau = tau % self.period
        cut = np.searchsorted(self.points,tau)
        value = self.cycles+self.prefix[-1]-self.prefix[cut]
        derivative = 0.0
        # Only endpoints inside the compact pulse support need interpolation.
        ranges = [(tau,min(tau+pulse.length,self.period),0.0)]
        if tau+pulse.length>self.period:
            ranges.append((0.0,tau+pulse.length-self.period,self.period))
        for lo,hi,offset in ranges:
            l,r = np.searchsorted(self.points,[lo,hi])
            x = self.points[l:r]-tau+offset
            w = self.weights[l:r]
            if len(x):
                value += float(w @ (pulse.cdf(x)-1))
                derivative -= float(w @ pulse.pdf(x))
        return float(value),float(derivative)


class Record:
    def __init__(self,path,limit):
        d = loadmat(path,variable_names=["frameNum","detTime","tr"])
        frames = d["frameNum"].ravel()
        keep = (frames>=0)&(frames<limit)
        self.period = float(d["tr"].item())*1e9
        phase = d["detTime"].ravel()[keep]
        self.frames = frames[keep].astype(np.int64)+np.floor(phase/self.period).astype(np.int64)
        self.phase = np.remainder(phase,self.period)
        self.gap = np.diff(self.frames)*self.period+np.diff(self.phase)
        assert np.all(self.gap>0)

    def selected_events(self,window,lo,hi=np.inf):
        mask = ((self.frames[1:]>=window[0])&(self.frames[1:]<window[1])
                &(self.gap>=lo)&(self.gap<hi))
        p,n = np.unique(self.phase[1:][mask],return_counts=True)
        return p,n

    def segment(self,window,lo,hi=np.inf):
        left = np.maximum(lo,(window[0]-self.frames)*self.period-self.phase)
        right = np.minimum(np.r_[self.gap,np.inf],(window[1]-self.frames)*self.period-self.phase)
        right = np.minimum(right,hi)
        keep = right>left
        return Exposure(np.remainder(self.phase[keep]+left[keep],self.period),right[keep]-left[keep],self.period)

    def smallest_gap(self,window):
        mask = (self.frames[1:]>=window[0])&(self.frames[1:]<window[1])
        return float(self.gap[mask].min())

    def discrete(self,window,K):
        width = self.period/K
        rounded_bins = np.floor(self.phase/width+0.5).astype(np.int64)
        index = self.frames*K+rounded_bins
        phase_bins = rounded_bins % K
        event_keep = (index[1:]>=window[0]*K)&(index[1:]<window[1]*K)
        min_gap = int(np.diff(index)[event_keep].min())
        D = min(min_gap-1,int(np.floor(200/width)))
        assert D>=int(np.floor(198/width))
        starts = np.maximum(index+D+1,window[0]*K)
        stops = np.minimum(np.r_[index[1:]+1,window[1]*K],window[1]*K)
        keep = stops>starts
        starts,stops = starts[keep],stops[keep]
        cycles = (stops//K-starts//K).sum()
        left,right = starts%K,stops%K
        hist_l=np.bincount(left,minlength=K);hist_r=np.bincount(right,minlength=K)
        opened = cycles + np.cumsum(hist_l)-np.cumsum(hist_r)
        observed = np.bincount(phase_bins[1:][event_keep],minlength=K)
        assert np.all(opened>=observed)
        assert int(opened.sum())==int((stops-starts).sum())
        return observed,opened,D


class Likelihood:
    def __init__(self,record,window,pulse,edges,profile=False):
        self.pulse,self.profile = pulse,profile
        self.exposures=[];self.nj=[]
        phases=[];numbers=[]
        for lo,hi in zip(edges[:-1],edges[1:]):
            self.exposures.append(record.segment(window,lo,hi))
            p,n=record.selected_events(window,lo,hi)
            self.nj.append(int(n.sum()));phases.extend(p);numbers.extend(n)
        self.phases,idx=np.unique(phases,return_inverse=True)
        self.counts=np.bincount(idx,weights=numbers)
        self.nj=np.array(self.nj)
        self.total=int(self.nj.sum())

    def evaluate(self,x,details=False):
        a,b=np.exp(x[0]),np.exp(x[2]);tau=x[1]
        f,df=self.pulse.shape(self.phases,tau)
        lam=a*f+b
        deriv=np.column_stack([a*f,a*df,np.full(len(f),b)])
        ll=float(self.counts @ np.log(lam))
        grad=deriv.T@(self.counts/lam)
        recovery=[]
        for j,exp in enumerate(self.exposures):
            q,dq=exp.integral(self.pulse,tau)
            integral=a*q+b*exp.total
            dint=np.array([a*q,a*dq,b*exp.total])
            if self.profile and j<len(self.exposures)-1:
                g=self.nj[j]/integral if integral>0 else 0.0
                if self.nj[j]>0:
                    ll+=self.nj[j]*(np.log(g)-1)
                grad-=g*dint
            else:
                g=1.0;ll-=integral;grad-=dint
            recovery.append(float(g))
        if details:
            return ll,grad,recovery
        return -ll/self.total,-grad/self.total


def fit_continuous(model,pilot,protocol):
    settings=protocol["solver"]
    candidates=[]
    bounds=[(-15,5),(pilot[1]-settings["delay_search_radius_ns"],pilot[1]+settings["delay_search_radius_ns"]),(-25,2)]
    for offset in settings["delay_start_offsets_ns"]:
        start=np.array([np.log(max(pilot[0],1e-6)),pilot[1]+offset,np.log(max(pilot[2],1e-8))])
        result=minimize(model.evaluate,start,jac=True,method="L-BFGS-B",bounds=bounds,
                        options={"maxiter":settings["maximum_iterations"],"ftol":settings["ftol"],"gtol":settings["gtol"]})
        candidates.append(result)
    best=min(candidates,key=lambda v:v.fun)
    ll,grad,g=model.evaluate(best.x,details=True)
    # A score finite-difference audit at an off-optimum point avoids judging
    # numerical cancellation against a nearly zero fitted score.
    check=best.x+np.array([0.017,0.000013,-0.023])
    analytic=model.evaluate(check)[1]
    numerical=[]
    for k,h in enumerate([1e-5,1e-7,1e-5]):
        d=np.zeros(3);d[k]=h
        numerical.append((model.evaluate(check+d)[0]-model.evaluate(check-d)[0])/(2*h))
    gradient_error=float(np.max(np.abs(analytic-np.array(numerical))))
    return {"a":float(np.exp(best.x[0])),"tau_ns":float(best.x[1]),"b_per_ns":float(np.exp(best.x[2])),
            "log_likelihood":ll,"detections_scored":model.total,"recovery_factors":g,
            "optimizer_success":bool(best.success),"optimizer_message":str(best.message),
            "normalized_score_max":float(np.max(np.abs(grad))/model.total),
            "finite_difference_score_error":gradient_error,
            "starts": [{"tau_ns":float(v.x[1]),"negative_mean_loglik":float(v.fun),"success":bool(v.success),"iterations":int(v.nit)} for v in candidates]}


def source_modules(root,protocol):
    manifest=json.loads((HERE/protocol["upstream"]["source_manifest"]).read_text())
    hashes={}
    for item in manifest:
        if item["repo"]==protocol["upstream"]["repo"] and item["path"] in ["src/spl_fisher_bounds/model.py","src/spl_fisher_bounds/constants.py","LICENSE.txt"]:
            assert sha(root/item["path"])==item["sha256"]
            hashes[item["path"]]=item["sha256"]
    path=root/"src/spl_fisher_bounds/estimators.py"
    assert sha(path)==protocol["upstream"]["estimators_sha256"]
    hashes["src/spl_fisher_bounds/estimators.py"]=sha(path)
    sys.path.insert(0,str(root/"src"))
    return importlib.import_module("spl_fisher_bounds.estimators"),importlib.import_module("spl_fisher_bounds.model"),hashes


def discrete_comparison(record,window,mass,raw_width,K,upstream,models,protocol):
    n,opened,D=record.discrete(window,K)
    width=record.period/K
    pulse=models.EmpiricalPulse(mass,raw_width/width,K)
    phases=np.arange(K,dtype=float)
    pilot=upstream.robust_pilot(n,opened,phases,K,1.0,1.0,5,pulse)
    one=upstream.one_step(pilot,n,opened,(window[1]-window[0])*K,phases,K,1.0,1.0,5,pulse)
    scale=max(1,int(n.sum()))
    def objective(x):
        theta=np.array([np.exp(x[0]),x[1]/width+0.5,np.exp(x[2])*width])
        ll,score=upstream.loglik_and_score(n,opened,theta,phases,K,1.0,1.0,5,pulse)
        return -ll/scale,-score*np.array([theta[0],1/width,theta[2]])/scale
    settings=protocol["solver"]
    start=np.array([np.log(pilot[0]),(pilot[1]-0.5)*width,np.log(pilot[2]/width)])
    bounds=[(-15,5),(start[1]-settings["delay_search_radius_ns"],start[1]+settings["delay_search_radius_ns"]),(-25,2)]
    fits=[]
    for offset in settings["delay_start_offsets_ns"]:
        x=start+np.array([0,offset,0])
        fits.append(minimize(objective,x,jac=True,bounds=bounds,method="L-BFGS-B",
                            options={"maxiter":settings["maximum_iterations"],"ftol":settings["ftol"],"gtol":settings["gtol"]}))
    best=min(fits,key=lambda v:v.fun)
    return {"K":K,"bin_width_ns":width,"dead_bins":D,"dead_bin_duration_ns":D*width,
            "detections_scored":int(n.sum()),"pilot_tau_ns":float((pilot[1]-0.5)*width),
            "one_step_tau_ns":float((one[1]-0.5)*width),"joint_mle_tau_ns":float(best.x[1]),
            "joint_mle_a":float(np.exp(best.x[0])),"joint_mle_b_per_ns":float(np.exp(best.x[2])),
            "joint_mle_success":bool(best.success),"joint_mle_message":str(best.message),
            "normalized_score_max":float(np.max(np.abs(objective(best.x)[1]))),
            "starts": [{"tau_ns":float(v.x[1]),"success":bool(v.success),"negative_mean_loglik":float(v.fun)} for v in fits]}


def geometry_audit(record,window,pulse,edges):
    rng=np.random.default_rng(490205)
    max_err=0.0;cases=0
    # Full sums compare endpoint compression with direct antiderivatives.
    for lo,hi in zip(edges[:-1],edges[1:]):
        exp=record.segment(window,lo,hi)
        for tau in [0.123,2.85,record.period-0.3]:
            direct=np.sum(pulse.primitive(exp.lo_phase+exp.duration-tau)-pulse.primitive(exp.lo_phase-tau))
            error=abs(float(direct)-exp.integral(pulse,tau)[0])
            max_err=max(max_err,error);cases+=1
    assert max_err<1e-5
    return {"full_interval_sum_cases":cases,"max_absolute_pulse_exposure_error":max_err}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--cache-dir",required=True,type=Path)
    parser.add_argument("--upstream-root",required=True,type=Path)
    parser.add_argument("--output",required=True,type=Path)
    args=parser.parse_args()
    if args.output.exists():
        raise FileExistsError("Preserve existing results; choose a new output path")
    protocol_path=HERE/"lidar-range-protocol.json"
    protocol=json.loads(protocol_path.read_text())
    for key in ["high_flux","low_flux","pulse"]:
        assert sha(args.cache_dir/protocol[key]["path"])==protocol[key]["sha256"]
    upstream,models,source_hashes=source_modules(args.upstream_root,protocol)
    high=Record(args.cache_dir/protocol["high_flux"]["path"],1000000)
    low=Record(args.cache_dir/protocol["low_flux"]["path"],1000000)
    calib=loadmat(args.cache_dir/protocol["pulse"]["path"],variable_names=["smoothPulseShape","binRes"])
    smooth=calib["smoothPulseShape"].ravel()
    raw_width=float(calib["binRes"].item())*1e9
    output={"protocol_sha256":sha(protocol_path),"executable_sha256":sha(__file__),
            "argument_sha256":sha(HERE/protocol["ordinary_argument"]),"upstream_hashes":source_hashes,
            "input_hashes":{key:protocol[key]["sha256"] for key in ["high_flux","low_flux","pulse"]},
            "versions":{"python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__},
            "variants":[],"model_certification":False,"range_benefit_demonstrated":False}
    started=time.perf_counter()
    for variant in protocol["pulse_variants"]:
        mass=smooth-smooth.min() if variant=="smooth_min_subtracted" else smooth.copy()
        mass=mass/mass.sum()
        row={"pulse":variant,"high_flux":[]}
        # A coarse histogram pilot for the low-flux guarded continuous likelihood.
        pulse_low=Pulse(mass,raw_width,low.period)
        model_low=Likelihood(low,protocol["low_flux_window_frames"],pulse_low,[protocol["low_flux_guard_ns"],np.inf])
        hist=np.histogram(model_low.phases,bins=625,range=(0,low.period),weights=model_low.counts)[0]
        centers=(np.arange(625)+0.5)*low.period/625
        template=pulse_low.shape(centers,0)[0]
        corr=np.fft.ifft(np.fft.fft(hist)*np.conj(np.fft.fft(template))).real
        pilot=[0.0003,float(np.argmax(corr)*low.period/625),0.00003]
        row["low_flux_provisional_reference"]=fit_continuous(model_low,pilot,protocol)
        for window in protocol["high_flux_windows_frames"]:
            pulse=Pulse(mass,raw_width,high.period)
            native=discrete_comparison(high,window,mass,raw_width,protocol["native_period_bins"],upstream,models,protocol)
            coarse=discrete_comparison(high,window,mass,raw_width,protocol["coarse_period_bins"],upstream,models,protocol)
            pilot=[native["joint_mle_a"],native["joint_mle_tau_ns"],native["joint_mle_b_per_ns"]]
            cutoff=min(200,high.smallest_gap(window))
            hard=fit_continuous(Likelihood(high,window,pulse,[cutoff,np.inf]),pilot,protocol)
            edges=protocol["profile_age_edges_ns"]+[np.inf]
            recovery_model=Likelihood(high,window,pulse,edges,profile=True)
            recovered=fit_continuous(recovery_model,pilot,protocol)
            guarded={str(guard):fit_continuous(Likelihood(high,window,pulse,[guard,np.inf]),pilot,protocol)
                     for guard in protocol["high_flux_guards_ns"]}
            audit=geometry_audit(high,window,pulse,edges)
            item={"window_frames":window,"hard_cutoff_ns":cutoff,"native_discrete":native,"coarse_discrete":coarse,
                  "continuous_hard":hard,"profiled_recovery":recovered,"guarded":guarded,"geometry_audit":audit,
                  "recovery_minus_native_mm":(recovered["tau_ns"]-native["joint_mle_tau_ns"])*C_MM_PER_NS,
                  "recovery_minus_continuous_hard_mm":(recovered["tau_ns"]-hard["tau_ns"])*C_MM_PER_NS}
            row["high_flux"].append(item)
            print(json.dumps({"pulse":variant,"window":window,"recovery_minus_native_mm":item["recovery_minus_native_mm"],
                              "recovery_minus_continuous_hard_mm":item["recovery_minus_continuous_hard_mm"]}),flush=True)
        output["variants"].append(row)
    corrections=np.array([[w["recovery_minus_native_mm"],w["recovery_minus_continuous_hard_mm"]]
                          for v in output["variants"] for w in v["high_flux"]])
    output["development_gate_pass"]=bool(np.all(np.abs(corrections)>=0.2) and np.all(np.sign(corrections)==np.sign(corrections.flat[0])))
    output["elapsed_seconds"]=time.perf_counter()-started
    output["limits"]=protocol["physical_limits"]
    args.output.write_text(json.dumps(output,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"output":str(args.output),"sha256":sha(args.output),"development_gate_pass":output["development_gate_pass"]}),flush=True)


if __name__=="__main__":
    main()
