"""Independent optimizer audit and direct multinomial-law comparison."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import time

import numpy as np
from scipy.optimize import brentq, linprog, minimize
from scipy.stats import binom, norm

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("auxiliary", HERE/"auxiliary.py")
aux = importlib.util.module_from_spec(spec)
spec.loader.exec_module(aux)


def reference_ratio(p, n, ratio, alpha):
    """Invert signed studentized moment by scalar roots, not quadratic formula."""
    x, y, _ = p
    critical = norm.isf(alpha/2)
    k = critical**2/(n+critical**2)
    def score(r):
        return (x*r-y)/np.sqrt(x*r*r+y)
    low, high = 1/ratio, ratio
    if score(low)>np.sqrt(k) or score(high)<-np.sqrt(k):
        return None
    if score(low)<-np.sqrt(k):
        low = brentq(lambda r: score(r)+np.sqrt(k), low, high, xtol=1e-14)
    if score(high)>np.sqrt(k):
        high = brentq(lambda r: score(r)-np.sqrt(k), low, high, xtol=1e-14)
    return low, high


def reference_lp(p, ratio, interval, f, maximum):
    """Charnes-Cooper global LP; returns objective and recovered weights."""
    inequalities = []
    for j in range(3):
        row = np.zeros(4); row[j]=1; row[3]=-ratio
        inequalities.append(row)
        row = np.zeros(4); row[j]=-1; row[3]=1
        inequalities.append(row)
    low, high = interval
    inequalities += [np.array([1.,-high,0.,0.]), np.array([-1.,low,0.,0.])]
    objective = np.r_[p*f, 0.]
    sol = linprog((-1 if maximum else 1)*objective, A_ub=inequalities,
                  b_ub=np.zeros(8), A_eq=[np.r_[p,0.]], b_eq=[1.],
                  bounds=[(0,None)]*4, method="highs")
    assert sol.success, sol.message
    return float(objective@sol.x), sol.x[:3]/sol.x[3]


def controls():
    rng = np.random.default_rng(4905101042)
    maximum_error = 0.
    root_cases = 0
    lp_cases = 0
    slsqp_cases = 0
    slsqp_status_failures = []
    targets = {"past": np.array([1.,0.,0.]), "future": np.array([0.,1.,0.]),
               "pooled": np.array([.5,.5,0.])}
    # These controls do not read pilot samples or compute their decision rates.
    for j in range(160):
        p = rng.dirichlet([2.,2.,2.])
        n = int(rng.integers(20,10001))
        ratio = float(rng.uniform(1.01,5.))
        alpha = float(rng.choice([.01,.0125,.025,.04]))
        ref = reference_ratio(p, n, ratio, alpha)
        low, high, empty = aux.ratio_interval(p[None,:], n, ratio, alpha)
        assert bool(empty[0]) == (ref is None)
        root_cases += 1
        if ref is None:
            continue
        assert np.max(np.abs(np.array(ref)-[low[0],high[0]])) < 1e-11
        for target, f in targets.items():
            for maximum in (False,True):
                w = aux.optimizer_weights(low, high, ratio, target, maximum)
                q, variance = aux.objective_variance(p[None,:], w, f)
                ref_q, ref_w = reference_lp(p, ratio, ref, f, maximum)
                err = abs(q[0]-ref_q)
                maximum_error = max(maximum_error, err)
                assert err < 2e-9
                assert np.all(w>=1-1e-10) and np.all(w<=ratio+1e-10)
                critical = norm.isf(alpha/2)
                a,b,c = w[0]
                moment = a*p[0]-b*p[1]
                second = a*a*p[0]+b*b*p[1]
                assert moment**2 <= critical**2/n*(second-moment**2)+1e-10
                lp_cases += 1
                if j<24:
                    sign = -1 if maximum else 1
                    def objective(t):
                        return sign*float(np.sum(p*t*f)/np.sum(p*t))
                    def gradient(t):
                        denominator = np.sum(p*t)
                        numerator = np.sum(p*t*f)
                        return sign*(p*f*denominator-numerator*p)/denominator**2
                    def constraint(t):
                        h = t[0]*p[0]-t[1]*p[1]
                        return t[0]**2*p[0]+t[1]**2*p[1]-(1+n/critical**2)*h*h
                    def constraint_gradient(t):
                        h = t[0]*p[0]-t[1]*p[1]
                        factor = 1+n/critical**2
                        return np.array([2*t[0]*p[0]-2*factor*h*p[0],
                                         2*t[1]*p[1]+2*factor*h*p[1],0.])
                    rmid = np.mean(ref)
                    bmid = .5*(max(1,1/rmid)+min(ratio,ratio/rmid))
                    initial = [rmid*bmid,bmid,(1+ratio)/2]
                    sol = minimize(objective,initial,jac=gradient,method="SLSQP",bounds=[(1,ratio)]*3,
                                   constraints={"type":"ineq","fun":constraint,"jac":constraint_gradient},
                                   options={"ftol":1e-10,"maxiter":500})
                    if not sol.success:
                        slsqp_status_failures.append({"case":j,"target":target,"maximum":maximum,
                                                      "message":sol.message,"constraint_residual":float(constraint(sol.x)),
                                                      "objective_error":float(abs(sign*sol.fun-q[0]))})
                    assert constraint(sol.x)/(1+n/critical**2) >= -1e-9, (j,target,maximum,constraint(sol.x),abs(sign*sol.fun-q[0]))
                    assert abs(sign*sol.fun-q[0])<2e-7, (j,target,maximum,sol.message)
                    slsqp_cases += 1
    # Include rare-cell and degenerate sample behavior, exchange, and R=1.
    for p in (np.array([.0001,.0002,.9997]), np.array([.0001,.4,.5999]),
              np.array([.4,.0001,.5999]), np.array([.25,.25,.5])):
        for n in (2,10,100,10000):
            ref = reference_ratio(p,n,2,.025)
            lo,hi,empty = aux.ratio_interval(p[None,:],n,2,.025)
            assert bool(empty[0]) == (ref is None)
            if ref is not None:
                assert np.max(np.abs(np.array(ref)-[lo[0],hi[0]]))<1e-10
            root_cases += 1
    counts = np.array([[0,0,0],[0,2,4],[25,25,50],[13,30,57],[300,140,560]])
    for target in targets:
        lo,hi,empty,guard = aux.intervals(counts,2,.025,.0125,target)
        assert np.array_equal(guard, [True,True,False,False,False])
        assert np.all(lo[guard]==1/8) and np.all(hi[guard]==3/8)
        opposite = {"past":"future","future":"past","pooled":"pooled"}[target]
        swapped = aux.intervals(counts[:,[1,0,2]],2,.025,.0125,opposite)
        assert np.allclose(lo,swapped[0],rtol=0,atol=1e-12)
        assert np.allclose(hi,swapped[1],rtol=0,atol=1e-12)
    p = np.array([[.25,.25,.5]])
    lo,hi,empty = aux.ratio_interval(p,100,1,.025)
    assert not empty[0] and lo[0]==hi[0]==1
    for target,f in targets.items():
        for maximum in (False,True):
            weights = aux.optimizer_weights(lo,hi,1,target,maximum)
            assert np.array_equal(weights,np.ones((1,3)))
            q,var = aux.objective_variance(p,weights,f)
            assert q[0]==.25
            assert abs(var[0]-(.0625 if target=="pooled" else .1875))<1e-15
    return {"root_cases":root_cases,"lp_extrema":lp_cases,"slsqp_extrema":slsqp_cases,
            "maximum_lp_objective_error":maximum_error,"slsqp_status_failures":slsqp_status_failures,
            "rare_cell_zero_exchange_R1_checks":True}


def law_comparison(sample, protocol):
    n = sample["n"]
    p = sample["probabilities"]
    ratio = sample["R"]
    nominal, tolerance = 5/16, 1/32
    a_low = max(1,int(binom.ppf(1e-14,n,p[0])))
    a_high = min(n-2,int(binom.isf(1e-14,n,p[0])))
    accum = {"balanced_conditional":0.}
    for label in protocol["allocations"]:
        for target in protocol["target_representations"]:
            for convention in ("unresolved_on_empty","flag_on_empty","empty"):
                accum[label+"/"+target+"/"+convention] = 0.
    mass = 0.
    guards_mass = 0.
    pairs = 0
    pilot = aux.sibling("pilot")
    for a in range(a_low,a_high+1):
        b = np.arange(n-a+1)
        counts = np.column_stack((np.full_like(b,a),b,n-a-b))
        probabilities = binom.pmf(a,n,p[0])*binom.pmf(b,n-a,p[1]/(1-p[0]))
        mass += float(probabilities.sum())
        pairs += len(b)
        flags = pilot.decisions(counts,ratio,nominal,tolerance,.05)["balanced_conditional"]
        accum["balanced_conditional"] += float(probabilities@flags)
        for label,allocation in protocol["allocations"].items():
            for target in protocol["target_representations"]:
                regular,flag_empty,empty,guard = aux.flags(counts,ratio,nominal,tolerance,allocation,target)
                for convention,decision in (("unresolved_on_empty",regular),("flag_on_empty",flag_empty),("empty",empty)):
                    accum[label+"/"+target+"/"+convention] += float(probabilities@decision)
        guards_mass += float(probabilities@guard)
    omitted = float(binom.cdf(a_low-1,n,p[0])+binom.sf(a_high,n,p[0]))
    assert abs(mass+omitted-1)<1e-11
    return {"sample_key":sample["key"],"n":n,"R":ratio,"detector":sample["detector"],
            "probabilities":accum,"count_pairs":pairs,"included_probability":mass,
            "omitted_marginal_probability":omitted,"guard_probability":guards_mass,
            "numerical_allowance":1e-10+omitted,
            "interval_arithmetic_or_formal_certificate":False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--controls-only",action="store_true")
    parser.add_argument("--freeze-commit")
    args = parser.parse_args()
    started = time.perf_counter()
    check = controls()
    if args.controls_only:
        print(json.dumps(check,indent=2))
        return
    assert args.freeze_commit, "Supply the pushed pre-evaluation freeze commit"
    root = HERE.parent.parent
    for name in ("auxiliary-protocol.json","auxiliary.py","auxiliary-audit.py"):
        frozen = subprocess.check_output(["git","show",args.freeze_commit+":applications/balanced-volume/"+name],cwd=root)
        assert frozen == (HERE/name).read_bytes(), name
    protocol = json.loads((HERE/"auxiliary-protocol.json").read_bytes())
    result = json.loads((HERE/"auxiliary-results.json").read_bytes())
    for name,key in (("auxiliary-protocol.json","protocol_sha256"),("auxiliary.py","script_sha256"),
                     ("results.json","original_results_sha256"),("counts.npz","counts_sha256")):
        assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==result[key]
    originals = json.loads((HERE/"results.json").read_bytes())
    samples = {x["key"]:x for x in originals["samples"]}
    laws = []
    for key in ("s040","s053","s057"):
        law = law_comparison(samples[key],protocol)
        laws.append(law)
        print(json.dumps({"completed":key,"candidate":law["probabilities"]["balanced_conditional"],
                          "best_auxiliary":max(v for k,v in law["probabilities"].items() if k.endswith("flag_on_empty"))}),flush=True)
    output = {"freeze_commit":args.freeze_commit,"controls":check,"law_comparisons":laws,
              "auxiliary_results_sha256":hashlib.sha256((HERE/"auxiliary-results.json").read_bytes()).hexdigest(),
              "audit_script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "seconds":time.perf_counter()-started}
    (HERE/"auxiliary-audit.json").write_text(json.dumps(output,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"controls":check,"seconds":output["seconds"]},indent=2))


if __name__ == "__main__":
    main()
