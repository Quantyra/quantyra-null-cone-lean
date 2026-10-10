"""Frozen S049 finite decision screen; conventional SciPy numerical tails."""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import time

import numpy as np
import scipy
from scipy.optimize import linprog
from scipy.stats import beta, binom

HERE = Path(__file__).resolve().parent


def lower(q, ratio):
    return q/(ratio-(ratio-1)*q)


def upper(q, ratio):
    return ratio*q/(1+(ratio-1)*q)


def sharp_bounds(prob, ratio):
    x, y, z = prob
    if max(x,y) > ratio*min(x,y)+1e-12:
        return None
    return [max(x,y)/(2*max(x,y)+ratio*z),
            ratio*min(x,y)/(2*ratio*min(x,y)+z)]


def lp_bounds(prob, ratio):
    # Charnes-Cooper linear-fractional transformation of weighted probabilities.
    # Variables are scaled weights w_A,w_B,w_C and common normalization c.
    # Normalize sum p_i*w_i=1, enforce x*w_A=y*w_B, and c<=w_i<=R*c.
    x,y,z = prob
    objective = np.array([x,0,0,0])
    equalities = [[x,y,z,0], [x,-y,0,0]]
    inequalities = []
    for i in range(3):
        high = np.zeros(4); high[i] = 1; high[3] = -ratio
        low = np.zeros(4); low[i] = -1; low[3] = 1
        inequalities.extend([high,low])
    vals = []
    for sign in (1,-1):
        sol = linprog(sign*objective, A_ub=inequalities, b_ub=np.zeros(6),
                      A_eq=equalities, b_eq=[1,0], bounds=[(0,None)]*4, method="highs")
        assert sol.success, sol.message
        vals.append(float(objective @ sol.x))
    return vals


def tail_flags(k,n,qlo,qhi,tail_budget):
    return (binom.cdf(k,n,qlo) <= tail_budget) | (binom.sf(k-1,n,qhi) <= tail_budget)


def decisions(counts, ratio, nominal, tolerance, alpha):
    a,b,c = counts.T
    n = a+b+c
    lo,hi = nominal-tolerance, nominal+tolerance
    past = tail_flags(a,n,lower(lo,ratio),upper(hi,ratio),alpha/2)
    pooled = tail_flags(a+b,n,lower(2*lo,ratio),upper(2*hi,ratio),alpha/2)
    marginal = tail_flags(a,n,lower(lo,ratio),upper(hi,ratio),alpha/4)
    marginal |= tail_flags(b,n,lower(lo,ratio),upper(hi,ratio),alpha/4)
    hlo, hhi = lo/(1-lo), hi/(1-hi)
    conditional = tail_flags(a,a+c,lower(hlo,ratio),upper(hhi,ratio),alpha/4)
    conditional |= tail_flags(b,b+c,lower(hlo,ratio),upper(hhi,ratio),alpha/4)
    return {"past_only":past, "pooled":pooled, "balanced_marginal":marginal,
            "balanced_conditional":conditional}


def physical_probabilities(v, ratio, pattern):
    weights = np.ones(3)
    if pattern != "uniform":
        weights[{"past_low":0,"future_low":1,"middle_low":2}[pattern]] = 1/ratio
    masses = np.array([v,v,1-2*v])
    retained = masses*weights
    return retained/retained.sum()


def controls():
    assert not tail_flags(np.array([0]),np.array([0]),0.2,0.4,0.0125)[0]
    x,y,z = Fraction(1,7), Fraction(2,7), Fraction(4,7)
    assert sharp_bounds((x,y,z),Fraction(2)) == [Fraction(1,6),Fraction(1,4)]
    assert [lower(x+y,Fraction(2))/2,upper(x+y,Fraction(2))/2] == [Fraction(3,22),Fraction(3,10)]
    rng = np.random.default_rng(4951)
    checks = 0
    for _ in range(64):
        v = rng.uniform(1/8,3/8)
        r = rng.uniform(1,2)
        p = np.array([v,v,1-2*v])*rng.uniform(1/r,1,3)
        p /= p.sum()
        exact = sharp_bounds(p,r)
        optimized = lp_bounds(p,r)
        assert np.max(np.abs(np.array(exact)-optimized)) < 1e-10
        assert exact[0]-1e-12 <= v <= exact[1]+1e-12
        checks += 1
    counts = np.array([[0,0,0],[10,20,70],[20,10,70],[25,25,50]])
    d = decisions(counts,1.25,.3125,.03125,.05)
    swapped = decisions(counts[:,[1,0,2]],1.25,.3125,.03125,.05)
    for method in ("pooled","balanced_marginal","balanced_conditional"):
        assert np.array_equal(d[method],swapped[method])
    return {"independent_lp_checks":checks,"zero_subset":True,"exchange_invariance":True,
            "exact_population_counterexample":True}


def main():
    start = time.perf_counter()
    raw_protocol = (HERE/"protocol.json").read_bytes()
    p = json.loads(raw_protocol)
    controls_result = controls()
    rep = p["trials_per_stratum"]
    families = len(p["true_volumes"])*len(p["R"])*len(p["detectors"])*len(p["n"])*len(p["nominal_volumes"])
    paired_allowance = np.sqrt(2*np.log(families*3/.01)/rep)
    false_flag_allowance = np.sqrt(np.log(families*4/.01)/(2*rep))
    rows = []
    samples = {}
    index = []
    counter = 0
    for vi,v in enumerate(p["true_volumes"]):
        for ri,ratio in enumerate(p["R"]):
            for di,detector in enumerate(p["detectors"]):
                prob = physical_probabilities(v,ratio,detector)
                population = sharp_bounds(prob,ratio)
                for ni,n in enumerate(p["n"]):
                    rng = np.random.Generator(np.random.PCG64(np.random.SeedSequence([49051010,vi,ri,di,ni])))
                    counts = rng.multinomial(n,prob,size=rep)
                    key = f"s{counter:03d}"
                    counter += 1
                    samples[key] = counts.astype(np.uint16)
                    index.append({"key":key,"v":v,"R":ratio,"detector":detector,"n":n,"probabilities":prob.tolist()})
                    for nominal in p["nominal_volumes"]:
                        flags = decisions(counts,ratio,nominal,p["tolerance"],p["false_flag_budget"])
                        is_null = abs(v-nominal) <= p["tolerance"]
                        rates = {m:float(np.mean(f)) for m,f in flags.items()}
                        if is_null:
                            assert all(x <= p["false_flag_budget"]+false_flag_allowance for x in rates.values())
                        candidate = flags["balanced_conditional"]
                        successes = int(candidate.sum())
                        lower99 = float(beta.ppf(.01,successes,rep-successes+1)) if successes else 0.0
                        gains = {m:float(np.mean(candidate.astype(int)-flags[m].astype(int))-paired_allowance)
                                 for m in flags if m != "balanced_conditional"}
                        local_gate = bool(not is_null and ratio>1 and lower99>=.8 and min(gains.values())>=.1)
                        rows.append({"sample_key":key,"v":v,"R":ratio,"detector":detector,"n":n,"nominal":nominal,
                                     "truth_inside_band":bool(is_null),"flag_probabilities_mc":rates,
                                     "candidate_one_sided_99pct_cp_lower":lower99,
                                     "family_adjusted_paired_gain_lower":gains,
                                     "population_balanced_bounds":population,
                                     "population_pooled_bounds":[lower(prob[0]+prob[1],ratio)/2,upper(prob[0]+prob[1],ratio)/2],
                                     "passes_local_advancement_gate":local_gate})
    np.savez_compressed(HERE/"counts.npz",**samples)
    result = {"protocol_sha256":hashlib.sha256(raw_protocol).hexdigest(),
              "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "counts_sha256":hashlib.sha256((HERE/"counts.npz").read_bytes()).hexdigest(),
              "environment":{"python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__},
              "controls":controls_result,"samples":index,"rows":rows,
              "paired_family_allowance":float(paired_allowance),"false_flag_family_allowance":float(false_flag_allowance),
              "local_gate_passes":sum(x["passes_local_advancement_gate"] for x in rows),
              "strongest_auxiliary_comparison_complete":False,"physical_validation_complete":False,
              "goal_complete":False,"seconds":time.perf_counter()-start}
    (HERE/"results.json").write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"strata":len(index),"decision_rows":len(rows),"controls":controls_result,
                      "local_gate_passes":result["local_gate_passes"],
                      "passing":[x for x in rows if x["passes_local_advancement_gate"]],
                      "seconds":result["seconds"]},indent=2))


if __name__ == "__main__":
    main()
