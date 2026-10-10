"""Saved-count replay and independent multinomial-law integration for S049."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import time

import numpy as np
from scipy.stats import binom

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location("balanced_pilot", HERE/"pilot.py")
pilot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pilot)


def direct_flags(a,b,c,r,nominal):
    """Independent rejection-boundary implementation using integer quantiles.

    Correct quantile ties by direct tails. This does not call pilot.decisions.
    """
    n = a+b+c
    lo,hi = nominal-1/32,nominal+1/32
    def lower_probability(w):
        return w/(w+r*(1-w))
    def upper_probability(w):
        return r*w/(r*w+1-w)
    def tail(k,m,ql,qu,alpha):
        low_cut = binom.ppf(alpha,m,ql).astype(np.int64)
        low_cut -= binom.cdf(low_cut,m,ql)>alpha
        high_cut = binom.isf(alpha,m,qu).astype(np.int64)+1
        high_cut -= binom.sf(high_cut-2,m,qu)<=alpha
        return (k<=low_cut)|(k>=high_cut)
    old = tail(a,n,lower_probability(lo),upper_probability(hi),.025)
    pool = tail(a+b,n,lower_probability(2*lo),upper_probability(2*hi),.025)
    marginal = tail(a,n,lower_probability(lo),upper_probability(hi),.0125)
    marginal |= tail(b,n,lower_probability(lo),upper_probability(hi),.0125)
    conditional = tail(a,a+c,lower_probability(lo/(1-lo)),upper_probability(hi/(1-hi)),.0125)
    conditional |= tail(b,b+c,lower_probability(lo/(1-lo)),upper_probability(hi/(1-hi)),.0125)
    return {"past_only":old,"pooled":pool,"balanced_marginal":marginal,"balanced_conditional":conditional}


def integrate(n,prob,r,nominal):
    # Marginalize A first, then conditional B. No Monte Carlo and no refitting.
    x,y,z = prob
    lo = max(0,int(binom.ppf(1e-14,n,x)))
    hi = min(n,int(binom.isf(1e-14,n,x)))
    omitted = float(binom.cdf(lo-1,n,x)+binom.sf(hi,n,x))
    sums = {m:0.0 for m in ("past_only","pooled","balanced_marginal","balanced_conditional")}
    mass = 0.0
    states = 0
    for a_scalar in range(lo,hi+1):
        b = np.arange(n-a_scalar+1)
        a = np.full_like(b,a_scalar)
        c = n-a-b
        weights = binom.pmf(a_scalar,n,x)*binom.pmf(b,n-a_scalar,y/(y+z))
        flags = direct_flags(a,b,c,r,nominal)
        for method,flag in flags.items():
            sums[method] += float(weights[flag].sum())
        mass += float(weights.sum())
        states += len(b)
    assert abs(mass+omitted-1) < 1e-11
    # Explicit numerical safety margin; this is not interval-arithmetic certification.
    pad = omitted+1e-10
    return {"probabilities":sums,"sum_probability":mass,"omitted_marginal_mass":omitted,
            "numerical_comparison_pad":pad,"enumerated_states":states,
            "status":"direct finite-law floating-point calculation, not exact rational or formal certification"}


def order_control():
    rng = np.random.default_rng(490512)
    for _ in range(12):
        uv = rng.random((96,2))
        points = np.vstack(([[0,0],[.5,.5]],uv))
        relation = np.all(points[:,None,:]<points[None,:,:],axis=2)
        past = relation[0,2:] & relation[2:,1]
        future = relation[1,2:]
        assert not np.any(past&future)
        assert np.array_equal(past,np.all(uv<.5,axis=1))
        assert np.array_equal(future,np.all(uv>.5,axis=1))
        counts = [past.sum(),future.sum(),np.count_nonzero(~(past|future))]
        permutation = np.r_[0,1,rng.permutation(96)+2]
        permuted = relation[np.ix_(permutation,permutation)]
        assert counts[:2] == [(permuted[0,2:]&permuted[2:,1]).sum(),permuted[1,2:].sum()]
        swapped = np.all(points[:,None,::-1]<points[None,:,::-1],axis=2)
        assert np.array_equal(relation,swapped)
    return 12


def main():
    started=time.perf_counter()
    raw = (HERE/"results.json").read_bytes()
    results=json.loads(raw)
    protocol_raw=(HERE/"protocol.json").read_bytes()
    frozen=subprocess.check_output(["git","show","5ea83e4:applications/balanced-volume/protocol.json"],cwd=REPO)
    assert frozen==protocol_raw
    assert results["protocol_sha256"]==hashlib.sha256(protocol_raw).hexdigest()
    assert results["script_sha256"]==hashlib.sha256((HERE/"pilot.py").read_bytes()).hexdigest()
    assert results["counts_sha256"]==hashlib.sha256((HERE/"counts.npz").read_bytes()).hexdigest()
    counts_archive=np.load(HERE/"counts.npz",allow_pickle=False)
    protocol=json.loads(protocol_raw)
    # Replay all pilot decisions without resampling.
    for row in results["rows"]:
        counts=counts_archive[row["sample_key"]].astype(np.int64)
        flags=pilot.decisions(counts,row["R"],row["nominal"],protocol["tolerance"],.05)
        for method,f in flags.items():
            assert float(f.mean())==row["flag_probabilities_mc"][method]
    # Verify independent quantile decisions on all count outcomes for small n.
    check_rows=0
    for n in (0,1,4,16,48):
        counts=np.array([[a,b,n-a-b] for a in range(n+1) for b in range(n-a+1)],dtype=np.int64)
        for r in (1,1.125,1.25,2):
            for nominal in (.25,.3125):
                ref=pilot.decisions(counts,r,nominal,1/32,.05)
                alt=direct_flags(*counts.T,r,nominal)
                for method in ref:
                    assert np.array_equal(ref[method],alt[method]),(n,r,nominal,method)
                check_rows+=len(counts)
    lookup={s["key"]:s for s in results["samples"]}
    confirmations=[]
    for row in results["rows"]:
        if row["passes_local_advancement_gate"]:
            result=integrate(row["n"],lookup[row["sample_key"]]["probabilities"],row["R"],row["nominal"])
            rates=result["probabilities"]
            assert rates["balanced_conditional"]>.8
            assert min(rates["balanced_conditional"]-rates[m] for m in rates if m!="balanced_conditional")>.1
            confirmations.append({"sample_key":row["sample_key"],"v":row["v"],"R":row["R"],
                                  "detector":row["detector"],"n":row["n"],"nominal":row["nominal"],**result})
            print(json.dumps({"confirmed":row["sample_key"],"probabilities":rates}),flush=True)
    audit={"status":"pass","results_sha256":hashlib.sha256(raw).hexdigest(),
           "replayed_decision_rows":len(results["rows"]),"independent_small_count_cases":check_rows,
           "order_observation_controls":order_control(),"confirmations":confirmations,
           "seconds":time.perf_counter()-started,"goal_complete":False}
    (HERE/"audit.json").write_text(json.dumps(audit,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({k:v for k,v in audit.items() if k!="confirmations"},indent=2))


if __name__=="__main__":
    main()
