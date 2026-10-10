"""Exact composite-binomial calibration for a finite multinomial reference."""
from bisect import bisect_left, bisect_right
from fractions import Fraction
from pathlib import Path
import hashlib
import importlib.util
import json
import platform
import time

import numpy as np
import scipy
from scipy.stats import binom

HERE = Path(__file__).resolve().parent


def sibling(name):
    spec = importlib.util.spec_from_file_location(name, HERE/(name+".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def endpoint_probabilities(ratio, lo=Fraction(9,32), hi=Fraction(11,32)):
    return lo/(lo+ratio*(1-2*lo)), ratio*hi/(ratio*hi+1-2*hi)


def cdf_value(cdf, k):
    return 0 if k<0 else cdf[k]


def critical_bounds(cdflo, denlo, cdfhi, denhi, budget):
    a = bisect_right(cdflo, (denlo*budget.numerator)//budget.denominator)-1
    b = bisect_left(cdfhi, denhi-(denhi*budget.numerator)//budget.denominator)+1
    return a,b


def endpoint_size(cdf, denominator, a, b):
    return cdf_value(cdf,a)+denominator-cdf_value(cdf,b-1)


def calibrated_row(cdflo, denlo, cdfhi, denhi, beta):
    a0,b0 = critical_bounds(cdflo,denlo,cdfhi,denhi,beta/2)
    a,b = critical_bounds(cdflo,denlo,cdfhi,denhi,beta)
    while True:
        left = endpoint_size(cdflo,denlo,a,b)
        right = endpoint_size(cdfhi,denhi,a,b)
        if (left*beta.denominator <= denlo*beta.numerator and
                right*beta.denominator <= denhi*beta.numerator):
            break
        # The low and high boundary scores are their respective endpoint tails.
        left_score = cdf_value(cdflo,a)*denhi
        right_score = (denhi-cdf_value(cdfhi,b-1))*denlo
        if left_score>=right_score:
            a -= 1
        if right_score>=left_score:
            b += 1
        assert a>=a0 and b<=b0, "Calibration discarded an original candidate rejection"
    assert a>=a0 and b<=b0
    return [a,b,a0,b0], max(left/denlo,right/denhi)


def next_cdf(previous, denominator, q):
    s,d = q.numerator,q.denominator
    out = [(d-s)*previous[0]]
    out.extend((d-s)*previous[k]+s*previous[k-1] for k in range(1,len(previous)))
    out.append(denominator*d)
    return out,denominator*d


def make_table(n, ratio, beta=Fraction(1,40)):
    qlo,qhi = endpoint_probabilities(ratio)
    cdflo,cdfhi,denlo,denhi = [1],[1],1,1
    rows = []
    maximum_size = 0.
    for m in range(n+1):
        if m:
            cdflo,denlo = next_cdf(cdflo,denlo,qlo)
            cdfhi,denhi = next_cdf(cdfhi,denhi,qhi)
        row,size = calibrated_row(cdflo,denlo,cdfhi,denhi,beta)
        rows.append(row)
        maximum_size = max(maximum_size,size)
    return {"n_max":n,"R":str(ratio),"qlo":str(qlo),"qhi":str(qhi),
            "pair_budget":str(beta),"rows":rows,"maximum_endpoint_size_float_summary":maximum_size,
            "exact_integer_endpoint_size_checks":2*(n+1),"exact_candidate_inclusion_checks":n+1}


def decisions(counts, table, candidate=False):
    counts = np.asarray(counts,dtype=int)
    critical = np.asarray(table["rows"],dtype=int)
    offset = 2 if candidate else 0
    flags = np.zeros(len(counts),dtype=bool)
    for j in (0,1):
        m = counts[:,j]+counts[:,2]
        a,b = critical[m,offset],critical[m,offset+1]
        flags |= (counts[:,j]<=a) | (counts[:,j]>=b)
    return flags


def finite_law(sample,table):
    n,p = sample["n"],sample["probabilities"]
    low = max(0,int(binom.ppf(1e-14,n,p[0])))
    high = min(n,int(binom.isf(1e-14,n,p[0])))
    mass=reference=candidate=extra=0.
    pairs=0
    for a in range(low,high+1):
        b = np.arange(n-a+1)
        counts = np.column_stack((np.full_like(b,a),b,n-a-b))
        probabilities = binom.pmf(a,n,p[0])*binom.pmf(b,n-a,p[1]/(1-p[0]))
        reference_flags = decisions(counts,table)
        candidate_flags = decisions(counts,table,candidate=True)
        assert not np.any(candidate_flags & ~reference_flags)
        mass += float(probabilities.sum())
        reference += float(probabilities@reference_flags)
        candidate += float(probabilities@candidate_flags)
        extra += float(probabilities@(reference_flags & ~candidate_flags))
        pairs += len(b)
    omitted = float(binom.cdf(low-1,n,p[0])+binom.sf(high,n,p[0]))
    assert abs(mass+omitted-1)<1e-11
    return {"candidate_probability":candidate,"reference_probability":reference,
            "additional_correct_flag_probability":extra,"count_pairs":pairs,
            "included_probability":mass,"omitted_marginal_probability":omitted,
            "numerical_allowance":1e-10+omitted,"power_is_exact_rational":False}


def main():
    started=time.perf_counter()
    protocol_bytes=(HERE/"finite-reference-protocol.json").read_bytes()
    protocol=json.loads(protocol_bytes)
    original_bytes=(HERE/"results.json").read_bytes()
    assert hashlib.sha256(original_bytes).hexdigest()==protocol["input_results_sha256"]
    original=json.loads(original_bytes)
    assert hashlib.sha256((HERE/"counts.npz").read_bytes()).hexdigest()==original["counts_sha256"]
    data=np.load(HERE/"counts.npz",allow_pickle=False)
    samples={s["key"]:s for s in original["samples"]}
    tables={}
    cases=[]
    pilot=sibling("pilot")
    for key in protocol["cases"]:
        sample=samples[key]
        ratio=Fraction(str(sample["R"]))
        table_key=str(ratio)+"/"+str(sample["n"])
        if table_key not in tables:
            tables[table_key]=make_table(sample["n"],ratio)
            print(json.dumps({"table_complete":table_key,"maximum_endpoint_size":tables[table_key]["maximum_endpoint_size_float_summary"]}),flush=True)
        table=tables[table_key]
        counts=data[key]
        reference=decisions(counts,table)
        candidate=decisions(counts,table,candidate=True)
        original_flags=pilot.decisions(counts,sample["R"],5/16,1/32,.05)["balanced_conditional"]
        assert np.array_equal(candidate,original_flags)
        assert not np.any(candidate & ~reference)
        law=finite_law(sample,table)
        cases.append({"sample":sample,"table":table_key,
                      "candidate_mc":float(candidate.mean()),"reference_mc":float(reference.mean()),
                      "law":law})
        print(json.dumps({"case":key,"candidate":law["candidate_probability"],"reference":law["reference_probability"]}),flush=True)
    result={"protocol_sha256":hashlib.sha256(protocol_bytes).hexdigest(),
            "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "original_results_sha256":hashlib.sha256(original_bytes).hexdigest(),
            "counts_sha256":original["counts_sha256"],"tables":tables,"cases":cases,
            "environment":{"python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__},
            "candidate_can_have_positive_power_advantage_over_reference":False,
            "globally_optimal_multinomial_test_claimed":False,
            "physical_validation_complete":False,"goal_complete":False,
            "seconds":time.perf_counter()-started}
    (HERE/"finite-reference-results.json").write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"seconds":result["seconds"],"cases":len(cases)}))


if __name__=="__main__":
    main()
