"""Independent integer certificates for the calibrated finite reference."""
from fractions import Fraction
from math import comb
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import time

import numpy as np

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("finite_reference",HERE/"finite_reference.py")
ref=importlib.util.module_from_spec(spec)
spec.loader.exec_module(ref)


def coefficient_cdf(m,q):
    """Independent binomial-mass recurrence at fixed m, not Bernoulli-step CDF."""
    s,d=q.numerator,q.denominator
    term=(d-s)**m
    total=term
    cdf=[total]
    for k in range(m):
        numerator=term*(m-k)*s
        denominator=(k+1)*(d-s)
        term,remainder=divmod(numerator,denominator)
        assert remainder==0
        total+=term
        cdf.append(total)
    assert total==d**m
    return cdf,total


def audit_table(table):
    qlo,qhi=Fraction(table["qlo"]),Fraction(table["qhi"])
    beta=Fraction(table["pair_budget"])
    maximum=0.
    for m,(a,b,a0,b0) in enumerate(table["rows"]):
        flo,dlo=coefficient_cdf(m,qlo)
        fhi,dhi=coefficient_cdf(m,qhi)
        def cdf(values,k):
            return 0 if k<0 else values[k]
        assert -1<=a<b<=m+1
        for values,den in ((flo,dlo),(fhi,dhi)):
            size=cdf(values,a)+den-cdf(values,b-1)
            assert size*beta.denominator <= den*beta.numerator
            maximum=max(maximum,size/den)
        assert a>=a0 and b<=b0
        # Check original threshold bounds directly, including maximality.
        assert cdf(flo,a0)*2*beta.denominator<=dlo*beta.numerator
        if a0<m:
            assert cdf(flo,a0+1)*2*beta.denominator>dlo*beta.numerator
        assert (dhi-cdf(fhi,b0-1))*2*beta.denominator<=dhi*beta.numerator
        if b0>0:
            assert (dhi-cdf(fhi,b0-2))*2*beta.denominator>dhi*beta.numerator
        if m<=24:
            for q,values in ((qlo,flo),(qhi,fhi)):
                independent=0
                for k in range(m+1):
                    independent+=comb(m,k)*q.numerator**k*(q.denominator-q.numerator)**(m-k)
                    assert independent==values[k]
    return {"rows":len(table["rows"]),"integer_endpoint_size_checks":2*len(table["rows"]),
            "integer_inclusion_checks":len(table["rows"]),"maximum_endpoint_size_float_summary":maximum}


def controls():
    tests=0
    for ratio in (Fraction(1),Fraction(5,4),Fraction(2)):
        table=ref.make_table(24,ratio)
        audit_table(table)
        for n in range(25):
            counts=np.array([[a,b,n-a-b] for a in range(n+1) for b in range(n-a+1)])
            reference=ref.decisions(counts,table)
            candidate=ref.decisions(counts,table,candidate=True)
            assert not np.any(candidate & ~reference)
            assert np.array_equal(reference,ref.decisions(counts[:,[1,0,2]],table))
            tests+=len(counts)
        assert not ref.decisions(np.array([[0,0,0]]),table)[0]
    return {"exhaustive_count_cases":tests,"small_integer_tables":3,
            "exchange_zero_and_nesting":True}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--controls-only",action="store_true")
    parser.add_argument("--freeze-commit")
    args=parser.parse_args()
    started=time.perf_counter()
    check=controls()
    if args.controls_only:
        print(json.dumps(check));return
    assert args.freeze_commit
    for name in ("finite-reference-protocol.json","finite_reference.py","finite_reference_audit.py"):
        frozen=subprocess.check_output(["git","show",args.freeze_commit+":applications/balanced-volume/"+name],cwd=HERE.parent.parent)
        assert frozen==(HERE/name).read_bytes(),name
    raw=(HERE/"finite-reference-results.json").read_bytes()
    result=json.loads(raw)
    for name,key in (("finite-reference-protocol.json","protocol_sha256"),("finite_reference.py","script_sha256"),
                     ("results.json","original_results_sha256"),("counts.npz","counts_sha256")):
        assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==result[key]
    tables={}
    for key,table in result["tables"].items():
        tables[key]=audit_table(table)
        print(json.dumps({"table_audited":key,**tables[key]}),flush=True)
    # Independent earlier finite-law audit supplies an unchanged candidate value.
    previous=json.loads((HERE/"auxiliary-audit.json").read_bytes())
    old_laws={r["sample_key"]:r for r in previous["law_comparisons"]}
    for case in result["cases"]:
        key=case["sample"]["key"]
        old=old_laws[key]["probabilities"]["balanced_conditional"]
        assert abs(case["law"]["candidate_probability"]-old)<1e-10
        assert case["law"]["reference_probability"]>=case["law"]["candidate_probability"]
        assert abs(case["law"]["reference_probability"]-case["law"]["candidate_probability"]-
                   case["law"]["additional_correct_flag_probability"])<1e-10
    output={"freeze_commit":args.freeze_commit,"controls":check,"tables":tables,
            "result_sha256":hashlib.sha256(raw).hexdigest(),
            "audit_script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "candidate_law_agrees_with_prior_independent_audit":True,
            "certification_scope":"Exact integer endpoint size and nesting for all stored conditional-size rows; ordinary proof for continuous nuisance coverage and all n. Power remains floating point. No Lean claim.",
            "seconds":time.perf_counter()-started}
    (HERE/"finite-reference-audit.json").write_text(json.dumps(output,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"seconds":output["seconds"],"controls":check}))


if __name__=="__main__":
    main()
