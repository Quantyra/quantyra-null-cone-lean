"""Exact arithmetic sanity checks for S038; no Lean invocation or proof claim."""
from fractions import Fraction as Q
import argparse
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run():
    epsilon = Q(1, 4)
    assert Q(1, 2) <= 1-epsilon <= 1+epsilon <= Q(3, 2)
    assert 8*epsilon**2 == Q(1, 2) <= 4  # squared gradient and Lipschitz bounds
    mean_f = Q(1)-Q(1)
    assert mean_f == 0
    half_integral_f = Q(1, 4)-Q(1, 2)
    physical_mass = Q(1, 4)+epsilon*half_integral_f**2
    assert physical_mass == Q(17, 64)
    assert physical_mass-Q(1, 4) == Q(1, 64)
    assert Q(3, 4)/(1+epsilon) == Q(3, 5)
    assert Q(3, 4)/(1-epsilon) == 1
    # Squaring 1+(2/5)x gives 1+(4/5)x+(4/25)x^2.
    assert Q(4, 25)*epsilon <= Q(1, 5)
    assert Q(2, 5)*epsilon*Q(1, 3) == Q(1, 30)

    def lower(x, ratio):
        return x/(ratio-(ratio-1)*x)

    def upper(x, ratio):
        return ratio*x/(1+(ratio-1)*x)

    cases = 0
    for ratio in (Q(1), Q(5, 4), Q(5, 3), Q(2), Q(10)):
        for k in range(101):
            p = Q(k, 100)
            # Algebraic inverses, endpoint coverage and interior ordering.
            assert lower(upper(p, ratio), ratio) == p
            assert upper(lower(p, ratio), ratio) == p
            assert 0 <= lower(p, ratio) <= p <= upper(p, ratio) <= 1
            for wa, wb in ((Q(1),ratio),(ratio,Q(1)),(Q(1),Q(1))):
                theta = wa*p/(wa*p+wb*(1-p))
                assert lower(theta, ratio) <= p <= upper(theta, ratio)
                cases += 1

    # Simpson diagnostic; the analytic proper-time separation uses the exact bound above.
    panels = 4096
    def integrand(t):
        return math.sqrt(2*(1+float(epsilon)*(2*t-1)**2))
    diag = (integrand(0)+integrand(1)+sum(
        (4 if k % 2 else 2)*integrand(k/panels) for k in range(1,panels)
    ))/(3*panels)
    bound = math.sqrt(2)/30
    assert diag-math.sqrt(2) > bound
    return {
        "story": "S038", "status": "passed", "check_kind": "arithmetic_sanity_not_formal_proof",
        "rho_range": ["3/4", "5/4"], "gradient_squared_bound": "1/2",
        "detection_range": ["3/5", "1"], "observed_intensity_both_models": "3/4",
        "physical_interval_volumes": ["1/4", "17/64"], "detected_interval_mass": "1/4",
        "proper_time_separation_strict_lower": "sqrt(2)/30",
        "diagonal_length_numerical_diagnostic": diag,
        "selection_bound_cases": cases, "lean_invocations": 0,
        "sources": {str(p.relative_to(ROOT)).replace('\\','/'): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in (Path(__file__).resolve(), ROOT/'notes/physical-observation-identifiability.md')},
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
