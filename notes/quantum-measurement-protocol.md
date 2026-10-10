# Frozen S047 bounded evaluation

2026-10-10. Freeze this protocol and executable in Git before executing the
study. [Model and ordinary proof](quantum-measurement-model.md),
[source comparison](quantum-measurement-sources.md). There is one candidate
and no data-driven revision. The source gate already proves that the proposed
report equals generic calibrated exact-binomial projection for every input.
This evaluation checks that implementation, exact small-sample coverage and
representative cost; it cannot turn the algebraic identity into an advantage.

## Fixed grids and observations

Use a=1/2, alpha=1/20, four marginal budgets delta=1/80 and the existing
outward endpoint grid of denominator 65,536 with exact integer tail checks.
Use equal calibration block sizes m+=m-=m. The nominal target is theta
half-width at most 1/10, compared with the no-data radius one.

Twenty-five main parameter strata are the Cartesian product

    p in {0, 1/5, 1/2, 4/5, 1};
    (eta+,eta-) in {(1/2,1/2), (1/2,1), (1,1/2), (1,1), (3/5,4/5)}.

Two withheld interior strata are `(p,eta+,eta-)=(1/3,2/3,5/6)` and
`(2/3,5/6,2/3)`. Their observations are not used to tune the code, method,
budgets or thresholds. No random-data pilot precedes this freeze.

For **exact finite-law coverage**, n,m range independently over {0,4,12}.
Enumerate every possible complete count tuple in all nine budgets. There
are 20,865 tuples, reused across the 27 parameter strata, making 243 exact
coverage cells. Zero-probability tuples remain part of the implementation
check. Use integer multinomial/binomial weights over a common rational
denominator to calculate coverage and fallback probability without Monte
Carlo error. Require coverage >=19/20 in every cell. The finite grid does
not establish the uniform theorem; the ordinary argument does. Expected
half-widths may be reported using floating arithmetic and must be labeled
as such, separately from exact coverage fractions.

For **representative cost and width diagnostics**, use all 27 strata at
`(n,m)=(128,0),(512,128),(2048,2048)`: 81 cases. Set observed probe counts
by largest-remainder rounding of n times the three probabilities, with
category index breaking ties. Calibration clicks are floor(m eta+),
floor(m eta-). These deterministic near-mean counts are neither random
replicates nor coverage/expected-error estimates. They exercise no-calibration,
unequal-budget and larger-budget behavior, including state/detector boundaries.
The largest experiment would require 6,144 total preparations. Report actual
wall time and RSS; no laboratory runtime is inferred from computational cost.

## Matched comparisons and decision thresholds

Every count tuple compares the candidate formula to a separately implemented
one-variable linear-feasibility baseline after eliminating bounded detector
nuisances. It receives exactly the same four observations, efficiency class,
error allocation and fallback. Require exact endpoint/fallback equality as
an implementation invariant. This is the applicable transformed
exact-binomial comparator for the full-record experiment. The detections-only
bounded-selection formula is a coarser-data comparison, not the principal
baseline.

At each of the 81 cost cases additionally record:

- Known-detector oracle: same probe data with efficiencies supplied exactly
  and two marginal failure budgets alpha/2; a diagnostic with extra information.
- Bias-ignoring diagnostic: conditional positive fraction among detections
  (use 1/2 if there are none), and its ordinary 95% binomial interval. Its
  nominal coverage is for the conditional parameter, not generally p.
- Joint-tomography point fit: the same full likelihood and loss-only class,
  three fixed SLSQP starts, analytic gradient, maximum 300 iterations each,
  ftol=1e-10. Save every convergence result and feasible returned candidate.
  The best finite feasible candidate is a local-fit diagnostic; there is no
  global-maximum or uniform-bootstrap-coverage claim. The NIST paper's
  likelihood is specialized; its package/optimizer is not reproduced.

For a new quantum-method investment, require all 27 largest-budget diagnostic
reports to meet the nominal radius 1/10 **and** at least 10% mean radius
improvement over the matched established report at that budget, without
coverage failure. Near-mean width success alone is insufficient evidence of
probabilistic utility. The identity established before data already rules out
the improvement requirement. Therefore the intended disposition is a bounded
known-method transfer, subject to finding no implementation/proof defect;
do not expand the experiment merely to seek a positive distinction.

## Resource, custody and audit

One worker; 900 seconds total wall ceiling, 768 MiB RSS/commit ceiling, with
the existing Windows job-object supervisor. Retain protocol/source commit,
software versions, all exact reports/coverage cells, diagnostic counts,
optimizer outcomes, timers and resource outcome. Exact enumeration needs no
seed. Record failures without overwriting them; an execution defect may be
repaired in a new version while preserving the frozen scientific design.

An independent audit must recheck every rational marginal tail, comparator
identity, exact coverage/fallback sum and deterministic cost input, and
verify the raw artifact inventory against Git. Verify the joint-likelihood
gradient on deterministic pre-freeze fixtures and re-evaluate reported fit
likelihoods. No repeated full test campaign is required without a new defect.
Keep numerical checks separate from any subsequent GCP Lean acceptance.

Remaining to-do list: execute this frozen study, audit delivery, resolve
applicable certification and record the final S047 disposition.
