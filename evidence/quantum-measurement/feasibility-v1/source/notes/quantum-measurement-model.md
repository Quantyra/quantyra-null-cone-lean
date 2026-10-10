# Loss-only qubit measurement: scoped feasibility argument

2026-10-10, S047. This is an ordinary mathematical argument and model freeze,
not a claim of Lean acceptance or a laboratory validation. The accompanying
[source comparison](quantum-measurement-sources.md) finds an established
confidence construction. The question is whether transferring it gives a
reason to invest in a separate quantum method.

## Experiment and observable

An arbitrary qubit density matrix is
`rho = [[p,z],[conj(z),1-p]]`, where `0 <= p <= 1` and
`|z|^2 <= p(1-p)`. The target is `theta = tr(rho Z) = 2p-1`.
The fixed loss-only POVM is

    E+ = diag(eta+,0), E- = diag(0,eta-),
    E0 = diag(1-eta+,1-eta-),  a <= eta+,eta- <= 1, a = 1/2.

Each operator is positive and their sum is the identity. Direct multiplication
gives Born probabilities

    r+ = p eta+, r- = (1-p) eta-, r0 = 1-r+-r-.

Coherence z changes none of these probabilities. Even perfect observations
in this basis cannot identify the full density matrix. The unknown state is
prepared independently n times. Record all three counts and the total n.
Independently prepare trusted `|0>` m+ times and trusted `|1>` m- times using
the same stable detector. Their respective correct-click counts K+,K- have
binomial parameters eta+,eta-. A known bit flip and one trusted basis state
can provide the two calibration preparations.

The full count law is

    Multinomial(n;r+,r-,r0) x Bin(m+,eta+) x Bin(m-,eta-).

Its first two probe marginals are binomial but are generally dependent.
Exact preparation, the efficiency lower bound, absence of dark counts and
misclassification, fixed efficiencies across all blocks, and independent
trials are hypotheses. No hardware evidence for them is supplied. This study
does not model drift, correlated loss, back-action across trials or uncertain
trusted preparations. Calibration failures do not diagnose those alternatives.

## Sharp population identification

For deterministic efficiency ranges `[l+,u+]`, `[l-,u-]` contained in `[a,1]`,
the possible populations given r+,r- form exactly

    P = [0,1] intersect [r+/u+, r+/l+]
              intersect [1-r-/l-, 1-r-/u-].                 (1)

Necessity follows by multiplying p and 1-p by the efficiency bounds.
For sufficiency, if 0<p<1 take `eta+=r+/p`, `eta-=r-/(1-p)`.
At p=0, feasibility forces r+=0; choose any admitted eta+ and set eta-=r-.
At p=1 use the symmetric construction. The diagonal state realizes every
feasible p. Nonnegative probabilities with r++r-<=1 then give the required
no-click probability automatically. Thus (1) is sharp for this scoped model.
Knowing either efficiency exactly and positively identifies p from its click
probability. Learning both efficiencies from their population calibration
laws therefore identifies theta; finite calibration is still uncertain.

For no calibration, two admitted models are

    A: p=2/5, eta+=3/4, eta-=1/2, theta=-1/5;
    B: p=3/5, eta+=1/2, eta-=3/4, theta=+1/5.

Both have `(r+,r-,r0)=(3/10,3/10,2/5)`. Their complete probe records have
identical laws for every n. Any estimator, including one using independent
randomization, has disjoint success events at radius strictly below 1/5 for
these two targets. Under the common law their success probabilities sum to
at most one. At least one model has failure probability at least 1/2.
This obstruction assumes m+=m-=0; calibration distinguishes the models.

Here the full-data population set is p in [2/5,3/5]. Retaining detections
alone gives conditional positive probability q=1/2 and efficiency ratio at
most two. The established bounded-selection transform gives [1/3,2/3].
Discarding no-clicks loses information. The apparent improvement over that
coarser experiment is not a new method beating a matched baseline.

## Finite uniform confidence

Let alpha=1/20. Give each of the four marginal binomial intervals total
failure budget delta=alpha/4=1/80, with delta/2 in each tail. Probe intervals
are `[A+,B+]`, `[A-,B-]`; calibration intervals intersected with [a,1] are
`[l+,u+]`, `[l-,u-]`. Use outward rational Clopper-Pearson endpoints checked
by exact integer tails, reusing `tools/marked_volume.py`. A zero-size
binomial block reports [0,1]. If a calibration intersection is empty,
report the full p range [0,1]. Otherwise set

    L = max(0, A+/u+, 1-B-/l-),
    U = min(1, B+/l+, 1-A-/u-).                           (2)

If L>U report [0,1]; otherwise report [L,U]. Transform to theta as
`[2L-1,2U-1]`. Full-range fallback is explicit, not an empty confidence set.

For any admitted state and detector, each marginal interval misses with
probability at most delta. The union bound makes the probability of any
miss at most 4 delta=alpha; it does not require independence of N+ and N-.
On the simultaneous coverage event, efficiency clipping is nonempty and
the true p satisfies every inequality in (2). Hence L<=p<=U and the theta
interval covers. The resulting guarantee is uniform 95% finite-sample
coverage over this model, including zero blocks and parameter boundaries.
Independent calibration blocks justify the displayed joint law; coverage
only requires the four correct marginal laws.

These are confidence intervals for a fixed unknown target, not posterior
probabilities. Floating beta quantiles propose rational endpoints; exact
tail checks supply their mathematical validity. Python is not Lean verified.

## Error sources and established comparator

More generally, (2) is the exact projection of the four marginal probability
boxes through `r+=p eta+`, `r-=(1-p) eta-`. Feasibility for the positive
block is equivalent to `u+ p >= A+` and `l+ p <= B+`; the negative block is
equivalent to `u- (1-p) >= A-` and `l- (1-p) <= B-`.
Their intersection with [0,1] proves this assertion, including p=0 and p=1.
If the box is nonempty, its width is bounded by

    U-L <= min(1, ((B+-A+)+(u+-l+))/a,
                  ((B--A-)+(u--l-))/a).                  (3)

Indeed, choose feasible detector values for either endpoint; the difference
of the two click probabilities is at most the probe-box width. Moving the
efficiency contributes at most its box width because p is at most one;
division by the efficiency lower bound gives (3). The theta half-width is
U-L. Probe and calibration widths are separate contributions. With fixed
calibration, unlimited probe data need not resolve the nuisance. Formula
(1), rather than a universal numerical crossover, describes that limit.
No minimax rate, optimal allocation or fixed calibration crossover is claimed.

A generic exact-binomial constraint-projection baseline given the same four
counts, budgets and efficiency class has exactly (2) for every input, with
the same fallback. This is an algebraic identity, not merely equality on a
simulation grid. Calling this construction a quantum specialization cannot
give a narrower interval than that matched established construction. The
conditional-detection selection transform remains a different-data diagnostic.

The matched joint-tomography likelihood is the multinomial probability above
times both calibration likelihoods, with the same loss-only structural zeros
and efficiency bounds. It supplies a point comparator. A numerical local
maximum and its bootstrap interval do not supply the uniform finite coverage
guarantee proved here. The evaluation records optimization outcomes rather
than assuming a global maximum or treating bootstrap coverage as exact.

## Formal reuse and remaining obligation

`binomial_report_coverage` and `membership_count_eq_binomial` already have
GCP acceptance in the satellite. They supply the generic marginal confidence
and iid count machinery. The Born reduction, full count-law construction,
four-report projection/coverage bridge and the explicit indistinguishability
pair above are ordinary mathematics at this checkpoint. They must not be
described as a certified quantum endpoint. Any selected new formal endpoint
will get an exact ordinary-to-formal map and GCP-only acceptance.

Remaining to-do list: frozen bounded evaluation, applicable certification,
and the final S047 investment/manuscript decision.
