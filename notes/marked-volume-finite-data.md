# Marked interval volume with bounded detection bias

S040/S041, 2026-10-09. This is an ordinary proof and implementation specification; the accompanying formal audit states exactly which endpoints have GCP acceptance. It supplements the [physical observation audit](physical-observation-identifiability.md). No physical detector is validated here.

## Experiment and target

Let `(M, mu)` be a probability space carrying normalized metric volume. Fix two marked events `p,q` independently of the evaluation sample and let `A=I+(p) intersect I-(q)` be measurable. The target `v=mu(A)` is dimensionless and invariant under marked, volume-preserving chronological isomorphism. The observed input consists of the two chronological flags `p << Xi` and `Xi << q` for each retained event. Their conjunction determines membership of A. The estimator needs neither endpoint coordinates nor a full order realization. Relabeling the events leaves the count unchanged.

The model assumes exact chronological flags. Incomparability is an observed relation outcome; a missing flag is an unavailable observation, not false. Reject inputs with missing/non-Boolean flags. A supplied full relation must be a valid strict partial order with distinct marked anchors before projecting to flags; arbitrary noisy or inconsistent full relations are outside this experiment. Taking transitive closure cannot supply missing truth without additional assumptions. No overlapping-suborder independence is used.

Let retention `pi` be a measurable function in `[a,b]`, with `0<a<=b<=1`, and retain events independently conditional on locations. Conditional on a fixed retained count n, iid volume events under independent thinning (or a Poisson sprinkling conditioned on its retained count) have law

    nu(B) = integral_B pi dmu / integral_M pi dmu.

The conditional law follows by factoring the joint accepted-event density into a product of `pi dmu / Z`; acceptance locations are independent of rejected waiting times. Fixing n by a rule depending on accepted locations is excluded. Define `theta=nu(A)`. The observed count X has mass `choose(n,k) theta^k (1-theta)^(n-k)`, because a specified set of k successful flags has probability `theta^k (1-theta)^(n-k)` and there are `choose(n,k)` such disjoint configurations. This statement is dimension independent. It requires the actual sampling law, not merely a geometric interpretation of an arbitrary point cloud.

## Detection uncertainty

Write `s=integral_A pi dmu`, `t=integral_(M minus A) pi dmu`. Integration of the bounds yields `av<=s<=bv` and `a(1-v)<=t<=b(1-v)`. Thus `s+t>=a>0`. Cross multiplication gives

    v/(R-(R-1)v) <= theta <= Rv/(1+(R-1)v), R=b/a.

Both maps are increasing on `[0,1]`; their derivatives are respectively `R/(R-(R-1)x)^2` and `R/(1+(R-1)x)^2`, and both denominators are at least one. Solving the inequalities gives

    lower_R(theta) <= v <= upper_R(theta),
    lower_R(x)=x/(R-(R-1)x), upper_R(x)=Rx/(1+(R-1)x).

These bounds are sharp without further restrictions on retention: use constant retention a in A and b outside, or the reverse. Intermediate values follow continuously. Endpoint cases v=0,1 satisfy the same formulas. R=1 gives point identification. For R>1 the interval generally stays wide as n grows. At theta=1/2 its width is `(R-1)/(R+1)`; this is a nuisance floor, not sampling error.

For any confidence interval `[L,U]` for theta with endpoints in `[0,1]`, monotonicity proves

    Pr{v not in [lower_R(L),upper_R(U)]} <= Pr{theta not in [L,U]}.

This gives a complete coverage composition, with the physical assumptions explicit. If external calibration gives an upper bound R only with failure probability eta, the unconditional failure bound becomes delta+eta by a union bound; independence of calibration is unnecessary if its bound is valid jointly. No calibration uncertainty is silently assigned zero for a real instrument.

## Finite intervals and numerical certification

For n>0 put `thetaHat=X/n`. Hoeffding gives `Pr{|thetaHat-theta|>=r}<=2 exp(-2nr^2)`. The clipped interval with `r=sqrt(log(2/delta)/(2n))` therefore has coverage at least `1-delta`. For n=0 return `[0,1]`. An implementation may instead supply any rational r for which `2 exp(-2nr^2)<=delta` is rigorously established. The frozen 95% analytic comparator uses a rational radius at least `sqrt(2/n)`, selected with integer square roots. The exact positive Taylor sum `sum_(j=0)^5 4^j/j! > 40` proves `2 exp(-4)<1/20`. Its slightly conservative radius avoids trusting floating logarithms or roots; the implementation operation is not yet Lean certified.

For the primary executable interval, invert exact binomial tails (Clopper-Pearson). For x>0 choose a rational lower endpoint L satisfying `Pr_L{K>=x}<=delta/2`, and use L=0 for x=0. For x<n choose a rational upper endpoint U satisfying `Pr_U{K<=x}<=delta/2`, and use U=1 for x=n. A float beta quantile can propose these endpoints, but every returned endpoint must pass an integer-arithmetic tail comparison; otherwise refine outward or fail closed to `[0,1]`. The proposal is not trusted for coverage. Outward rounding on a denominator D introduces at most `1/D` per side relative to the exact root when the proposal selects the adjoining grid cell; record any larger adjustment.

Here is the coverage proof. Couple binomial variables with common iid uniforms to see that the upper tail is increasing in theta and the lower tail decreasing. If L(x)>theta, then `Pr_theta{K>=x}<=delta/2`. The possible such x form a subset of the upper-tail rejection region, whose probability is at most delta/2: its smallest element already has that tail probability. Likewise U(x)<theta lies in a lower-tail rejection region of probability at most delta/2. Union gives total failure at most delta. This argument does not require a monotone numerical endpoint function. It applies to each sample count, not a posterior probability for the realized interval.

For rational theta=m/D, integer numerator terms are `choose(n,k) m^k (D-m)^(n-k)` with common denominator `D^n`. Summing the requested tail and comparing integers against rational delta/2 avoids underflow and floating tail errors. Endpoint theta=0,1 is handled directly. A returned rational interval and its detection transform can therefore be checked without trusting SciPy. n=0 is handled before tail inversion. Exact-binomial is an established calibration, not a new statistical invention.

## Comparison and physical scope

The coefficient-to-proper-time route estimates an entire density in the original two-dimensional regularity class and then bounds lengths of matched curves. It needs a common coordinate/gauge interpretation and calibrated volume scale. This experiment estimates one volume functional directly at ordinary binomial resolution, with O(n) flag processing and no density smoothness assumption. It gives neither proper time nor curvature. The existing sup-norm density guarantee does not control derivatives; no curvature branch is opened by this result.

Chain-abundance and causal-set curvature operators solve different geometric questions and introduce small-diamond/continuum and derivative assumptions. They are not fair estimators of the same directly marked count under identical information. The appropriate established comparator here is the ordinary exact binomial interval, plus the conservative analytic interval and the no-data interval. Our contribution at this stage is the explicit observation/calibration contract, certified composition and reproducible feasibility audit. Full geometric reconstruction and field-clock application claims remain separate gates.

Primary sources: Clopper and Pearson, *The use of confidence or fiducial limits illustrated in the case of the binomial*, Biometrika 26 (1934), 404-413, [journal DOI](https://doi.org/10.1093/biomet/26.4.404), [full-text mirror](https://www.barestatistics.nl/uploads/1/1/7/9/11797954/clopper__pearson_1934.pdf), inspected printed pages 404-408 for the confidence-belt argument and pages 409-413 for numerical approximation and examples. [R's official binom.test documentation](https://www.stat.math.ethz.ch/R-manual/R-patched/RHOME/library/stats/html/binom.test.html) confirms the conservative coverage interpretation; shortest length is not asserted. Chain/operator sources and their limited relevance are recorded in the roadmap source ledger; their proofs are not used by this interval theorem.

Remaining to-do list: execute the frozen protocol, certify substantive ordinary endpoints on GCP, and record the exact ordinary-to-formal boundary, including S038's separate confounding example.
