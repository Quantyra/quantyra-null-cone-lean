# Beam-profile selection and contamination model

S049, 2026-10-10. This is an ordinary feasibility argument for a possible
detector-only beam-profile decision. It does not establish a new tracking
method, a comparative decision benefit, physical calibration or Lean
certification. The earlier pure-thinning results and manuscripts stay frozen.

## Physical target and operational observations

Fix spatial cuts before evaluation and define three exclusive categories:

```
A = {X <= x0, Y <= y0},
B = {X > x0, Y > y0},
C = the complement.
```

Writing their generated probabilities as `(a,a+d,1-2a-d)` is exact, with
`d = 1-F_X(x0)-F_Y(y0)`. This follows by inclusion-exclusion, including atoms
on either cut with the inequalities above. A median-based construction needs
calibrated marginals; no balance property follows from the beam data alone.
The physical target would be membership of `a` in a specified acceptable
band, conditional on a defined target particle cohort. These spatial
categories do not represent Lorentz chronology.

The operational instrument supplies its own clusters. A validation reference
may supply particle trajectories and calibration, but its per-event selection
cannot silently become part of a detector-only procedure. For the proposed
complete-reference cohort, relate generated target records and observed
clusters by a partial one-to-one matching that preserves the category label.
Missed target records affect retention. Unpaired observed records, including
off-target particles, wrong labels and extra split clusters, affect
contamination. A merge may instead remove target records; categorically wrong
merges can also require an unpaired output. The existence of a useful matching,
its error bounds and the sampling law remain physical obligations.

Let `p=(a,a+d,1-2a-d)` and impose the null constraints

```
0 <= delta < l <= a <= u,  |d| <= delta,  2*u+delta < 1,
R >= 1,  w_j in [1/R,1],
t_j = w_j*p_j/S,  S = sum_j w_j*p_j,
q = (1-eta)*t + eta*h,  h in Delta_3,  0 <= eta <= epsilon < 1.
```

Only ratios of the category retention probabilities matter for `t`, so a
common scale can be removed. `eta` is the fraction of observed records
outside the correctly labeled retained-target channel. It is not the
probability of missing a target particle. The mixture allows arbitrary
contaminant categories but does not by itself establish independent draws.

## Exact convex description of the continuous null

Use variables `y0,y1,y2,c_A,c_B,c_C,e_A,e_B,e_C`, where all but `y2` are
nonnegative, and set

```
b = (y1, y1+y2, y0-2*y1-y2),
l*y0 <= y1 <= u*y0,  -delta*y0 <= y2 <= delta*y0,
b_j/R <= c_j <= b_j,
q_j = c_j+e_j,  sum_j q_j = 1,  sum_j e_j <= epsilon.
```

Every model point supplies these variables by taking
`y0=(1-eta)/S`, `y1=a*y0`, `y2=d*y0`, `c=(1-eta)*t` and `e=eta*h`.
Conversely, any feasible lift has `sum c >= 1-epsilon > 0`, hence `y0>0`.
Its three `b_j` are strictly positive by the parameter assumptions. Set
`a=y1/y0`, `d=y2/y0`, `w_j=c_j/b_j` and `eta=sum e`. These recover the model;
if `eta=0`, choose any `h`, otherwise take `h=e/eta`. In particular
`sum c=y0*sum(w*p)=1-eta`. All constraints are linear, so their projection
onto `(q_A,q_B)` is convex. It is bounded and closed: for example
`sum c >= y0/R` bounds `y0`, and the other variables are bounded in turn.

The clean null `T` has an exact finite description. Evaluate `w*p/sum(w*p)`
at the four corners of `[l,u] x [-delta,delta]` and the eight corners of
`[1/R,1]^3`. The unnormalized map `w*p` is affine in each of these five
scalar parameters separately. Multilinear interpolation expresses each
interior mass vector as a nonnegative combination of its 32 corner mass
vectors. Normalizing changes these coefficients by positive total-mass
factors and yields a convex combination of the normalized corner images.
Conversely those corner images lie in `T`, and the lift proves `T` convex.
Their convex hull therefore equals the entire continuous clean null.

For positive `epsilon`, every smaller contamination level can be absorbed
into `h`: write
`h' = ((epsilon-eta)*t + eta*h)/epsilon`. It belongs to the probability
simplex, so the full null is exactly the Minkowski sum

```
Q_epsilon = (1-epsilon)*T + epsilon*Delta_3.
```

At zero contamination it is `T`. Consequently the convex hull of the 96
corner images `(1-epsilon)*t_corner + epsilon*unit_j` is exact, including
degenerate clean hulls when `R=1` and `delta=0`. Rational inputs give an
exact rational polygon. No discretization of the nuisance set is involved.

## Sharp conditional probability bounds

For `A:C` and `B:C`, respectively, the conditional probabilities are
`q_A/(q_A+q_C)` and `q_B/(q_B+q_C)`. For the lower endpoints put
`a-=l`, `b-=l-delta`, `c-=1-2*l+delta`; for the upper endpoints put
`a+=u`, `b+=u+delta`, `c+=1-2*u-delta`. Then

```
L_A = (1-epsilon)*a- / (a- + R*(c- + epsilon*b-)),
L_B = (1-epsilon)*b- / (b- + R*(c- + epsilon*a-)),
U_A = (R*(a+ + epsilon*b+) + epsilon*c+) /
      (R*(a+ + epsilon*b+) + c+),
U_B = (R*(b+ + epsilon*a+) + epsilon*c+) /
      (R*(b+ + epsilon*a+) + c+).
```

To prove sharpness, fix positive `(a,b,c)`. For `A:C` the minimum places all
contamination in C, uses `eta=epsilon`, and takes
`w_A=1/R,w_B=w_C=1`. Its value is
`(1-epsilon)*a/[a+R*(c+epsilon*b)]`. The maximum places contamination in A
and takes `w_A=w_B=1,w_C=1/R`, giving
`[R*(a+epsilon*b)+epsilon*c]/[R*(a+epsilon*b)+c]`.
The contaminant extremes follow by linear-fractional optimization over the
simplex (or direct differentiation); weight monotonicity follows immediately
from these fractions before optimizing the weights. Exchanging A and B gives
the other two expressions.

Substitute `b=a+d,c=1-2*a-d`. All four optimized fractions increase with
both `a` and `d`. For the two lower fractions, after removing positive
factors, the derivative numerators with respect to `(a,d)` are
`(1-(1-epsilon)*d, (1-epsilon)*a)` and
`(1+(1-epsilon)*d, 1-(1-epsilon)*a)`. For the upper fractions use
`U=1-(1-epsilon)*c/[H+c]` with `H=R*(a+epsilon*b)` or
`H=R*(b+epsilon*a)`. The corresponding positive derivative factors are
`(1+epsilon-(1-epsilon)*d, epsilon+(1-epsilon)*a)` and
`(1+epsilon+(1-epsilon)*d, 1-(1-epsilon)*a)`.
The parameter constraints make them positive. Thus the stated corners attain
the global extrema. At `delta=epsilon=0` both intervals recover
`[l/(l+R*(1-2*l)), R*u/(R*u+1-2*u)]`.

The independent numerical audit homogenizes the same lifted constraints,
replacing `sum q=1` with `q_X+q_C=1` for each conditional optimization.
In the homogeneous cone, the pollution inequality is
`(1-epsilon)*sum e <= epsilon*sum c`. Positive denominators permit scaling
in both directions. This is an application of established linear-fractional
programming: [Charnes and Cooper (1962), pp. 182-184](https://iiif.library.cmu.edu/file/Cooper_box00010_fld00009_bdl0001_doc0001/Cooper_box00010_fld00009_bdl0001_doc0001.pdf),
[DOI 10.1002/nav.3800090303](https://doi.org/10.1002/nav.3800090303).
The audited specialization is not a new general optimization principle.

## What a statistical transfer would additionally require

If observed categories are iid with fixed law `q`, each category count
conditional on its count together with C is binomial. The earlier
[two-tail endpoint calibration](../balanced-volume/finite-reference-derivation.md)
therefore applies using these enlarged intervals, with the usual union bound
for the two dependent tests. The iid premise is substantive: multiple tracks
per event, shared alignment, time dependence and reference selection can
violate it. This model calculation does not validate that premise.

If a separate calibration has failure probability at most `gamma`, a total
error bound of `alpha+gamma` also requires that conditional on the frozen
calibration and its valid event, the operational test has error at most
`alpha`. A justified independent split is one sufficient route. Merely
combining marginal calibration coverage with a data-adaptive test is not.
No calibration failure allowance is selected or estimated here.

## Exact overlap with the earlier positive benchmark

The earlier pure-thinning alternative has `a=b=1/4,c=1/2` and
`w=(1,4/5,1)`, yielding

```
q_alt = (5/19,4/19,10/19).
```

Within the nominated null band `[9/32,11/32]`, take `a=b=9/32,c=7/16`,
the same weights, and contamination entirely in C. Its clean law is
`t=(45/151,36/151,70/151)`, and the exact identity is

```
(1-20/171)*t + (20/171)*(0,0,1) = q_alt.
```

Thus allowing contamination `epsilon >= 20/171` (about 11.696%) makes this
particular alternative observationally identical to an allowed null. The
full iid categorical sample laws agree for every sample size. Every test
uniformly valid at level `alpha` over this enlarged null consequently has
rejection probability at most `alpha` at that alternative, including tests
with independent randomization. More samples cannot separate identical laws.
The earlier finite reference's model power would instead become its
false-flag probability at this null witness if transferred unchanged.

This is not a measured contamination rate, a refutation of the original
pure-thinning theorem or a universal impossibility for beam applications.
It is an exact obstruction for a specified expanded model and benchmark.

For the protocol's balance-error sensitivity check, compute the minimum
contamination by support functions. Write `h_T(n)=max_{t in T} n.t` and
`h_Delta(n)=max(0,n_A,n_B)`. The hull of `(T+Delta)/2` supplies the edge
normals needed for every positive contamination level, including when `T`
is a segment or point: positive scaling of two fixed polygons preserves
the common refinement of their normal fans. Each supporting inequality
requires

```
epsilon >= (n.q-h_T(n))/(h_Delta(n)-h_T(n))
```

when the denominator is positive. A zero denominator contributes no new
condition for `q` in the simplex. Taking the maximum with zero gives the
exact minimum. The zero-contamination boundary follows by continuity. Check
exact hull membership at this minimum, nonmembership at half of a positive
minimum, and an independent continuous LP minimizing `sum e` subject to
the observed `q` and the lifted constraints without a contamination cap.

## Finite-record feasibility check and decision boundary

If the inspected development subset has `N_obs` operational clusters and
`N_ref=56,907` complete reference tuples, any partial one-to-one matching
can pair at most `N_ref` clusters. Its unpaired observed fraction is at least
`max(0,1-N_ref/N_obs)`. This bound requires no spatial matching algorithm.
It applies to this specific record cohort; it does not establish the
superpopulation contamination parameter, detector noise or physical truth
of the reference associations. Conditioning on all reference hits can
exclude genuine particles that appear in the detector's operational feed.

The frozen protocol will count clusters only in the already inspected
10,000-event subset and compare this cardinality bound with the exact
overlap threshold. No outcomes from the remaining 102,700 events are read.
A failed envelope for this mapping calls for changing or parking the mapping
before tuning a test or spending those measurements. A surviving mapping
would still need a useful physical decision and matched comparison against
full multinomial nuisance inference; wider conditional intervals alone are
not a comparative benefit.

Remaining to-do list: execute the frozen model/cardinality audit, resolve the
operational mapping, then establish a comparative benefit and validate its
physical assumptions before claiming practical use.
