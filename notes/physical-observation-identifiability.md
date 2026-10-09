# Physical observations and identifiable geometry

2026-10-09, S038. **Decision: proceed with observable interval-volume inference under explicit sampling assumptions; do not interpret an unknown event-intensity density as a physical metric.** The ordinary arguments below resolve the observation audit and specify the next bounded study. They are not yet new Lean-certified results and carry no novelty claim. The existing S036 theorem and its original experiment are unchanged.

## 1. Physical forward model

Let D be a time-oriented spacetime region with Lorentzian metric g and finite metric volume. Generation and detection produce events with intensity measure

    Lambda(dx) = kappa w(x) dvol_g(x),

where kappa is an overall calibrated intensity if known, and w is the product of relative source intensity and detection efficiency. A detector probability is in [0,1]; a relative source-intensity factor need not be. We use an inhomogeneous Poisson process when discussing unconditioned counts. Conditional on N=n, its locations are iid from

    mu(dx) = w(x) dvol_g(x) / Z,  Z = integral_D w dvol_g.

For the fixed-n experiment this iid law can instead be assumed directly. Record strict directed chronology between sampled points, then discard coordinates and arbitrary labels. Marked reference events, clock readings, known worldlines or other calibration are additional observations when included. A physical signal graph need not supply complete chronology: absent edges can be unobserved timelike relations, and detected null signals have a different sampling model.

In the existing square chart, let

    g_rho = -rho (du tensor dv + dv tensor du).

Then dvol_g = rho du dv, future timelike chronology is strict increase of both coordinates, and an absolutely continuous future curve has length integral sqrt(2 rho u' v'). The original class fixes integral rho=1 and both marginals uniform. Its observed probability density is rho only when w is constant. General generation/detection gives q=w rho/Z. The original theorem cannot be applied to q as a metric coefficient without that bridge or equivalent known calibration; q may also fail the original regularity conditions.

For a general coefficient a(x,y), let q be the normalized event density and U=F_X(x), V=F_Y(y) its marginal probability transforms. Positive continuous marginal densities q_X,q_Y give

    a_tilde = a/(q_X q_Y),  c = q/(q_X q_Y) = w a_tilde/Z.

Thus the uniform-marginal density c represents the transformed physical metric divided by total volume only for constant w. Then g=Vol(D) g_c in these coordinates, and physical proper times are sqrt(Vol(D)) times normalized proper times. The transformation itself does not prove the class bounds needed for S036. Coordinate gauge, physical scale and sampling assumptions are three separate obligations.

## 2. Exact confounding under conformal change

For dimension d and any positive smooth Omega, set

    g' = Omega^2 g,  w' = Omega^(-d) w.

The metric volume is dvol_g'=Omega^d dvol_g. Multiplication gives w' dvol_g'=w dvol_g. Positive conformal scaling preserves time-oriented timelike curves, hence chronology. Couple the two models using the identical point process. Their counts, locations and every observed chronological relation coincide. Any observation channel that depends only on those inputs and a common independent seed also has identical law. This proves equality for labeled and unlabeled data, for every fixed n and for the full Poisson process. It does not include metric-dependent clock readings or an externally measured intensity field.

Consequently, observing more events or more complete chronology cannot by itself separate unknown source/detection intensity from metric volume. This is a model ambiguity, not a shortcoming of a particular reconstruction algorithm. It is distinct from S025's coordinate change between isometric metrics.

Constant scaling is already an obstruction without variable w: g'=c^2 g gives dvol_g'=c^d dvol_g, so normalized-volume sampling and chronology are unchanged, while proper times multiply by c. A fixed n supplies no absolute volume. With known kappa and known w=1, the *unconditioned* count law Poisson(kappa Vol(D)) identifies volume statistically; a single observed count still has uncertainty. Unknown kappa preserves a scale ambiguity. Known integrated intensity alone does not resolve an unknown spatial w.

## 3. An explicit example inside the original density class

Let f(t)=2t-1, epsilon=1/4, and

    rho_0(u,v)=1,
    rho_1(u,v)=1+(1/4) f(u)f(v).

Both are smooth on a neighborhood. Since |f|<=1, rho_1 is between 3/4 and 5/4. Since integral_0^1 f=0, both marginals are exactly uniform and total volume is one. Its gradient has components (1/2)f(v), (1/2)f(u), with Euclidean squared norm at most 1/2; the square is convex, so its Lipschitz constant is at most sqrt(1/2)<2. Both densities satisfy the original class. Their quotient sup distance is 1/4 because rho_1 is invariant under global transpose.

Choose detection probabilities

    pi_0=3/4,  pi_1=(3/4)/rho_1.

Here 3/5<=pi_1<=1, so these are genuine detection probabilities, not unbounded source weights. In both models pi_j rho_j=3/4 pointwise. Starting with a homogeneous, known-intensity Poisson sprinkling per metric volume and independently detecting each event with probability pi_j therefore produces exactly the same retained process. Counts do not repair the ambiguity even when the generation intensity is known.

There are physically different volume targets despite the identical observations. Include two marked reference events p=(0,0), q=(1/2,1/2) in the closure convention, with their chronological relations to the random sample. Their open interval A is (0,1/2)^2. Under rho_0 its normalized metric volume is 1/4. Under rho_1 it is

    1/4 + (1/4) (integral_0^(1/2) (2t-1) dt)^2
    = 1/4 + 1/64 = 17/64.

The detected interval fraction has expectation 1/4 in both models. The marked events add no distinction because chronology remains the same. Equivalent examples can use interior anchors; closure anchors are chosen here for simple exact arithmetic.

The metrics also have different time separations between p0=(0,0) and q0=(1,1). For rho_0, Cauchy–Schwarz bounds every future-curve length by sqrt(2), attained by the diagonal. For rho_1 the diagonal alone has length

    sqrt(2) integral_0^1 sqrt(1+(1/4)(2t-1)^2) dt.

For 0<=x<=1/4, sqrt(1+x)>=1+(2/5)x: square the nonnegative right side and use (4/25)x^2<=(1/5)x. The inequality is strict for x>0 in this range. Since integral_0^1 (2t-1)^2 dt=1/3, the diagonal length is strictly greater than sqrt(2)+sqrt(2)/30. Thus the maximal proper time differs by more than sqrt(2)/30, even with equal total volumes and identical detected data.

These examples give immediate estimation obstructions. Under one common observation law, success sets for two targets at distance Delta are disjoint whenever their error radii sum to less than Delta. Their success probabilities sum to at most one, including independent randomized estimators. No estimator can give confidence greater than one half for both models at a common radius below 1/8 for the density loss, below 1/128 for this interval volume, or below sqrt(2)/60 for the marked proper-time target. This conclusion holds at every sample size. It does not contradict S036, whose constant-intensity observation model excludes the second detector.

## 4. What is recoverable

| Available information | Supported target | Remaining condition |
| --- | --- | --- |
| Complete chronology and iid sampling with unknown positive w | Interval probability under the *detected* measure; measured causal structure | Physical volume and metric coefficient remain confounded. |
| Complete chronology, iid normalized metric-volume sampling, two fixed marked reference events | Normalized metric volume of their chronological interval | Reference events are selected independently of the evaluation sample; calibration of the sampling law is external. |
| The preceding model plus known kappa and unconditioned count | Absolute interval volume and total volume through Poisson counts | Include count uncertainty; exposure/domain and detection efficiency must be known. |
| Known bounds on relative detection variation | A partially identified interval for physical volume | Report a nonvanishing nuisance term, even at infinite sample size. |
| Recorded clock comparisons or calibrated worldlines | Potentially a proper-time or metric target | Requires a new forward model; those observations are not already in a causal order. |

Known spatial w can support inverse-probability weighting only when its value is available at the observed events, or reconstructible with adequate guarantees. A function expressed in unavailable latent coordinates is not an implementable calibration. Uniform thinning preserves normalized volume sampling conditional on retained count; event-dependent thinning generally does not.

## 5. Primary proof comparison

Braun's 2026 journal version assumes globally hyperbolic spacetimes and a common finite total mass; the 2025 v1 states weaker causal hypotheses. Journal pages 3–4 and 12–13 were inspected, including the complete order, volume and weighted assembly arguments. The proof matches generic sequences, extends chronology to a conformal isometry, and uses measure preservation to constrain its factor. Unknown weights therefore do not identify the original metric. Our explicit example specializes this familiar ambiguity; no general reconstruction novelty is claimed. Neither version supplies our finite detector-calibration guarantee. The dense-map extension proof is not independently re-proved here. [Journal DOI](https://doi.org/10.1088/1361-6382/ae456c), [publisher PDF deposited at INSPIRE](https://inspirehep.net/files/532485f95bc081fb1857e27ea6d57d68), [arXiv v1](https://arxiv.org/abs/2507.01907v1).

Retrieval versions, hashes and inspected pages are retained in [source evidence](../evidence/physical-observation/s038-sources.json). The failed direct-publisher retrieval is distinguished from the successful publisher-PDF mirror. No third-party PDF is redistributed.

## 6. Selected next study

Choose **normalized volume of one marked chronological interval** as S041's first physical functional. It needs only interval membership, rather than full density recovery, and has an exact elementary sampling model. Given n iid evaluation events independent of the fixed anchors, X=number in their interval is binomial with parameter theta=mu(A). Derive and implement finite confidence intervals, compare conservative analytic and exact-binomial calibration, and include the full marked-order observation bridge. Choosing endpoints or the best interval after inspecting these same n events would require a new simultaneous or sample-splitting argument.

Choose **bounded event-dependent independent thinning** as S040's first imperfect-observation channel. Let detection probabilities lie in [a,b], 0<a<=b<=1, with ratio R=b/a known. For p=normalized metric volume and theta=detected interval mass, splitting expected retention inside/outside A gives

    p/(R-(R-1)p) <= theta <= Rp/(1+(R-1)p).

Both functions are increasing. Inverting them gives

    theta/(R-(R-1)theta) <= p <= R theta/(1+(R-1)theta).

This follows by separately bounding the two nonnegative integrals in theta=A_w/(A_w+B_w); for p=0 or p=1 the formulas follow directly. A confidence interval [L,U] for theta yields a physical-volume interval with these lower and upper transforms. S040/S041 must supply the complete probability statement, parameter edge cases, implementation checks and exact-source GCP certification. Point identification with unknown nonconstant detection is explicitly not the target.

S044 will compare interval-volume calibration in controlled known geometries and withheld nuisance configurations. This can test a simulation-validation use case in any dimension where true chronology is available; it does not require solving full higher-dimensional metric reconstruction. A genuine 2+1/3+1 simulator must use Lorentz chronology, not coordinate product order. Compare both useful uncertainty and the additional information required by each baseline. A field clock/network claim stays closed until its recorded relations and event process satisfy a separately checked observation model.

Pass the next study only with frozen parameter ranges, independent evaluation, justified coverage and useful widths at specified sample/resource budgets. Preserve empirical failures. These are selected follow-ups under the roadmap goal, not completed experiments. S039's full-density feasibility and S042's geometric work remain necessary independent branches.

## 7. Verification and limits

[Exact arithmetic check](../checks/check_physical_observation_model.py) verifies the example's constants, interval mass and selection-bound inversion, with a numerical proper-time integral as a diagnostic only. The universal proofs are the ordinary arguments above; finite checks are not substitutes. New Lean acceptance is pending in the S040/S041 campaign. No detector, clock network or field observation has been validated by this audit.

Remaining to-do list: certify and evaluate the selected S040/S041 interval-volume/thinning result; complete S039 estimator feasibility, S042/S043 geometry, S044 application comparison, S045 publication and S046 targeted extension. S038 closes with this physical-model audit and successor specification after repository delivery.
