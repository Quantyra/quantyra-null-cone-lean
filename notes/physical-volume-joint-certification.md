# Joint physical-volume accuracy and detector calibration

2026-10-09 (Hawaii), S046 mathematical certification. The full scoped upper/lower theorem and separate zero-sample result now have GCP acceptance. S046 remains open for its primary-proof comparison, final finite-formula validation and manuscript disposition. This extends the [accepted upper endpoint and detector obstruction](physical-volume-rate-progress.md) and certifies the [ordinary derivation](physical-volume-calibration-rate.md).

## Frozen experiment and complete statement

The original class K retains smoothness, density bounds [1/2,3/2], Euclidean Lipschitz constant 2 and uniform coordinate marginals. An unknown measurable detector lies globally in [1/R,1], with 1<=R<=2. The data are all directed chronological relations among n retained events and two fixed marked anchors (0,0), (1/2,1/2), modulo permutations of sampled events. The target v is the original physical mass of their open chronological interval. Generated counts, detector values, latent coordinates and clocks are not added to the observations.

For n>=1 set a=1/sqrt(n), b=(R-1)/(R+1), s=min(1,a+b). `physical_volume_joint_rate` proves both quantified statements together:

    For every admitted model, P(|K/n-v| > 2*s) <= 1/20.
    For every measurable full-order estimator and any common independent probability seed,
    some admitted model has P(|T-v| > s/256) >= 1/4.

The constants are uniform in n and R, including R=1 and sequences R approaching 1 with n. The upper estimator is a single measurable function of the observed quotient. The lower bound permits arbitrary independently randomized estimators, not just count estimators. It is not a claim of optimal constants, a sharp identified set or shortest confidence intervals.

## Sampling comparison

Use f(t)=2t-1, rho_epsilon(u,v)=1+epsilon*f(u)*f(v), and epsilon=1/(2sqrt(n)), with detector identically one in both the flat and alternative models. The original class membership and physical target formula v_epsilon=1/4+epsilon/16 are accepted from S040. The new proof establishes the actual coordinate product likelihood L and

    E_0 L = 1,
    E_0 (L-1)^2 = (1+epsilon^2/9)^n-1 <= 1/35.

It derives the with-density identity and all required integrability conditions. Likelihood nonnegativity holds almost everywhere on the product diamond; no global positivity of the ambient polynomial is assumed. The squared profile integral is exactly 1/3.

The bound is finite: for x=1/(36n), Bernoulli's inequality gives (1-x)^n>=35/36, and (1+x)^n(1-x)^n=(1-x^2)^n<=1. Thus (1+x)^n<=36/35. Cauchy-Schwarz and the accepted finite-observation contraction give full marked-order total variation at most 1/4. This controls all observed relations before an estimator discards information.

The accepted finite seed testing theorem, applied to measurable disjoint scalar-success events, gives worst-case strict error greater than a/128 with probability at least 3/8. The more general sampling obstruction permits any radius r satisfying 2*r<epsilon/16. Detector one is allowed for every R>=1.

## Joint lower bound and zero samples

The previously accepted detector pair with epsilon=b gives identical complete observation laws and a physical-volume gap b/16, with globally valid detectors in [1/R,1]. Its general obstruction permits 2*r<b/16 with failure at least 1/2.

`physical_volume_joint_rate_lower` chooses the sampling pair when a>=b and the detector pair otherwise. In both branches r=s/256 is strictly less than half the applicable target gap. The detector branch proves R>1 rather than assuming it; the sampling branch handles R=1. No fixed-R limiting argument is used.

For n=0, `physical_marked_volume_range` proves v in [1/8,3/8], so the constant estimate 1/4 has deterministic absolute error at most 1/8. `empty_full_marked_law` identifies the actual observation as a Dirac law retaining the fixed anchor relations. Flat density and epsilon=1/2 with unit detectors therefore have the same observation law and target gap 1/32. `no_data_physical_volume_obstruction` gives error exceeding 1/128 with probability at least 1/2 for some admitted model, for every independent randomized estimator. This is a separate convention; the positive-n rate formula is not applied at n=0.

## Ordinary-to-formal map

| Obligation | Accepted endpoint |
| --- | --- |
| Original K, actual target and globally valid compensating detector | S040 `ConfoundingGeometry`, `ConfoundingDetector`, `ConfoundingTargets`, `ConfoundingMarked`; prior S046 `VolumeRateExperiment`. |
| Observable fraction and finite upper bound | Prior S046 `MarkedEstimator`, `VolumeRateBounds`, `VolumeRateUpper`, `VolumeRateModel.volume_rate_upper`. |
| Actual polynomial product likelihood and exact moments | `VolumeRateLikelihood`: with-density/real-set formulas, support-aware positivity, first and second moments. |
| Uniform finite divergence control | `VolumeRateScale`: admissible epsilon, exact scaling and Bernoulli power bound. |
| Full marked law and arbitrary seed testing | `VolumeRateSampling`: full marked TV, scalar testing and admitted-model sampling obstruction. |
| Joint positive-n theorem | `VolumeRateJoint`: joint lower bound and combined quantified upper/lower endpoint. |
| No-data target range and actual equal laws | `VolumeRateEmpty`: deterministic upper error and randomized obstruction. |

## Acceptance and interpretation

GCP run `space-volumerate-acceptance-20261010T023105Z-5d08cf` passed 3,097 full-root jobs and **797 exact type/axiom reports**, including all 29 new theorems in five modules. There were zero warnings and only `propext`, `Classical.choice` and `Quot.sound`. All 198 captured source identities match the archive, current files and staged Git blobs. Pinned dependencies were checked before and after. [Receipt](../evidence/gcp/space-volumerate-acceptance-20261010T023105Z-5d08cf/receipt.json), [custody verification](../evidence/volumerate/formal-verification.json), [verifier](../checks/verify_volume_rate_acceptance.py).

Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` ran only on project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. Isolated RAM caches preserved prior work. Failed attempts are retained. After collection and the no-other-Lean-work check, the task-owned VM was verified TERMINATED at `2026-10-10T02:42:04.505587+00:00`. [Cleanup](../evidence/gcp/space-volumerate-acceptance-20261010T023105Z-5d08cf/cleanup.json). Existing proof evidence, frozen pilot and all published manuscripts are preserved. No new samples were generated.

The rate identifies a statistical crossover: additional retained events reduce the sampling term, while fixed unknown detector variation leaves an accuracy floor. Maintaining sampling-order accuracy requires the calibration term to decrease at order n^(-1/2) or faster. This is not a monetary investment optimum or validation of a physical instrument. The proof constants remain loose; practical confidence reports still require their own comparisons.

Partial identification and bounded-selection inference are established topics. The bounded contribution is this finite geometric/full-observation result and its certification. The direct Aronow-Lee comparison remains pending a lawful copy; final finite-formula validation and manuscript placement remain open. Earlier ordinary and partial-certification notes preserve their historical status statements; this audit supplies the current mathematical status.

Remaining to-do list: S046 source comparison, final finite validation and manuscript disposition; S039 and S042-S044 remain selected.
