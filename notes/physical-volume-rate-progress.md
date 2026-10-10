# Physical volume: upper rate and calibration obstruction

2026-10-09 (Hawaii), partial S046 delivery. The joint minimax result in the [ordinary derivation](physical-volume-calibration-rate.md) remains incomplete in Lean. This delivery certifies the complete uniform upper endpoint and the detector-limited lower endpoint, building on [S040 confounding](confounding-certification.md). It adds no empirical-performance or publication claim.

## Exact experiment and observable estimator

`VolumeRateModel R rho pi` keeps the original smooth, Euclidean-Lipschitz, uniform-marginal `InDensityClass`, with a measurable detector globally in [1/R,1]. Integrability and probability normalization are derived. Observations contain all directed chronological relations among n retained events and the two fixed anchor roles (0,0) and (1/2,1/2); only sample labels are discarded. No generated counts, detector values, latent coordinates or clocks are supplied.

`MarkedEstimator` extracts the two anchor-to-event relations needed for interval membership, proves invariance under sample permutations, and lifts the fraction to the actual quotient. The resulting measurable estimator is exactly K/n on every generated sample, takes values in [0,1] for n>0, and obeys Hoeffding's bound under the full observed law. This is an observable mathematical estimator; the existing executable count estimator is unchanged.

## Certified upper endpoint

Set a=1/sqrt(n), b=(R-1)/(R+1), and s=min(1,a+b). For every n>=1, R>=1, and admitted model,

    P(|markedOrderFraction 0 1 - physicalMarkedVolume rho| > 2*s) <= 1/20.

`VolumeRateModel.volume_rate_upper` is the fixed-experiment endpoint. `physical_volume_rate_upper` also permits arbitrary fixed anchor pairs. The proof derives both retention-transform deviations from the retained probability as at most b, and hence the same bound for absolute physical/retained probability bias. Algebraic nonnegativity is proved through square identities. The upper result includes R=1 and is uniform for sequences R approaching 1.

The formal proof uses concentration radius 2/sqrt(n), with exact Hoeffding budget n*r^2=4, followed by the already accepted 95% exponential bound. The ordinary note uses sqrt(2/n). Both give the identical frozen endpoint 2*s with failure at most 1/20; the formal route changes no theorem constant. The minimum with 1 is justified by the estimator and physical probability ranges, including the small-n case.

## Certified detector obstruction

For every 1<R<=2 use epsilon=b. The formal proof shows 0<epsilon<=1/3 and (1-epsilon)/(1+epsilon)=1/R. The flat geometry with constant detector 1-epsilon and the polynomial alternative with the globally clamped compensating detector both satisfy `VolumeRateModel`. Their complete marked observation laws agree, and their physical volumes differ by b/16.

For every n (including zero), every common independent probability seed and every measurable scalar estimator T, `physical_volume_detector_obstruction` produces an admitted model with

    P(|T - physicalMarkedVolume rho| > r) >= 1/2 whenever 2*r < b/16.

In particular, `physical_volume_detector_rate_lower` gives r=b/64. The argument uses the actual full observation laws and arbitrary independent randomization; it assumes no testing inequality. R=1 has no positive detector ambiguity, so its sampling obstruction remains a separate obligation.

## Acceptance and custody

GCP run `space-volumeupper-acceptance-20261010T015754Z-02151c` passed **768 exact type/axiom reports**, including all 25 new theorems in four modules, and 3,092 full-root build jobs. There were zero warnings and only `propext`, `Classical.choice` and `Quot.sound`. All 192 captured source hashes match the archive, current files and staged Git blobs. Pinned dependencies were checked before and after.

Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` ran only on GCP: project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. [Receipt](../evidence/gcp/space-volumeupper-acceptance-20261010T015754Z-02151c/receipt.json), [custody result](../evidence/volumeupper/formal-verification.json), [verifier](../checks/verify_volume_upper_acceptance.py). Failed development attempts and transport output are retained. Isolated RAM builds preserve the reusable disk cache and other campaigns.

After collection and a no-other-Lean-work check, the task-owned VM was verified `TERMINATED` at `2026-10-10T02:04:50.181023+00:00`. [Cleanup](../evidence/gcp/space-volumeupper-acceptance-20261010T015754Z-02151c/cleanup.json). The baseline proof files, frozen S041 pilot and all manuscript/DOI artifacts are preserved, apart from declared root/audit integration. No samples were generated and no local Lean invocation occurred.

## Remaining S046 obligations

The sampling lower bound still requires the polynomial likelihood's exact second moment, its finite divergence bound, contraction to full marked observations, and randomized scalar testing. The polynomial alternative need only be nonnegative almost everywhere under diamond area; it is not globally nonnegative outside the diamond. An adaptation of the old Gaussian likelihood proof must preserve that distinction. The accepted squared-profile integral is 1/3, and the ordinary moment target is (1+epsilon^2/9)^n. Combine the sampling bound with the accepted calibration obstruction to certify the frozen s/256, failure>=1/4 endpoint. The zero-sample convention, final deterministic formula validation, direct Aronow-Lee comparison and manuscript disposition remain open. These accepted components do not establish a sharp identified set, optimal constants, calibration cost policy or field sensor benefit.

Remaining to-do list: finish S046 sampling/joint/n=0 proofs, source comparison, finite validation and manuscript disposition; S039 and S042-S044 remain selected.
