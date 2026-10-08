# Remaining Lean certification targets

2026-10-07. The author asks whether the remaining prose results should be Lean certified. Recommendation: yes, with the published paper first. All four stories are selected for execution. S022 and S023 now have accepted exact-source GCP proofs; S024-S025 remain uncertified. Original inverse/identifiability and label-law equivalence retain accepted GCP verification at `b7d762acc9c10ca881f8366f545f3998b0528448`; manuscript 0.3.1 correctly identifies the remaining prose results.

## 1. Logarithmic-grid inverse: S022

Target candidate modules: `LogGridRate.lean` and `ImprovedInverse.lean`. Prove exactly `conformalDistance rho sigma <=130*((log N/N)^(1/6)+unlabeledFiniteLawDiscrepancy rho sigma N)` for original K and N>=2. Keep natural log, cutoff 65536, grid `floor(sqrt(n/(8 log n)))`, failure <=1/10 and one global axis ambiguity. No occupied-grid, concentration, reconstruction or inverse conclusion may become a main assumption.

Existing reuse: `GoodSamples.reconstruction_probability_grid` already handles any valid grid; `OrderSelector.reconstructed_orderCDFGood`, `FiniteTV.orderLawTV_event_bound` and `orderCDFGood_common_orbit` supply the common observable/orbit machinery. The existing good-event probability and intersection wrappers hardcode the original fourth-root radius, so add/generalize wrappers with proved new-radius probability instead of invoking them unchanged. Reuse actual interpolation in `DensityInterpolation`, transpose in `Transpose`, and exact labeled/unlabeled TV equality in `Unlabeled`.

Obligations: monotonicity/cutoff and floor inequalities; both exponential terms; new success mass and CDF radius `174 sqrt(8) sqrt(log n/n)`; common observable overlap below TV 4/5; cubic coefficient interpolation and exact `8*712704^2<130^6`; high-TV and small-N branches; original labeled and actual unlabeled all-N exports. The prose proof and finite arithmetic checks are supporting sources, not formal evidence.

## 2. Actual proper time: S023

Target candidate module: `ProperTime.lean`. There are currently no curve-length or time-separation definitions in this library. Define the paper's absolutely continuous future curves with values in the closed diamond, prove derivative measurability/integrability and endpoint integral identities, then define `L_rho=integral sqrt(2rho(gamma)u'v')`. Derive the Cauchy-Schwarz integral bound from that structure and the square-root coefficient inequality from density positivity.

Define time separation by the supremum over actual admissible lengths, treating an empty class as zero. Prove nonnegativity, finiteness, fixed-endpoint comparison, transpose curve/length transport and one global orientation for every pair of endpoints. Export Proposition 6.2's conformalDistance bound and the original inverse-law consequence; compose with S022 for the improved rate. Do not weaken to smooth curves without proving equality with the absolutely continuous definition. A conditional lemma assuming the target length inequality is not certification of the geometric result.

## 3. Finite-data guarantees: S024

Separate from the manuscript. Formalize original-graph implication forcing and certificate soundness, the data-dependent simultaneous rank budget, actual finite DKW marginal concentration plus grid Hoeffding and rational outward rounding, and LP/cell/point/histogram certificate soundness. Assess available proved empirical-process results before choosing the implementation route; an imported theorem citation is not a Lean proof, and an added DKW axiom is unacceptable. Certifying only the old grid calibration would leave the current split-DKW result unproved.

Prove checker soundness and a faithful representation bridge. SciPy can stay outside the trusted computation if a proved checker verifies its rational dual certificates. This does not certify every Python runtime operation or transform full-range density bands into useful inference.

## 4. Gauge counterexample: S025

Separate from the manuscript. Formalize the actual 2+1 Lorentzian diamond and explicit conformal automorphism, smoothness/inverse/Jacobian, density class membership, change of variables and iid chronology-preserving coupling. Derive equality of all finite order laws and positive coefficient distance modulo spatial O(2), alongside the geometric isometry. Existing rational checks are supporting algebra tests, not a universal Lean proof. This strengthens the negative feasibility conclusion; it does not solve the missing higher-dimensional gauge/stability problem.

## Common acceptance and routing

All development/acceptance Lean, Lake and transitive Lean commands execute on GCP only, with pinned Lean 4.30.0/mathlib. Use isolated immutable source inputs and preserve other work. Retain run/instance identities, exact source and dependency hashes checked before/after, complete root build, exact theorem-type/axiom reports, failed attempts and raw terminal logs. No `sorry`, extra axioms, or assumptions encoding the target conclusions. Stop a task-started instance after collection if no other work acquired it. Hosted CI is supplementary.

Finish each story with focused verified commits/pushes and accurate scope documents. Existing DOI artifacts remain immutable; a later manuscript version can advertise enlarged formal coverage after actual acceptance. Certification establishes correctness of encoded statements, not originality, optimality, practical inference or new physics. No specialist-review/adoption gate applies.

S023 delivery is complete. [S024's deterministic foundations](finite-foundation-certification.md) have partial exact-source GCP acceptance with 107 audited exports; the sharp statistical coverage and density certificate suite remain open.

Remaining to-do list: finish finite-data S024 and gauge-counterexample S025. See [S022 acceptance](logarithmic-certification.md) and [S023 acceptance](proper-time-certification.md).
