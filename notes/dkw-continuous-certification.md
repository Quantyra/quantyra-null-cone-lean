# Continuous DKW and exact split calibration: partial S024

2026-10-07 local date (2026-10-08 UTC). The sharp continuous uniform DKW theorem, its original-K marginal transport, actual joint-grid failure and exact rational split-calibration checker soundness are now Lean proved.

For n>0 and every real e>=0, `uniform_DKW_actual_population` bounds the actual iid uniform probability of an error greater than e at any real threshold by `2*exp(-2*n*e^2)`. Its population CDF is the actual uniform measure of `Iic t`. No concentration premise is assumed.

`DKWQuantization.lean` proves the measurable clipped natural-ceiling map, inclusive grid ties, actual interval/product masses and exact cardinal/q^n pushforward identity. `DKWUniformGrid.lean` applies the accepted finite counting-law theorem to actual continuous samples. `DKWUniform.lean` proves the nested dyadic event identity, measurability and increasing-union probability bound. The identity holds for all samples; quantization support is only used almost everywhere in the finite-grid transport.

`DKWClass.lean` transports each coordinate vector under the actual original-K product sample measure to the continuous uniform product law. Dependence between coordinates of a sampled point is allowed. Each marginal has the sharp factor two, so the two-marginal failure is at most `4*exp(-2*n*epsilonM^2)`.

`SplitProbability.lean` derives the actual joint-grid union over (q+1)^2 vertices from proved Hoeffding concentration. Combined failure is at most

`4*exp(-2*n*epsilonM^2) + 2*(q+1)^2*exp(-2*n*epsilonJ^2)`.

`SplitCalibration.lean` uses the existing proved 512-subdivision rational exponential upper function, individual probability caps at one, budget-denominator outward ceiling and exact split allocation. `checkSplitCalibration` is a decidable rational checker. For original K, n>0 and an accepted fixed calibration, `checked_split_accuracy_probability` proves actual accuracy-event probability at least `1-delta`. The checker does not assume a target probability or empirical accuracy premise. Parameters are fixed before sampling; choosing them from n and delta does not require an extra table union. Arbitrary data-adaptive calibration is not covered.

The check is sound, not a proof of every Python search execution. A failed epsilon-budget search may select epsilon=1; the runtime then uses its deterministic radius-one fallback. That fallback and faithful full report representations remain open. Accuracy-event probability must still be connected to the checked simultaneous all-cutoff CDF theorem. No full S024 coverage or useful density resolution is claimed.

Authoritative acceptance: `space-dkw-continuous-acceptance-20261008T033940Z-8b2f81`, GCP project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. Root build: 2935 jobs; 143 exact-type/axiom audits; exit zero with no warnings or added axioms. The [receipt](../evidence/gcp/space-dkw-continuous-acceptance-20261008T033940Z-8b2f81/receipt.json), immutable source capture, dependency identities and raw logs preserve acceptance. Lean 4.30.0 and all nine dependency pins remain unchanged. Local Lean invocations: zero.

The [development ledger](../evidence/gcp/dkw-continuous-development-index.json) retains nine immutable captures: six failures, one clean intermediate grid build, one successful calibration development build with linter warnings and the final clean root acceptance. Failed captures and their temporary compiler dependency reports are not certification evidence. Published manuscript/DOI artifacts remain preserved; this software scope postdates manuscript 0.3.1.

After collection and a successful check for other Lean/Lake work, the task-started VM was verified TERMINATED. Shutdown and final-state evidence are retained in the acceptance run.

The next report bridge should define success as a predicate of the finite observed `OrderCode`. Its preimage under `sampledOrder` is measurable even when success quantifies over every real threshold. Almost-everywhere coordinate support/injectivity and the accepted accuracy event then imply this observable success event through `checked_trimmed_CDF`. Preserve one orientation for all trim cutoffs; a cutoff selected from the observed order needs no additional union. The deterministic radius-one branch must cover rejected budget checks.

Source/evidence commit `9c94ce11a3e089f0fb379dc795698d8ca371e63f` is pushed. Supplementary [proof/manuscript CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37724203707), [literature CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37724203732) and [Python CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37724203710) all passed. This delivery closeout changes docs/evidence only; proof/check/config bytes retain exact accepted identities.

Remaining to-do list: accuracy-to-CDF/report integration and representations; actual cell feasibility, all-point expansion, histogram error and deterministic fallbacks; final S024 acceptance and delivery; S025.
