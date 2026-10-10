# Laplace functional of the actual retained Poisson experiment

2026-10-09 (Hawaii), S040. The explicit product and Laplace functionals now have GCP acceptance. This extends the [accepted count/tuple process law](thinning-process-certification.md) and discharges one more endpoint of the [ordinary thinning proof](independent-thinning-process.md). S040 remains incomplete: stopping, complete geometric confounding and the final decision audit remain open.

## Result and assumptions

Draw N from Poisson(kappa), independently of an infinite iid sequence of pairs (X_i,U_i), where X_i has probability law mu and U_i is uniform on [0,1]. Inspect the first N pairs and keep X_i when U_i < pi(X_i). Require a measurable detector pi in [0,1], its integrability, and positive mean retention Z = integral pi dmu. Kappa may be zero. Write nu = pi mu / Z.

For every measurable f taking values in [0,1], the formal result proves

    E product_retained f(X_i)
      = exp(kappa Z (integral f dnu - 1))
      = exp(kappa integral pi(x) (f(x)-1) dmu(x)).

The product is over the actual retained tuple in generation-index order. An empty product is one. The proof uses the accepted actual count/tuple law, the finite product integral and the Poisson exponential series. It does not assume a separate Poisson-thinning theorem.

Substitute f(x)=exp(-h(x)). For every nonnegative measurable real-valued h, without a boundedness assumption, this gives

    E exp(-sum_retained h(X_i))
      = exp(kappa integral pi(x) (exp(-h(x))-1) dmu(x)).

The sum includes multiplicity, so atoms and repeated retained locations are covered. The test function is finite-valued at each point, though it may be unbounded. Extended-real test functions taking +infinity are not part of this endpoint. The positive-Z assumption remains; selected detector bounds 0<a<=pi<=b<=1 imply it. No separate finite-counting-measure representation or characterization-by-Laplace theorem is asserted.

In the normalized physical model, mu is the metric-volume probability law and kappa is the generated mean. This establishes a distributional property of the specified independent detection experiment. It supplies neither operational detector calibration nor an absolute geometric scale. It does not address correlated detection, missing relations, adaptive anchors or geometry-dependent stopping.

## Ordinary-to-formal map

| Obligation | Endpoint |
| --- | --- |
| Bounded-test integrability and normalized retained integral | `thinning_unit_integrable`, `retained_integral_identity` |
| Real and extended-nonnegative Poisson power series | `poisson_power_hasSum`, `poisson_power_series` |
| Finite retained product: measurability, range and expectation | `retained_sample_product_measurable`, `retained_sample_product_unit`, `retained_sample_product_integral` |
| Actual Poisson product expectation, including intensity form | `poisson_retained_product_lintegral`, `poisson_retained_product_integral`, `poisson_retained_product_intensity` |
| Explicit Laplace functional | `poisson_retained_laplace_functional` |

The first seven endpoints are in `ThinningGenerating.lean`; the remaining four are in `ThinningLaplace.lean`. All eleven are included in the root import and full type/axiom audit.

## Verification and preservation

Run `space-stopping-acceptance-20261010T001049Z-8b6cab` passed **3,072 root-build jobs and 647 exact type/axiom reports**, with zero warnings and only `propext`, `Classical.choice` and `Quot.sound`. All 170 captured source identities and pinned dependency identities were checked before and after. Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` ran on `quantyra-lean-builder-01`, `us-central1-a`, project `quantyra-lean-cert-20260915`. [Acceptance receipt](../evidence/gcp/space-stopping-acceptance-20261010T001049Z-8b6cab/receipt.json).

The [custody verifier](../checks/verify_laplace_acceptance.py) checks the input archive, each archived source, exact current/staged Git bytes, all theorem reports, the protected 636-export baseline and frozen pilot. Its [result](../evidence/stopping/laplace-formal-verification.json) invokes no Lean. No new sample, manuscript or DOI change occurred.

The first attempt failed the disk preflight before upload or compilation. Subsequent runs used a separate task-owned `/dev/shm` build cache on GCP, seeded by a copy of the preserved accepted cache. Sources, immutable inputs and raw logs remained on persistent storage and were collected locally. Development failures and their diagnostics remain under `evidence/gcp/space-stopping-*`. The terminal development cache was observed absent by cleanup; its exact task link was checked and removed after collecting the failure. Existing caches and other campaigns were preserved. The successful acceptance used a foreground remote build/audit session. The accepted RAM cache is ephemeral and is not evidence required to reproduce the result.

After acceptance collection and a no-other-Lean-work check, the campaign-owned VM was stopped and verified `TERMINATED` at `2026-10-10T00:18:16.170545+00:00`. [Cleanup receipt](../evidence/gcp/space-stopping-acceptance-20261010T001049Z-8b6cab/cleanup.json). There were no workstation Lean invocations or hosted-CI proof runs.

## Next obligation

Formalize the first-n stopping experiment on the accepted infinite iid stream. Prove almost-sure termination from positive Z, then factor each terminal prefix-pattern event using `retained_pattern_submeasure_law` and sum the disjoint stopping-time fibers. This should yield the first-n retained iid law, including n=0, and its marked-volume confidence composition. A natural implementation uses the least prefix with retained count n and a measurable fallback on nontermination. Merely assuming that law or assuming termination would leave the obligation open.

Remaining to-do list: first-n stopping and almost-sure termination; complete admissible geometric/marked-law confounding and randomized obstruction; S040 final decision audit. S039, S042-S044 and S046 remain selected.
