# Independent random counts and physical-volume coverage

2026-10-09, S040. This continues the [accepted finite generated-sample construction](thinning-certification.md) and the [ordinary process proof](independent-thinning-process.md). The six new modules described here have full exact-source GCP acceptance. S040 remains incomplete.

## Experiment and result

Let locations have probability law mu and let each location carry an independent uniform mark. A measurable detector retains a location x exactly when its mark is below pi(x), where `0<=pi<=1` and the mean retention `Z=integral pi dmu` is positive. The formal experiment uses an actual infinite iid stream of these pairs and an independent, natural-valued generated count N with arbitrary probability law Q. It inspects precisely the first N pairs and lists accepted locations in generation order.

For every retained count n, including n=0, the restricted law of that tuple is its count probability times `nu^n`, where `nu=pi*mu/Z`. On a count event of positive probability, its conditional law is therefore `nu^n`. Zero-probability counts need no conditional assertion. The result does not require a moment bound on N. Count independence is an explicit feature of the product input law; adaptive stopping is a separate experiment.

When N is Poisson with mean kappa, the retained count is Poisson with mean `kappa*Z`, and the same tuple factorization holds. The proof sums the actual binomial thinning probabilities and derives the exponential-series identity. The count/tuple result allows kappa=0 and mean retention one. Positive Z is required to define the normalized retained location law; the separate real/extended-real series identity also covers Z=0.

For any family of measurable maps F_n from n retained locations to a common observation space, the observed law is the count-weighted sum of the pushforwards of `nu^n`. Thus a bound that holds for every count also holds under the actual unconditional experiment. The theorem supplies the general composition rule. A concrete full marked-order quotient, finite counting-measure representation or explicit Laplace-functional formula still needs its corresponding formal map and proof.

## Confidence guarantee

With known bounds `0<a<=pi<=b<=1`, use R=b/a and the accepted retention transforms on a rational binomial interval. Require the report for each possible observed count to satisfy its exact validity contract, including the empty-sample report. Then the resulting physical interval-volume report has unconditional failure probability at most delta for any independent generated-count law Q. In particular, the same statement applies to Poisson generation without first conditioning on the retained count.

The original geometric-class specialization uses the actual density measure, strict null chronology, fixed marked anchors and executable rational report checker. The target is normalized physical interval volume. The true target appears only in the mathematical failure event `physicalReportFailure`; it is not supplied to the report algorithm. The report itself uses the observed membership count and declared detector bounds.

This construction does not justify sample-selected anchors, a geometry-dependent stopping rule, missing relations or correlated detections. It supplies neither absolute physical scale nor field validation. No new evaluation samples are generated, and the frozen pilot remains separate evidence.

## Ordinary-to-formal map

| Obligation | Module and endpoints |
| --- | --- |
| Actual infinite stream and finite-prefix law | `ThinningStream.lean`: `infinite_iid_prefix_law`, `generated_stream_prefix_law`, `stream_retained_submeasure_law`, `nat_product_restriction_map` |
| Independent random generated count | `ThinningMixture.lean`: measurable count/tuple maps, `mixed_retained_submeasure_series`, `mixed_retained_count_mass`, `mixed_retained_conditional_law` |
| Actual finite count mass and Poisson summation | `ThinningPoissonMass.lean`: `finite_retained_count_mass`, `retention_mean_unit`, `poisson_binomial_term`, `poisson_binomial_hasSum`, `poisson_binomial_series` |
| Poisson retained count and tuple | `ThinningPoisson.lean`: `poisson_retained_submeasure_law`, `poisson_retained_count_mass`, `poisson_retained_count_law` |
| Count-dependent observation and unconditional bounds | `ThinningFunctional.lean`: `mixed_retained_observable_law`, `poisson_retained_observable_law`, `mixed_retained_observable_bound`; count-fiber decomposition and total mass |
| Physical report coverage in the actual experiment | `ThinningMixedCoverage.lean`: `retained_physical_report_failure_bound`, `mixed_physical_report_coverage`, `InDensityClass.mixed_physical_report_coverage` |

## Verification

Run `space-process-acceptance-20261009T234349Z-57dc8e` passed **3,070 root-build jobs and 636 exact type/axiom reports**, including all 29 new theorems and two named probability instances. There were zero warnings and only `propext`, `Classical.choice` and `Quot.sound`. Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` ran on `quantyra-lean-builder-01`, `us-central1-a`, project `quantyra-lean-cert-20260915`. All 167 captured sources and pinned dependency identities were checked before and after. [Acceptance receipt](../evidence/gcp/space-process-acceptance-20261009T234349Z-57dc8e/receipt.json).

The [custody verifier](../checks/verify_process_acceptance.py) checks the input archive and each archived source, exact current and staged Git bytes, all full type/axiom reports, the protected preceding baseline and the frozen pilot. Its [result](../evidence/process/formal-verification.json) records the checks. The verifier invokes no Lean, and Python runtime semantics are not Lean-certified.

Development failures remain preserved under `evidence/gcp/space-process-*`. Only redundant build caches belonging to this campaign's terminal, already collected development runs were reclaimed after checking for other Lean work. Sources, raw logs, shared dependencies and accepted caches were preserved. The acceptance run used fresh immutable inputs and the preceding accepted build cache.

After collection and a no-other-Lean-work check, the campaign-owned VM was stopped and verified `TERMINATED` at `2026-10-09T23:49:14.962042+00:00`. The [cleanup receipt](../evidence/gcp/space-process-acceptance-20261009T234349Z-57dc8e/cleanup.json) links ownership to the first development run. No workstation Lean invocation, new pilot sample or manuscript/DOI change occurred.

Remaining to-do list: certify the explicit Laplace functional, stopping experiment and complete confounding endpoints; finish S040's decision audit. S039, S042-S044 and S046 remain selected.
