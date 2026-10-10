# S047 feasibility decision and acceptance

2026-10-10. **Park a separate loss-only quantum estimation project.** Retain
the calibrated exact-binomial report and its formal transfer. The report can
be informative, but it is exactly the established nuisance-projection
baseline given the same observations. There is no statistical improvement to
develop into a separate quantum-method manuscript in this candidate.

This resolves the selected S047 feasibility study, not all possible quantum
applications. One model and one frozen evaluation were used; no revised
candidate, further simulation or standalone quantum paper is commissioned.
The [source comparison and field screen](quantum-measurement-sources.md)
keep a substantive causal-set field project behind its missing observation
and stability bridge. A failed advantage gate is not an impossibility result
for other detectors, experiments or methods.

## Mathematical result and limits

The [ordinary model argument](quantum-measurement-model.md) specifies a
single-qubit Pauli-Z target, loss-only detection with each efficiency in
[1/2,1], complete positive/negative/no-click probe records, and independent
trusted-basis calibration counts. For all admitted parameters and all probe
and calibration block sizes, the report covers the observable with
probability at least 95%. Each calibration block has its own error budget;
the two probe counts are not assumed independent.

Without calibration, the admitted models `(p,eta+,eta-)=(2/5,3/4,1/2)` and
`(3/5,1/2,3/4)` have the same complete ternary-record law at every probe
sample size, but observable values -1/5 and +1/5. Every estimator, including
independently randomized estimators, has failure probability at least 1/2
at one model for any error radius strictly below 1/5. Calibration breaks
that pair's indistinguishability; the obstruction is not asserted with
positive calibration data.

The density-matrix/POVM multiplication, sharp population projection,
sampling/calibration width decomposition and matched-baseline algebra are
ordinary arguments. Formal probability starts from the explicit induced
ternary Born probabilities; complex-matrix positivity and physical hardware
behavior are not certified by Lean. No full-state tomography, validated
detector model, minimax quantum rate, optimal confidence width or new physics
is claimed. Trusted preparation, stable efficiencies, loss without dark
counts/misclassification and independent trials remain model hypotheses.

## Frozen numerical comparison

Protocol and code were committed and pushed as
`ec87f42064ee2330d181dcbc2ad17975b1edead2` before execution. The
[frozen protocol](quantum-measurement-protocol.md) and
[machine-readable design](quantum-measurement-protocol.json) distinguish
exact small-sample laws from deterministic near-mean cost cases. The complete
[study](../evidence/quantum-measurement/feasibility-v1/manifest.json),
[summary](../evidence/quantum-measurement/feasibility-v1/summary.json) and
[independent audit](../evidence/quantum-measurement/feasibility-v1/audit.json)
are retained with their source payloads.

| Prespecified check | Result |
| --- | --- |
| All complete count tuples for n,m in {0,4,12} | 20,865 checked; candidate and independent linear-feasibility baseline endpoints and fallback agree exactly. |
| Exact finite-law coverage at 27 boundary/interior/main/withheld strata and nine budgets | All 243 cells pass; minimum is 2035/2048 = 0.99365234375. There is no Monte Carlo error in these rational coverage sums. |
| Exact marginal tail certificates | All 190 distinct reports checked again by a different integer polynomial evaluator. |
| Representative cost/width cases | All 81 complete; these are deterministic rounded near-mean counts, not random coverage or expected-error replicates. |
| Nominal theta radius <=0.1 at n=2048,m+=m-=2048 | All 27 diagnostic cases pass; largest realized radius 0.0987548828125. |
| At least 10% mean radius improvement over matched established inference | Fails: improvement is exactly zero, as proved before data. |
| Restricted joint-likelihood diagnostics | All 243 optimizer starts report success; all returned likelihoods independently re-evaluated, maximum numerical discrepancy below 9.1e-13. This is not a global-maximum certificate. |
| Execution resources | 6.15 seconds supervised wall, 102.71 MiB peak RSS, 115.76 MiB peak committed memory; below the 900-second/768-MiB limits. |
| Independent arithmetic/artifact audit | 8.60 seconds supervised wall, 32.63 MiB peak RSS; all checks pass. |

Known-detector oracle intervals and bias-ignoring conditional-detection
estimates remain explicitly different-information or misspecified diagnostics.
At the 27 largest-budget fixed-count cases the candidate's average radius is
about 0.04259 and the oracle's about 0.03353. These are averages across the
fixed design, not expected widths under sampling. The restricted joint fit
uses the matched likelihood, not the original NIST optimizer/package; no
bootstrap interval is presented as a uniform finite confidence comparator.

The lower bound 0.99365 is only the minimum on the finite numerical grid.
The uniform 95% guarantee comes from the theorem. The useful diagnostic
widths do not establish high-probability useful width at the larger budget.
The investment decision rests on exact equality to the established baseline,
not on a claim that calibrated inference is uninformative.

## GCP acceptance and ordinary-to-formal map

Full acceptance run:
`space-qubit-acceptance-20261010T141342Z-df8453`, project
`quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`,
zone `us-central1-a`. The
[receipt](../evidence/gcp/space-qubit-acceptance-20261010T141342Z-df8453/receipt.json)
records the root build, 1,288 exact type/axiom reports, zero warnings and
source/dependency identities checked before and after execution. The build
completed all 3,195 dependency jobs; unchanged targets were reused. There
was one full acceptance audit after focused development, not a full audit
after every helper lemma. All Lean/Lake execution was on GCP.

| Mathematical component | Formal statement and scope |
| --- | --- |
| Ternary probabilities and complete observations | [QubitLoss.lean](../QuantyraNullCone/QubitLoss.lean): `qubit_click_ranges`, `qubit_trial_probability`, `qubit_trial_click_masses`, `qubit_record_probability`. The full probe vector and both calibration counts are retained. |
| Actual count marginals | `qubit_probe_count_preserving`, `qubit_calibration_plus_preserving`, `qubit_calibration_minus_preserving` derive the four binomial marginals of the actual record law; probe-count independence is never substituted. |
| Computable report algebra and uniform finite coverage | [QubitConfidence.lean](../QuantyraNullCone/QubitConfidence.lean): `qubit_box_report_covers`, `binomial_marginal_report_failure`, `loss_only_qubit_confidence`, using the existing exact rational tail predicate and generic binomial theorem. The endpoint allows unequal and zero calibration sizes. |
| No-calibration limitation for arbitrary estimators | `qubit_confounded_full_probe_law` and `qubit_uncalibrated_randomized_obstruction`, reusing the accepted general identical-law testing argument. |

The confidence theorem is conditional on valid rational marginal endpoint
tables for every possible count. Python proposes and exactly checks these
certificates; its source, optimizer and interpreter are not Lean verified.
No complex density-matrix library or universal detector model is hidden in
the formal scope. The separate source/proof map makes that boundary explicit.

The input archive contains 268 tracked source/dependency-control files; its
SHA256 is `4b986c497b5268ba95e16d11e5ac7ecd4b013680b87a1a19b8fb7a07ed0f1b6b`.
Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` remain
pinned. Audited dependencies are limited to the existing standard axioms
`propext`, `Classical.choice`, and `Quot.sound`; no new axiom or admitted proof
was introduced. Previous accepted Lean files are unchanged apart from root
imports and the expanded audit; the two new modules supply this result.

Two development failures are preserved with exact inputs and terminal logs:
one needed noncomputable annotations and removal of an unused simp argument;
the other needed rational-to-real coercion normalization. An initial SSH
startup transport failure is also retained. None changed the mathematical
claim or the frozen study. The accepted source is checked against Git by
[the delivery verifier](../tools/verify_quantum_delivery.py).

The task-owned VM's final status and persistent-cache verification are in
the [cleanup receipt](../evidence/gcp/space-qubit-acceptance-20261010T141342Z-df8453/cleanup.json).
The [delivery record](../evidence/quantum-measurement/delivery.json) verifies
raw Git custody for numerical evidence, source payloads and all three cloud
attempts. Retained byte hashes are checked without rerunning Lean locally.

## Investment and manuscript disposition

Retain this as an open, reusable certification example. Attribute the generic
binomial, calibration, projection and quantum-tomography ingredients to the
reviewed sources. Do not promote the routine specialization or an increased
proof count as a new quantum-estimation method. No new quantum manuscript or
DOI is warranted by this comparison. A future methods exposition may use
the example while preserving these limitations.

Reopen this candidate only for a concrete observation/model need and a
complete argument showing a new useful guarantee or advantage over a method
with the same information and coverage requirement. The conditional field
branch needs a matched order/scale/propagator-stability bridge in its own
story; higher-dimensional branches retain S042/S043's existing gates.
The separately proposed S048 physical-volume manuscript remains the next
packaging opportunity, outside this completed feasibility scope.

Published manuscripts, earlier frozen experiments and accepted source
evidence remain preserved. Open-source decentralized informal review is the
workflow; specialist review and downstream adoption are not completion gates.

Remaining to-do list: none for S047. S048 manuscript preparation is proposed
separately; new quantum/field research is gated as above.
