# Independent detection: finite generated samples

2026-10-09, S040. This develops the finite generated-sample portion of the [complete ordinary thinning proof](independent-thinning-process.md). The generated sample consists of N iid pairs `(X_i,U_i)` with location law mu and independent uniform marks. Event i is retained exactly when `U_i < pi(X_i)`, for a measurable detector with values in [0,1] and positive mean retention Z.

## Observation and theorem

The observed tuple contains the retained locations in generation order. Conditional only on its length being n, on an event of positive probability, its law is the n-fold product of the normalized retained measure `pi*mu/Z`. The implementation defines this actual tuple by the realized retention pattern and its increasing enumeration. A constant fallback makes the map total outside the selected count; the theorem removes all dependence on that fallback on the conditioning event.

This construction includes n=0 and detectors with mean retention one whenever the count event has positive probability. It does not condition on a specified pattern as an additional observed input. Instead, the proof first treats each pattern and then sums over every pattern with n retained entries, including zero-probability patterns.

The full coordinate-tuple law permits any common measurable observation of the retained locations. The coverage specialization in this package uses the two exact chronological anchor flags for each retained event, their interval membership count, and the accepted rational exact-binomial report. With known detector bounds `0<a<=pi<=b<=1`, applying the retention transforms with R=b/a covers the physical interval volume with failure probability at most the report's delta. The final original-class corollary uses the actual density measure, strict null chronology and the executable report-check predicate.

The anchors are fixed independently of the generated sample. The reported target is a normalized volume fraction; the result supplies neither unknown anchor matching nor absolute scale. Independence of the generated pairs and uniform marks is a hypothesis of this specific experiment.

## Ordinary-to-formal map

| Mathematical obligation | Module and substantive endpoints |
| --- | --- |
| The actual uniform-threshold event gives submeasure pi*mu, mass Z and normalized retained location law | `ThinningChannel.lean`: `detected_submeasure`, `detected_event_mass`, `detected_conditional_location`; finite-product conditioning and subset projection |
| Arbitrary prescribed retention pattern and detected-count mass | `ThinningSubset.lean`: `retained_subset_law`, `detected_count_atom` |
| Actual retained tuple in generation order | `ThinningSelected.lean`: measurable tuple maps, `ordered_pattern_conditional_law`, `retained_ordered_pattern_law` |
| Summation over all patterns of the observed length | `ThinningCount.lean`: `retained_pattern_submeasure_law`, `retained_count_submeasure_law`, `retained_count_conditional_law` |
| Actual generated experiment, marked observation and physical coverage | `ThinningCoverage.lean`: `generated_retained_marked_law`, `generated_retained_binomial_coverage`, `InDensityClass.generated_retained_binomial_coverage` |

## GCP acceptance and custody

Run `space-thinning-acceptance-20261009T224115Z-70f2d5` passed the full GCP root build with **3,047 jobs and 605 exact type/axiom reports**, including all 28 new theorems in these five modules. There were zero warnings and only `propext`, `Classical.choice` and `Quot.sound`. Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` ran on `quantyra-lean-builder-01`, `us-central1-a`, project `quantyra-lean-cert-20260915`. All 160 captured source identities and pinned dependencies were checked before and after. [Acceptance receipt](../evidence/gcp/space-thinning-acceptance-20261009T224115Z-70f2d5/receipt.json).

The [local custody verifier](../checks/verify_thinning_acceptance.py) checks every captured file against current LF-normalized bytes and its staged Git blob, all 605 exact types/axiom reports, the archive hash, protected baseline and frozen pilot. It invokes no Lean. Its [result](../evidence/thinning/formal-verification.json) records those checks. Python runtime semantics are not Lean-certified.

Development failures remain retained. The first boot-time SSH failure preceded launch; its workspace was verified absent. Development run 8 exhausted disk while copying a cache, before Lean started. Its empty exit marker and missing finish timestamp remain explicitly unverified, rather than being converted to a proof failure or success. After verifying earlier terminal failures and their archived evidence, only six redundant task-owned build caches were removed; sources, raw logs, shared dependencies and accepted caches were preserved. [Infrastructure disposition](../evidence/gcp/space-thinning-coverage-dev8-20261009T223151Z-c58346/disposition.json), [reclamation receipt](../evidence/gcp/space-thinning-coverage-dev8-20261009T223151Z-c58346/read-223623.stdout.txt). A fresh immutable run then completed acceptance.

After collection and a no-other-Lean-work check, the VM started by this campaign was stopped and verified `TERMINATED`. The [cleanup receipt](../evidence/gcp/space-thinning-acceptance-20261009T224115Z-70f2d5/cleanup.json) links ownership to the initial start and records the final state. No local Lean invocation, new pilot sample or manuscript/DOI change was used.

## Remaining S040 endpoints

The finite-N result is one part of the selected story. The ordinary proof also treats an independent random generated count, Poisson generation and the resulting count/process law, and sampling until n acceptances with almost-sure termination. These require their own formal composition and acceptance. The complete S038 confounding endpoint still needs admissible original-class geometries, globally valid detector extensions, equal full marked-order/process laws, separated physical targets and the obstruction for arbitrary independently randomized estimators. An equal product of two functions alone is insufficient.

The frozen pilot and its previously accepted S041 report calibration remain separate evidence. No new samples or field-detector validation are introduced here. The [joint volume/calibration rate](physical-volume-calibration-rate.md) is an ordinary S046 result with separate formal obligations.

Remaining to-do list: random-count, Poisson, stopping and complete confounding certification; S040 final decision audit and delivery. S039, S042-S044 and S046 remain selected.
