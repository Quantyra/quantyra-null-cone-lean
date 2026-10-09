# Marked-volume analytic acceptance and remaining formal boundary

2026-10-09. Final accepted GCP run: [`space-marked-volume-calibration-20261009T193939Z-b7f4f7`](../evidence/gcp/space-marked-volume-calibration-20261009T193939Z-b7f4f7/receipt.json). The full root build completes 3,037 jobs and the audit prints 532 exact theorem types and axiom reports, including 24 new endpoints. There are zero warnings and only `propext`, `Classical.choice` and `Quot.sound` dependencies. Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` are pinned. No Lean/Lake invocation ran locally or on GitHub.

The [capture manifest](../evidence/gcp/space-marked-volume-calibration-20261009T193939Z-b7f4f7/capture-manifest.json), raw logs and source archive bind the accepted input. [Custody verification](../evidence/marked-volume/formal-verification.json) independently compares all accepted source hashes with both the worktree and staged Git blobs, inspects every report, and checks preservation of the pre-campaign baseline. These checks execute no Lean. They establish source identity and reported kernel dependencies; this manual semantic map establishes correspondence to the ordinary argument.

| Ordinary argument | Accepted formal endpoint and exact scope |
| --- | --- |
| Iid measurable membership has two-sided Hoeffding concentration | `iid_indicator_hoeffding`, for every probability space and positive n. |
| Two fixed chronological anchor flags determine interval membership | `marked_interval_code_measurable`, `marked_fraction_indicator`, `marked_fraction_relabel`; the input is their Boolean conjunction, a projection of marked chronological observations. The relation and anchors are fixed parameters. |
| Concentration applies to the actual observed-code law | `marked_interval_actual_law_hoeffding`; `markedIntervalLaw` is the pushforward of the actual product sample measure. |
| Integrating bounded retention constrains physical interval mass | `retention_integral_bounds`, `retention_mass_identification`, `retained_physical_identification`; both inside and outside integrals are derived, not assumed equal to the desired target. |
| Detection reweights and normalizes the sampling law | `retained_measure_apply`, `retained_measure_real_apply`, `retained_measure_probability`, with `retention_total_positive`; the normalized density is `pi / integral pi`. |
| Identification bounds are increasing and compose with clipped sampling intervals | `retention_denominators`, `retention_lower_mono`, `retention_upper_mono`, `retention_interval_composition`, `marked_fraction_unit`, `marked_endpoints_unit`, `marked_endpoints_cover`. |
| Complete analytic physical-volume failure bound | `marked_volume_retention_coverage` and `retained_marked_volume_coverage`, for the actual marked-code law under the normalized retained measure. |
| Exact rational 95% calibration | `marked_hoeffding_95`, `marked_rational_radius_95`, `retained_marked_volume_95`: nonnegative rational r satisfying `n*r^2>=2` gives failure at most 1/20. The executable analytic method checks this condition using integers and fractions. |

Theorems reside in [MarkedVolume.lean](../QuantyraNullCone/MarkedVolume.lean) and [MarkedThinning.lean](../QuantyraNullCone/MarkedThinning.lean). The last theorem assumes a probability measure mu, integrable pi bounded everywhere between positive a and b, positive sample count, a measurable marked interval and the rational radius guard. In the physical specialization mu is normalized metric volume and the relation is chronology. The theorem is dimension independent; it is not a proof that an arbitrary instrument satisfies that model. The upper bound b<=1 is needed to interpret pi as a retention probability; the normalized-weight theorem itself is valid for more general positive bounded weights.

## Explicit outstanding obligations

1. Prove the exact binomial count-law identity and finite-tail confidence inversion in Lean, then connect the rational binomial report checker. The primary binomial implementation currently has the complete ordinary proof, exact integer certificates, an independent artifact audit and numerical validation; it is not yet the subject of the new Lean coverage theorem.
2. Construct the iid thinning/conditional retained-sample or Poisson-process bridge formally. The present formal observation law starts from independent draws from the normalized retained measure. Its derivation from independently detected generated events remains an ordinary proof.
3. Certify the full S038 confounding example: admissible different physical targets, valid detectors, identical detected observations and the resulting estimation obstruction, including independent estimator seeds. No claim that the current mass algebra establishes that entire example is made.
4. Preserve the difference between mathematical report-checker soundness and Python execution semantics. Formal coverage assumes exact measured chronological flags and a valid known calibration bound; missing flags, noisy relations, post-sample anchors and real calibration error are not silently included.

These obligations keep S040 and S041 active. The zero-sample `[0,1]` fallback is tested and trivially covers a normalized volume, but the new positive-sample analytic theorem does not claim that executable branch as a formal endpoint. General lower-dimensional class admissibility, proper-time confounding and unrestricted physical metric reconstruction remain separate statements.

## Retained attempts

- `space-marked-volume-dev1-20261009T192321Z-292c31`: task-owned VM started; the first SSH attempt reached the boot window and failed, retry succeeded. Compilation found a relabeling rewrite and two missing `noncomputable` annotations. All logs are retained.
- `space-marked-volume-dev2-20261009T193030Z-75ea8d`: a set-membership simplification was needed in the probability-transfer proof. The failed run and read-only inspection failures are retained.
- `space-marked-volume-dev3-20261009T193559Z-563d15`: full acceptance of 529 exports, including the 21 new observation/retention endpoints.
- `space-marked-volume-calibration-20261009T193939Z-b7f4f7`: full acceptance of 532 exports, adding three exact 95% calibration endpoints. Source and dependency identities were verified before and after compilation. Task-owned cloud cleanup is retained in this run directory.

Remaining to-do list: the exact-binomial, process-construction and complete confounding obligations above; all other selected roadmap stories remain tracked in the planning repository.
