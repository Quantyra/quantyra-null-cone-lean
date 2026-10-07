# Lean verification checkpoint

2026-10-06, E002/S005. The complete selected finite realizer rank theorem is kernel checked, including a specialization matching the original specification. The full spacetime inverse bound remains a mathematical prose proof; it is not claimed as a compiled Lean theorem.

## Checked statements

| Theorem | Checked scope | Reported axioms |
| --- | --- | --- |
| `Realizer.five_edge_forcing` | Every two-order realizer propagates orientation along the five-edge comparable-witness path. | None |
| `Realizer.global_orientation` | One anchor orientation determines all eligible pairs, conditional on actual witness existence. | None |
| `occupied_grid_global_orientation` | Real-coordinate grid occupancy supplies the anchors and witnesses and yields one common orientation for all separated interior incomparable pairs. This discharges the geometric witness hypothesis rather than assuming it. | `propext`, `Classical.choice`, `Quot.sound` |
| `abs_rank_sub_le_disagreements` | Absolute difference of the real-coerced predecessor ranks is bounded by the number of pairwise comparison disagreements. | `propext`, `Classical.choice`, `Quot.sound` |
| `verticalStrip_card_le` | Empirical marginal error at most 2r implies a strip count at most 10rn for each interior event. | `propext`, `Classical.choice`, `Quot.sound` |
| `comparisons_agree` | Both coordinate comparisons agree outside the boundary and narrow vertical strip after the common orientation is chosen. | `propext`, `Classical.choice`, `Quot.sound` |
| `finite_realizer_rank_rigidity` | For ANY two-order realizer, ONE Boolean swap gives BOTH rank errors <=30rn for EVERY interior event. Witnesses, the strip count, and the disagreement bounds are derived, not assumed. | `propext`, `Classical.choice`, `Quot.sound` |
| `finite_realizer_rank_rigidity_specified` | Matches the original selected statement with r=1/m, unit-square coordinates, distinct coordinates, no grid-line ties, both marginal bounds, and normalized boundary fraction <=20r. | `propext`, `Classical.choice`, `Quot.sound` |

Sources are `QuantyraNullCone/Realizer.lean`, `Grid.lean`, `Counts.lean`, and `Bridges.lean`. The root module imports all four. No source contains `sorry`, `admit`, or a new axiom declaration. The axiom printer reports no `sorryAx` for the listed theorems. The foundational dependencies listed above are mathlib's ordinary Lean dependencies, not added geometric assumptions.

## Reproducible environment and checks

Lean executable: v4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, Windows x86_64. Mathlib checkout and manifest pin: `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Dependency revisions are saved in `lake-manifest.json`.

Executed the final `lake build QuantyraNullCone`: exit code 0, build completed successfully with 984 jobs. Each listed axiom report appeared in the build output. `lake env lean checks/Audit.lean` also exited zero and printed the full types and axiom dependencies of both final theorems. Inspection confirmed that the existential Boolean swap precedes the universal event quantifier and is shared by both inequalities. Standalone checks of the proof modules exited zero. This verifies all six components of the selected target, not the probability or continuous-density portions of the full inverse theorem.

For a fresh checkout, suppress the broad automatic cache hook during dependency update with `MATHLIB_NO_CACHE_ON_UPDATE=1`, then fetch only these module closures:

```text
lake update
lake exe cache get Mathlib.Data.Real.Archimedean Mathlib.Algebra.Order.Floor.Semiring Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
lake build QuantyraNullCone
lake env lean checks/Audit.lean
```

The environment variable applies to `lake update`; restore any previous value afterward. The focused cache fetched and decompressed 963 files successfully. An earlier broad cache attempt and the first focused retry ran out of disk space; those attempts failed and are not counted as verification. Task-generated temporary archives and failed extracted artifacts were cleaned, and the subsequent focused attempt and library build succeeded. Source repositories and unrelated files were preserved.

## Scope beyond this target

2026-10-06 S013 continuation: `Cumulative.lean` adds the inclusive rank/CDF identity, `32r` coordinate rigidity, the empirical rectangle sandwich with one exceptional-point penalty in each direction, and the deterministic `87r` CDF consequence. Both final deterministic exports compiled locally and passed the exact-type/dependency audit, using only the same three standard foundations. The CDF consequence explicitly assumes population threshold stability and latent empirical accuracy; it does not prove the concrete model's analytic or probability premises. `Model.lean` defines the original Euclidean-Lipschitz density class, restricted density measure, iid sample/order law, CDF, transpose, half-L1 finite-law TV, Delta_N and coefficient distance. Its order-only observable measurability theorem compiled. Uniform marginal/CDF facts and the later concentration/interpolation/separation/assembly stages remain active work, not completed full inverse verification.

`Measures.lean` compiled the concrete normalization proof: smoothness gives continuity and compact integrability, Fubini plus the original unit marginals gives density integral one, and nonnegative integration identifies the with-density measure's total mass. The iid product law and measurable directed-order pushforward are then proved probability measures. The density/order-law normalization exports report only `propext`, `Classical.choice`, and `Quot.sound`. These are concrete consequences of `InDensityClass`, not assumed normalization hypotheses.

The continuation uses the same pinned Lean/mathlib versions and user-owned Windows tools. Additional focused cache targets are listed in `.github/workflows/verify.yml`; caches and tools are outside versioned proof artifacts. The historical build record above remains evidence for its original finite target. Dan's current workflow is open-source, decentralized informal feedback; specialist review and downstream adoption are not publication prerequisites.

Further S013 continuation: `DensityCDF.lean` compiled the real density-measure/integral identities, both uniform marginal measures for arbitrary measurable real sets, all-real CDF threshold stability, and the two unit-edge CDF identities. Threshold stability follows by bounding each rectangle difference by a coordinate interval strip, using the proved uniform marginal measures and restricted-volume monotonicity. The only model premise is the original `InDensityClass`; the proof does not postulate marginal-measure equality or threshold stability. Grid concentration, boundary counts and full inverse assembly remain separate unfinished obligations.

The original selected statement is a specialization of a stronger theorem: the rank proof only needs the v marginal bound; unit-square and no-grid-line assumptions are not needed once occupancy, the boundary count, and the two coordinate injectivity hypotheses are supplied. The original hypotheses were retained explicitly in the specified specialization to make the scope comparison checkable.

Remaining to-do list for the original finite target: none. Remaining selected S013 work: prove the concrete measure/probability/analytic premises, assemble the full all-N inverse theorem and identifiability, and audit the final exports and delivered commits. Originality remains provisional pending fuller source comparison.

## Exact-source GCP verification and deterministic grid bridge

2026-10-06 (UTC 2026-10-07) GCP verification: run `space-20261007T093129Z-retry1` on `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`, used native Linux Lean 4.30.0. The exact prior `22e0059` baseline built with 2583 jobs and twelve export audits; the candidate built with 2584 jobs and sixteen export audits. Both exited zero, with no compiler warnings and only `propext`, `Classical.choice`, and `Quot.sound` in audited exports. Per-file source hashes were checked before and after compilation, and every tracked dependency byte was checked against the nine pinned Git trees. The [receipt](../evidence/gcp/space-20261007T093129Z-retry1/receipt.json), [raw logs](../evidence/gcp/space-20261007T093129Z-retry1/logs), [source manifest](../evidence/gcp/space-20261007T093129Z-retry1/capture-manifest.json), [dependency verification](../evidence/gcp/space-20261007T093129Z-retry1/dependency-source-verification.json), and retained exact source archive document the outcome. The initial cache CLI setup failure is retained separately and was not proof verification. The VM was stopped after evidence collection and a check for other Lean/Lake work; final state is TERMINATED.

`GridAccuracy.lean` proves F1 from actual grid-vertex discrepancy: both marginal errors are at most `2r`, the boundary count is at most `20rn`, and latent empirical CDF discrepancy is at most `3r` at every real threshold. The boundary proof uses the sharper `r` errors at 4r and 1-4r. The final export `finite_realizer_cumulative_error_of_grid_vertices` derives the normalized-rank `87r` bound for every realizer with one global Boolean swap. Its premises are K, unit-square coordinates, positive sample size, `m>=16`, `mr=1`, coordinate injectivity, occupancy and vertex discrepancy. No marginal, boundary, population stability or reconstruction conclusion is assumed. Occupancy, injectivity and vertex accuracy still require the separate probability proof.

Earlier local and hosted verification records are preserved as historical/supplementary evidence. This exact-source GCP run provides current certification support for the prior twelve exports and the four new deterministic exports. Probability, density interpolation, observable-TV separation, all-N assembly and identifiability remain unfinished; no full inverse formalization is claimed.

## Original iid reconstruction probability — F2

2026-10-07 F2: exact-source GCP run `space-sampling-20261007T103552Z-585351` passed the root library build (2898 jobs), the full exact-type/dependency audit of thirty-two selected exports, and the existing finite/grid checks. No compiler warnings, errors or admitted dependencies remain. The only audited foundations are `propext`, `Classical.choice` and `Quot.sound`. Source SHA256 values were checked before and after execution, and dependency revisions/clean tracked trees match the pinned nine-package manifest. [Receipt](../evidence/gcp/space-sampling-20261007T103552Z-585351/receipt.json), [raw logs](../evidence/gcp/space-sampling-20261007T103552Z-585351/logs), [source capture](../evidence/gcp/space-sampling-20261007T103552Z-585351/inputs.tar.gz) and [development index](../evidence/gcp/sampling-development-index.json) retain both the final result and unsuccessful attempts. The initial acceptance upload encountered the instance's idle shutdown before launch; after confirming guest shutdown and completing stop/restart, the same immutable capture was submitted. The VM is now TERMINATED after evidence collection and a no-other-Lean-work check.

`Sampling.lean` proves square support almost surely, null fixed coordinate/grid lines, open-cell density mass at least `r²/2`, the exact iid miss probability and occupancy failure at most `m² exp(-nr²/2)`. `Coordinates.lean` derives uniform coordinate pushforwards and almost-sure coordinate injectivity from the iid product law and atomless uniform marginals. `Concentration.lean` derives the indicator and empirical CDF tail `2 exp(-2nr²)` and vertex-union failure `2(m+1)² exp(-2nr²)`. Only different iid sample points are treated as independent; neither the two axes within one point nor overlapping grid events are assumed independent.

`GoodSamples.lean` combines the null events and both actual failure bounds, then applies F1 to every realizer. `ProbabilityRate.lean` proves the original fourth-root grid's integer rounding: for `n>=65536`, `m=floor(sqrt(sqrt n))` is at least sixteen, the two failure terms sum to at most `3/32<1/10`, and `87/m<=174 n^(-1/4)`. The exported `InDensityClass.reconstruction_probability` assumes only the original K and `n>=65536`. Its conclusion is sample-measure mass at least `9/10` for the event that every realizer admits one global Boolean swap giving the all-real-threshold normalized-rank CDF bound `174 n^(-1/4)`. No occupancy, concentration, null-tie, reconstruction or final inverse conclusions are hypotheses of that export.

F2's original reconstruction probability bound is now formalized. This does not complete S013: actual density interpolation, the measurable order-only selector and TV separation, the all-N coefficient theorem, identifiability and final scope audit remain required. Label/unlabel and proper-time formalization status must be reported separately. The improved logarithmic-grid estimate remains a separate prose result.

Remaining to-do list: F3 boundary-valid density interpolation; F4 order-only observable selection and TV separation; F5-F6 full inverse/identifiability and final audit.

## Boundary-valid density interpolation — F3

2026-10-07 F3: exact-source GCP run `space-interpolation-20261007T112652Z-43e687` passed the complete root build (2899 jobs) and all thirty-five selected exact-type/dependency reports, with zero compiler warnings and only `propext`, `Classical.choice` and `Quot.sound`. Source SHA256 values were checked before and after execution; all nine dependency revisions and clean tracked source trees match the pinned manifest. [Receipt](../evidence/gcp/space-interpolation-20261007T112652Z-43e687/receipt.json), [source archive](../evidence/gcp/space-interpolation-20261007T112652Z-43e687/inputs.tar.gz), [raw logs](../evidence/gcp/space-interpolation-20261007T112652Z-43e687/logs) and [development index](../evidence/gcp/interpolation-development-index.json) retain the final outcome and failed inputs. The VM is TERMINATED after collection and a no-other-Lean-work check.

`DensityInterpolation.lean` proves the original `coefficientDeviation(rho,sigma)^3<=2048 epsilon` for actual densities in K under all-threshold population CDF discrepancy at most epsilon. It proves real rectangle mass by four-corner CDF inclusion/exclusion, identifies actual density-measure mass with the product-volume density integral, and obtains an actual supremum-attaining point by continuity on the compact square. Around that point, a boundary-safe square of side `delta/16` lies inside the domain and has signed density difference at least `delta/2`; its signed integral is at least `delta^3/512`. The proof treats both maximizing signs and the zero case. It never substitutes the with-density measure of a clipped signed difference and does not assume the interpolation or coefficient conclusion.

F0-F3 are formalized intermediate stages. The measurable order-only selector, observable-TV separation, original all-N coefficient theorem and identifiability remain unfinished. The logarithmic-grid estimate remains a separate prose result; no full inverse certification or originality clearance is claimed.

Remaining to-do list: F4 observable selection/TV separation; F5-F6 all-N inverse/identifiability and final audit.
