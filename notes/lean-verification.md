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

## Order-only selector and observable TV separation — F4

2026-10-07 F4: exact-source GCP run `space-observable-20261007T114943Z-041e63` passed the complete root build (2901 jobs) and all forty-two selected exact-type/dependency reports, with zero compiler warnings and only `propext`, `Classical.choice` and `Quot.sound`. All source SHA256 values were verified before and after execution; the nine dependency revisions and clean tracked source trees match the pinned manifest. [Receipt](../evidence/gcp/space-observable-20261007T114943Z-041e63/receipt.json), [immutable inputs](../evidence/gcp/space-observable-20261007T114943Z-041e63/inputs.tar.gz), [raw logs](../evidence/gcp/space-observable-20261007T114943Z-041e63/logs) and [development index](../evidence/gcp/observable-development-index.json) preserve the terminal outcomes, including the runner-path failure before Lean and subsequent failed proof attempts. The VM is TERMINATED after collection and a no-other-Lean-work check.

`OrderSelector.lean` proves existence of a realizer for coordinate-injective samples, chooses one realizer from the observed code alone and fixes a zero output for invalid codes. The selector does not depend on either density or latent coordinates. Every selected CDF evaluation and its good-code event are measurable because the observed code space is finite. The actual sample coordinate null/tie result eliminates the vacuous invalid-realizer case when transferring the previously proved reconstruction probability: the observed-law good-code event has mass at least `9/10` for `n>=65536` and error `174 n^(-1/4)`.

`FiniteTV.lean` derives the event-difference bound from the exact half-L1 singleton-mass definition for any two finite probability laws. Applying it to those two good-code sets proves an overlap whenever the actual directed-order TV is below `4/5`. A common observed code, the same selector and the two globally fixed Boolean alignments give either `|F_rho(s,t)-F_sigma(s,t)|<=348 n^(-1/4)` at every real threshold, or `|F_rho(s,t)-F_sigma(t,s)|` bounded by the same quantity at every real threshold. Orientation is one global choice, never a choice per threshold. No concentration, reconstruction, overlap or CDF conclusion is an extra premise of the main export.

F0-F3 and F4's observable-CDF separation are formalized intermediate stages. The frozen F4 transpose-isometry obligation is carried into F5 assembly; it has not been compiled. The transpose density/CDF identity, original all-N coefficient theorem, identifiability, label-law equivalence and final scope reconciliation remain unfinished. The logarithmic-grid improvement and proper-time consequence remain separate prose results. These exports do not yet certify the full inverse theorem.

Remaining to-do list: F5-F6 transpose bridge, all-N inverse/identifiability, label/time scope and final audit.

## All-N inverse and all-law identifiability

2026-10-07: exact-source GCP run `space-identifiability-20261007T121032Z-4c3c47` passed the complete root build (2904 jobs) and all fifty-five selected exact-type/dependency audits, with zero compiler warnings and only `propext`, `Classical.choice` and `Quot.sound`. Source SHA256 values were verified before and after execution; all nine pinned dependency revisions and clean tracked source trees match the capture. [Receipt](../evidence/gcp/space-identifiability-20261007T121032Z-4c3c47/receipt.json), [immutable source](../evidence/gcp/space-identifiability-20261007T121032Z-4c3c47/inputs.tar.gz), [raw logs](../evidence/gcp/space-identifiability-20261007T121032Z-4c3c47/logs) and [development index](../evidence/gcp/inverse-development-index.json) retain the final result, the earlier warning-bearing successful inverse build and the failed identifiability attempt. The VM is TERMINATED after evidence collection and a check for other Lean/Lake work. The deprecated `push_neg` warning was fixed in source, not hidden or filtered.

`Transpose.lean` closes the carried transpose obligation: original K is invariant under coordinate exchange, with the same Euclidean Lipschitz constant, exchanged interval marginals and smooth-neighborhood pullback. Product-volume swap preserves the restricted square volume. A measurable-embedding change of variables gives the actual density-measure transport and `F_transpose(s,t)=F_sigma(t,s)` at all real thresholds; the transport identity is valid for any density function because no unnecessary global measurability premise is imposed. Coefficient deviation is invariant when both densities are transposed.

`InverseRate.lean` proves nonnegativity and the upper bound one for actual coefficient/conformal discrepancy, bounds each TV_k by the actual finite supremum Delta_N, and applies F4/F3 in the globally selected orientation. The cubic bound is `712704 n^(-1/4)`, below `(100 n^(-1/12))^3=1000000 n^(-1/4)`. The high-TV branch uses discrepancy at most one; the small-sample branch proves `1<=100 N^(-1/12)` explicitly. The exported `InDensityClass.full_inverse` assumes only K for both densities and `N>=2`, and concludes precisely `d_conf<=100(N^(-1/12)+Delta_N)` for the actual iid labeled directed-order laws. No reconstruction, interpolation, normalization, overlap or inverse conclusion is a hypothesis.

`Identifiability.lean` proves coefficient deviation zero iff the two densities agree everywhere on the square, and conformal distance zero iff one global identity/transpose gives that equality. Equality of all directed-order laws makes every actual Delta_N zero. Taking the negative real-power rate to zero yields conformal distance zero, then the density-equality conclusion. Nothing asserts equality of arbitrary density extensions outside the square.

The original all-N coefficient estimate and its all-law consequence are now compiled for labeled directed-order laws. The label/unlabel TV equivalence remains a prose proof and must be reconciled before claiming a formally verified unlabeled-observable theorem. Proper-time and logarithmic-grid Lean proofs remain separately selectable. The archived 0.2.0 manuscript and its DOI payload are preserved; its formal-scope description is historical, and these later software proofs do not alter that deposit.

Remaining to-do list: formal labeled/unlabeled law equivalence and final original-observable scope/type/dependency audit.

## Original unlabeled-observable completion

2026-10-07 final original-observable bridge: exact-source GCP run `space-unlabeled-20261007T123238Z-759aaa` passed the complete root build (2907 jobs), all sixty-eight selected exact-type/dependency audits, and before/after source SHA256 plus nine pinned dependency identity/clean-tracked-tree checks. It exited zero with no compiler warnings and only `propext`, `Classical.choice` and `Quot.sound`. The [receipt](../evidence/gcp/space-unlabeled-20261007T123238Z-759aaa/receipt.json), [immutable inputs](../evidence/gcp/space-unlabeled-20261007T123238Z-759aaa/inputs.tar.gz), [raw logs](../evidence/gcp/space-unlabeled-20261007T123238Z-759aaa/logs) and [development index](../evidence/gcp/unlabeled-development-index.json) preserve the final and failed attempts. The first SSH preflight closed during boot before launch; the same captured input was subsequently launched after proving its cloud workspace absent and no other Lean/Lake work active. The task-started VM is TERMINATED after collection.

`Exchangeability.lean` proves that every sampled chronology is a strict partial order, iid sample-index permutations preserve the actual sample measure, sampled chronology commutes with simultaneous index relabeling, and the actual order law is exchangeable. `QuotientTV.lean` proves a general finite-map L1 identity when both singleton-mass functions are constant on each fiber, deriving pushforward singleton mass by finite sums and the absolute-value identity on a constant fiber. `Unlabeled.lean` defines the finite measurable quotient by simultaneous index permutations, proves quotient equality iff directed-order isomorphism, and proves normalization of its actual pushforward law. It derives fiber-constant masses from actual exchangeability, then exact TV and Delta_N equality. No exchangeability or quotient-TV conclusion is assumed in the actual-K exports.

`InDensityClass.full_inverse_unlabeled` assumes only original K for both densities and N>=2, concluding the original `d_conf<=100(N^(-1/12)+Delta_N)` with Delta_N defined from unlabeled directed-order laws. `InDensityClass.all_unlabeled_law_identifiability` assumes only original K and equality of all such observed laws, concluding pointwise density equality on the square under one global identity or transpose. Neither event labels, total coordinate orders, latent positions nor time-reversed dual identification are observable inputs. All F0-F6 original coefficient obligations are now proved. Proper-time and the optimized logarithmic-grid Lean estimate remain separately selectable; their prose status is retained.

The archived software 0.1.0 and manuscript 0.2.0 remain immutable historical packages; current main-branch formal results postdate them. Originality is still provisional. Open-source informal feedback/use/testing remains the review workflow, without a specialist-review or adoption gate.

Remaining to-do list: final delivery and scope completion audit.

## Final delivery closeout ? 2026-10-07

The full original-observable proof and requirement audit are committed and pushed at `b7d762acc9c10ca881f8366f545f3998b0528448`. [Supplementary hosted checks](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37622943270) passed both jobs, including the root/type/axiom audit, all existing finite/grid sanity checks and manuscript compilation. Exact proof/check/build-configuration bytes match the authoritative GCP capture, with sixty-eight export reports and no compiler warnings. Fresh public manuscript PDF/source identities and software DOI/version were verified; S014's high-precision check passed. The task-started GCP instance is TERMINATED. Final planning closeout records S012-S014 completion and supersedes development-stage delivery to-do lists.

Remaining to-do list: none for S012-S014.

## S022 logarithmic inverse acceptance

The [S022 acceptance record](logarithmic-certification.md) supersedes earlier prose-only descriptions of the logarithmic bound for current software. Exact-source GCP run `space-loggrid-acceptance-20261008T000726Z-1e4d11` passed the 2909-job root build and 78 exact-type/axiom audits with no warnings or added axioms. Original proofs and published artifacts remain preserved.

Remaining to-do list: deliver S022 and complete S023-S025.

## S023 actual proper-time acceptance

[Proper-time certification](proper-time-certification.md) records exact-source GCP run `space-propertime-acceptance-20261008T003208Z-4a6684`: 2910 root-build jobs, 90 exact-type/axiom audits, exit zero, no warnings or added axioms. Actual AC curves, FTC derivative integrals, Cauchy-Schwarz, length/supremum comparison and global transpose transport are proved.

Remaining to-do list: deliver S023; complete S024-S025.

## S024 partial deterministic and analytic acceptance

S022 and S023 delivery is complete. [Finite-data foundations](finite-foundation-certification.md) record the 107-export acceptance of forcing/rank, position, rational dual, rounding and conditional CDF proofs. [Sharp-DKW analytic certification](dkw-analytic-certification.md) adds the universal likelihood barrier, proved stationary parameter, Bernoulli Pinsker and actual derivative/shape arguments. Exact-source run `space-dkw-analytic-acceptance-20261008T022033Z-1e119b` passed the 2924-job root build and 115 exact-type/axiom audits with zero warnings or added axioms. Statistical DKW coverage and the cell/point/histogram/report suite remain open; S024 is not complete.

Remaining to-do list: sharp probability coverage, actual density/report guarantees and full S024 delivery; S025.

## S024 sharp finite-grid counting-law acceptance

[Finite-grid certification](dkw-finite-certification.md) records exact-source GCP run `space-dkw-finite-acceptance-20261008T025036Z-645562`: 2928 root-build jobs and 125 exact-type/axiom reports, exit zero with no warnings or added axioms. Cartesian revealed-atom identities, terminal mean, a direct first-crossing Ville bound, the sharp one-sided likelihood/CDF consequence, exact bin reflection and the two-sided all-nonnegative-tolerance counting-law bound are proved. The theorem's left side is cardinal divided by q^n. Uniform continuous quantization/law and the dense-grid/actual-K transport remain unproved, so this does not complete S024.

Remaining to-do list: continuous uniform and actual-K DKW/coverage transport; density/report suite; full S024 acceptance and delivery; S025.

## S024 complete density-report acceptance

[Integrated density-report certification](density-report-certification.md) records `space-density-report-acceptance-20261008T054425Z-0ff64c`: 2955 root jobs, 219 exact-type/axiom audits, zero warnings or added axioms. The canonical runtime LP is connected to actual original-K cell means and instantiated rational dual checks. Reported cell/point bands, histogram residual/error and conservative fallback are checked under one orientation. Actual full-report probability uses only original K, n>0 and an accepted fixed calibration-or-fallback check; no accuracy or primal-feasibility premise remains in the main theorem. Matching Lean/Python representation and adversarial fixtures are retained. This closes the earlier mathematical integration obligations and preserves the practical full-range limitation. Focused source/evidence commit `488338a80a293848874661aeb0e6c161b28893a7` is pushed; all three supplementary CI workflows passed and the task-started VM is verified TERMINATED. All S024 requirements are fulfilled.

Remaining to-do list: S025.

## S025 genuine Lorentzian gauge certification ? 2026-10-07

[Full counterexample certification](higher-dimensional-certification.md) records `space-lorentz-acceptance-20261008T071627Z-221cd8`: 3001 root jobs and 295 exact-type/axiom audits, adding 76 selected exports with zero warnings or added axioms. It proves the actual 2+1 Euclidean diamond volume, genuine future chronology, smooth Cartesian automorphism and inverse, actual derivative/Jacobian, transported density-class membership, actual iid coupling and every labeled/unlabeled finite directed-order law equality. Positive coordinate distance modulo all spatial O(2) accompanies the derived geometric isometry. The zero-hypothesis main theorem assumes neither density normalization nor measure transport/law equality. Every development and acceptance Lean invocation ran on GCP; 18 captures preserve 16 failed attempts, one clean targeted development build and final acceptance. Published 0.3.1 artifacts remain frozen; higher-dimensional inverse rates and new physical nonidentifiability are not claimed.

Remaining to-do list: none for the four-story certification plan.

S025 focused source/evidence commit `74c1f743d085c63b45ac2bf30008ad5d29b98fbc` is pushed; all three supplementary workflows passed and the task-owned VM is verified TERMINATED. The documentation/evidence closeout preserves every accepted proof/check/config identity. All four selected certification stories are complete.

Remaining to-do list: none for the selected certification plan.

## S032 first component acceptance ? 2026-10-08

[Fourth-root certification](fourth-root-certification.md) records `space-degree-components-acceptance-20261009T042345Z-eee254`: 3008 root jobs and 328 exact-type/axiom audits, with 33 new exports and zero warnings or added axioms. Original-K degree filtering and deep-point retention supply one-orientation shifted-cell counts. Actual iid fixed-mass concentration and a union argument give a 19/20 sample event under explicit grid/rectangle parameters. Shell mass, cell-average bias and clipping give the conditional cell-point error. Eight immutable GCP attempts retain six failures, one development success and final component acceptance. This is a partial milestone: no full fourth-root upper/lower/law endpoint is yet certified.

Remaining to-do list: actual shifted grid/histogram and parameter/floor/clamping/fallback bounds; measurable unlabeled selector and full upper guarantee; same-class lower bound; actual-law corollary; final S032 acceptance; S033 manuscript reassessment.
