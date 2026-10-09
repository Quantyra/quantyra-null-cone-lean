# Statement correspondence and review scope

This working revision retains the original density class, one unlabeled strict directed order, full closed square and one global identity/transpose. It adds a matching logarithmic lower obstruction and the fixed-confidence minimax-radius sandwich. The 0.1.0 published edition and historical preparation snapshot are preserved.

## New statements

| Prose | Formal correspondence and discharged obligations |
| --- | --- |
| Centered profiles | `logLowerProfile h c` subtracts the actual interval integral of the translated odd Gaussian. The primitive and mean formula are proved; both exact mean zero and variance reduction use actual integrals. Smoothness is global. Peak, tail and Lipschitz bounds are uniform in the center. |
| Packing in K | `logLowerFamily m j` has h=1/(16m) and centers 1/4+(j+1/2)/(2m). Original `InDensityClass` is imported unchanged. Its Euclidean distance is the square root of the sum of coordinate squares, not the default product norm. Uniform marginals are exact, and smoothness needs no uniform bound on higher derivatives. |
| Separation | `log_lower_packing_separation` gives 3h/128 at a diagonal witness in the closed square. `log_lower_success_disjoint` composes the two global alignments and uses transpose invariance. It permits arbitrary outputs and r<=h/256, including smaller radii. |
| Testing | `many_event_likelihood_sum_le` integrates F=sum indicator(Aj)Lj. Disjointness removes cross terms; squared integrability and probability-reference assumptions are explicit. `many_event_failure_exists` uses Pj probabilities, their actual restricted likelihood integrals, and B<=m/4 to obtain failure>=1/2. |
| iid and seed | `log_lower_sample_withDensity` proves the identity for the actual finite product measure. `log_lower_seed_real_apply` identifies event probabilities on sample times seed; `log_lower_seed_second_moment` shows the independent probability seed leaves the bound unchanged. These are not formal stand-ins for an assumed observation law. |
| Finite scale | `logLowerMesh n` is the natural ceiling of (n/log n)^(1/4). `log_lower_mesh_budget` proves exp(nh^4/4)<=m/4 for n>=2^64; `log_lower_target_radius` proves rate/8192<=h/256. All positivity, logarithms, ceilings and constants are discharged. |
| Logarithmic endpoint | `logarithmic_randomized_minimax_obstruction` quantifies over every estimator and independent probability seed. Its only estimator premise is measurability of the target-radius simultaneous success event for every K density. Its conclusion is some original-K density with complementary success probability >=1/2. `logarithmic_lower_bound_at_radius` handles any smaller radius with that radius's measurability. No auxiliary-radius measurability is used. |
| Minimax radius | `UniformOrderConfidenceRadius` requires one estimator before the quantifier over K, measurable success events and uniform 19/20 coverage. `orderConfidenceRadius95` is the real infimum over nonnegative achievable radii. `fourth_root_uniform_radius_achievable` lifts the actual deterministic upper theorem by ignoring the seed. Nonemptiness and boundedness of the infimum set are proved. `logarithmic_uniform_radius_necessary` excludes every radius at most rate/8192; `logarithmic_minimax_radius_bounds` proves the sandwich. |

`DensityEstimateGood` uses a Boolean global orientation followed by the universal quantifier over all points of `diamond`. `LowerEstimateSuccess` is the corresponding event in order-code times seed. Its complement is strict quotient error, including the stated extended-success convention for unbounded outputs. Lean functions are defined on all of R^2; restricting them to D, or extending an arbitrary D-output outside D, leaves every success event unchanged.

The coordinate-data lower endpoint follows by applying the same testing argument directly to coordinate success events. It is a written consequence, not a separately named coordinate-estimator Lean endpoint. Likewise the infimum over all seed spaces follows from constants uniform in every seed law; the formal theorem quantifies over each seed space. This distinction is explicit in the manuscript and `formal-map.json`.

## Retained statements and attribution

The old upper estimator, actual-law corollary, two-point lower obstruction, band consequence and their full proofs remain in the revision. Their 39 mapped exports are retained byte-for-byte at the proof-source level. The new map adds all 62 audited S036 exports, giving 101 unique mapped exports. Library-wide acceptance contains 508 reports; it is not a claim of 508 results in this manuscript.

The ordinary note records an equivalent per-event Cauchy-Schwarz proof; the manuscript and Lean both use the summed-indicator proof. Guntuboyina's Section I, Theorem II.1 and Example II.8 equation (15), l=2, are credited as established testing methods. The primary full-text receipt is `evidence/finite-data/s036-literature.json`. Earlier Winkler, rank/copula and geometric comparisons retain their S033 provenance; this revision does not claim a fresh exhaustive search or new general testing inequality.

The independent seed is the same law under every density. No assumption of observed ranks, independent overlapping suborders, stronger regularity or a new dimensional model is added. Same-rate coordinate and order conclusions concern this loss and fixed confidence, not experiment equivalence or equal optimal constants. Constants are conservative; no practical success, expected risk or efficient estimator is claimed. The frozen pilot is unchanged.

## Reproduction and custody

`verify_sources.py` reads source and retained GCP logs only. It checks every captured source at the working tree and cited proof commit, all 508 allowed-axiom reports, exact type reports for 101 mapped exports, and preservation of every earlier tracked file except the explicitly allowed navigation/EOL/root/audit integration files. Raw cloud logs are retained unchanged, including failed attempts. All eight local-authoring/GCP-compilation snapshots are indexed in `evidence/gcp/s036-logarithmic-final.json`.

`build.py` invokes Tectonic and PyMuPDF only, checks layout/glyph/reference diagnostics and emits page renders. Visual review is separately recorded in `review.json`; generating images does not assert that they have been inspected. This is AI-assisted mathematical and visual review under the repository's decentralized informal workflow, not independent specialist refereeing.

Remaining to-do list: none for statement correspondence; final artifact review and delivery are recorded in `review.json` and the S036 planning audit.
