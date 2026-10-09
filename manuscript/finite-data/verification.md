# S034 manuscript review

8 October 2026. The selected preparation scope produces a complete separate theory manuscript, version 0.1.0, with no publication or DOI action. [PDF](finite-sample-order-density.pdf), [formal map](formal-map.json), [identity checks](source-verification.json), [page receipt](review.json).

## Mathematical correspondence

Theorem 1.1 quantifies one estimator before the unknown original-K density. Its input is the actual directed-order isomorphism class; the original Euclidean Lipschitz condition, uniform marginals and full closed-square loss are explicit. One global transpose is allowed. The arbitrary output is not asserted to be a normalized density. The two endpoint exports and the concrete selector were read together with their all-n branch and quotient transport proofs.

Sections 2–4 include the earlier occupied-grid forcing proof with attribution, strict predecessor self-subtraction, successor inclusion-exclusion, both degree inclusions, cell erosion/dilation and the complete bias/extension calculation. The fixed rectangle family includes both orientations before sampling; the sample-dependent orientation is not treated as a fixed random set. Count cells use Ioc endpoints and queries use clamped floor/min indices, with error on closures.

The concentration is the accepted Bernoulli MGF/Chernoff route: tolerance 4h^3, mass at most 8h^2, individual bound 2 exp(-n h^4/2), conservative family failure 8/n^3. The sharper Bernstein intermediate bound from the historical ordinary note is not claimed as certified. The auxiliary prose failure budget is below 1/20 for n>=8; the actual active branch satisfies the stronger size hypotheses in the formal composition. No remaining helper premise is carried into Theorem 1.1.

Corollary 1.2 uses the same estimator and actual single-n laws. Success sets intersect when TV<9/10; the large-TV branch uses the class diameter. It estimates neither TV nor a probability law from one order.

Section 5 verifies exact marginal cancellation, original-K Euclidean Lipschitz membership, quotient separation h/e, Gaussian integral pi/32 after squaring, actual product likelihood, chi-square identity and finite observation data processing. Theorem 1.3 retains the independent arbitrary seed, explicit measurable-success-event assumptions, closed success/strict failure distinction, all-n finite risk and n>=16 specialization. Outputs need not lie in K. The random-width band inequality is a written midpoint/union consequence with its own measurability qualification; no conditional-on-acceptance coverage claim or separate Lean band export is made.

The statement map links 39 individually audited exports. Reading theorem names or matching source hashes alone is not a semantic proof audit. This preparation review inspected the endpoint types, definitions and critical reduction/scale/product statements against the prose. The complete accepted GCP root build supplies formal proof checking. No Lean source, root import or integrity checker was changed, and no Lean/Lake command ran during preparation.

## Literature and practical claims

The manuscript reuses the completed [S033 primary-source refresh](../../notes/finite-data-manuscript-literature-refresh.md), its [retrieval receipt](../../evidence/finite-data/s033-literature-refresh.json), and the [S031 comparison](../../notes/finite-data-feasibility-comparison.md). It does not claim a new full-text search during S034. Bibliographic metadata for the two 2024 published copula papers was checked against their locally retained publisher PDFs.

The published Seck–Mamane Theorem 1, smoothness condition and displayed rate are used, with the Remark 3 distinction from the oracle rate. The 2023 preprint's different rate/remainder is not substituted. The two Winkler papers retain the exact earlier inspected locations and flat-model limitation. Rank/copula estimation, Gaussian testing and qualitative reconstruction are credited. The inaccessible 2026 conditional-parameter article is not a theorem-level exclusion or a source for this paper. Third-party full texts stay outside Git.

All pilot counts and practical limits were reconciled with the frozen [results](../../notes/finite-data-feasibility-results.md): ten orders, thirty reports, twenty LP witness pairs, forty resource-bounded runs and eighty ungenerated conditional samples. The new degree estimator is not an additional piloted method. The logarithmic gap, classical-choice efficiency limit, conservative constants and absence of an order-specific lower penalty remain explicit.

## PDF and custody

The final PDF has 12 pages. Every page was visually inspected in the final rendered contact sheets, checking formulas, page breaks, bounds, bibliography and font rendering. No unresolved references, missing characters, overfull/underfull boxes or LaTeX warnings remain. The raw Tectonic output retains a nonfatal Fontconfig configuration notice; the rendered Latin Modern text and mathematics were checked.

The source verifier checks all 135 accepted source identities against the current files and cited proof commit. Historical utilities using CRLF in this Windows checkout have their raw hashes and exact LF comparison disclosed in the receipt. The 446 accepted audit reports use only propext, Classical.choice and Quot.sound. The preservation comparison protects 5,415 baseline tracked files, including the two published families, all raw evidence, old drafts, formal sources, metadata and frozen study. Only navigation/EOL metadata and this new directory are allowed to differ.

Remaining to-do list: none for S034 preparation; a separate manuscript publication/DOI action is subsequent scope.
