# S033 bounded primary-source refresh

2026-10-08 (Hawaii). This refresh supplements the [S031 comparison](finite-data-feasibility-comparison.md) and [purchased Winkler audit](winkler-full-text-comparison.md). It is an applicability comparison, not an exhaustive priority claim. Retrieval identities and access limits are recorded in [the receipt](../evidence/finite-data/s033-literature-refresh.json); third-party full texts remain outside Git.

## Published-version correction

The [published Seck–Mamane paper](https://doi.org/10.37920/sasj.2024.58.1.3), **Theorem 1, printed p. 40 (PDF 6)**, differs materially from the [2023 preprint](https://arxiv.org/html/2303.05627v1). It requires `(d+2)/2 < t < N+1` and gives an almost-sure supremum rate `R_n = sqrt(2^(2(1+d)j_n) log log n / n)` for the specified resolution. **Remark 3, printed p. 43**, expressly distinguishes its slower rank-based rate from the oracle's optimal rate. Inspected: assumptions and Proposition 1, printed 39; Theorem 1 and proof, 40–43; visual checks of theorem and final proof/remark pages. The Appendix's empirical-process proof is not independently re-proved here.

This supersedes use of the preprint's unquantified `o(1)` as the description of the published result. The applicable comparison remains: empirical coordinate ranks, stronger smoothness/norm conditions and asymptotic control do not directly supply a finite, uniform-original-K, order-only confidence theorem. Smoothness of each K density does not provide a common bound on higher derivatives over K. Neither the rank-based exponent nor an oracle rate should be quoted as our contribution.

## Other comparisons

| Primary source and inspected passage | Consequence for the proposed finite-data paper |
| --- | --- |
| [Swanepoel–Seck–Mamane (2024)](https://www.journals.ac.za/index.php/sasj/article/download/6437/4034/28206), Conditions 1–4 and Theorem 1/proof, printed 101–105, PDF 4–8; refreshed theorem and proof decomposition | Estimates joint and marginal densities and quantiles from coordinate data. Its supremum result is almost-sure and uses Besov, support and positive-marginal conditions. Credit uniform copula estimation and boundary work; no finite order-only confidence guarantee is imported. |
| [Braun (2025), v1](https://arxiv.org/html/2507.01907v1), global dimension convention, Theorems 1.4–1.5 and their model definitions | All-size chronology laws determine isometry, or a weighted conformal equivalence, under the stated causal/geometric conditions; dimension is at least three. This is qualitative reconstruction context. Our contribution must be a finite single-order statistical guarantee in a restricted class, not discovery of reconstruction from order and number. |
| Winkler (1985; 1991), Genest–Masiello–Tribouley (2009), Autin–Le Pennec–Tribouley (2010) | Reuse the exact inspected locations and limits from S031. Coordinate forcing, flat-model rank recovery and rank-based copula density estimation are established precedents. No new full-text reread is claimed. |
| [2026 covariate-dependent copula-parameter lower-bound paper](https://www.mdpi.com/2227-7390/14/5/914) | Search/publisher-index screen concerns parameters in a conditional copula family. Full-text retrieval returned 403. No theorem is imported or excluded on the basis of an unread proof. |

## Search scope and verdict

Queries covered partial-order/copula density estimation; causal-order finite reconstruction rates; random dimension-two orders; copula supremum, boundary and minimax rates; and 2025–2026 continuations. Unrelated causal-discovery, trading-order and imaging results were excluded by their observation models. Search freshness labels were not treated as publication dates. Four refreshed primary documents were retrieved and hashed; the receipt retains the failed publisher retrieval. This bounded screen found no inspected theorem that supplies the complete S032 observation/class/confidence/quotient statement. That is a bounded finding, not proof of absence.

The defensible candidate contribution is the **degree-filter/deep-cell reduction from a single unlabeled directed order to a uniform full-square density guarantee**, composed with the existing geometric recovery theorem. Gaussian two-point testing supplies a familiar transferred lower benchmark. The logarithmic gap remains open; no new density-estimation exponent, extra order-information cost, efficient estimator or practical calibration success is established.

The [manuscript decision](finite-data-manuscript-decision.md) applies this comparison to the exact accepted statements.

Remaining to-do list: none for the S033 literature refresh.
