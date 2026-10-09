# S033 decision: a separate finite-data theory paper

2026-10-08. **Proceed to a separately scoped theory manuscript.** The mathematical package is substantive enough for a focused paper about finite reconstruction from a single unlabeled directed order. Its central contribution is the degree-filter/deep-cell reduction and the resulting explicit, uniform confidence theorem. This is a bounded research judgment, not a certification of priority or a claim of useful numerical calibration.

S032 is delivered at [`6752732882862bc848c7a96722a7660456d6da38`](https://github.com/Quantyra/quantyra-null-cone-lean/tree/6752732882862bc848c7a96722a7660456d6da38). The [final campaign](fourth-root-certification.md) records joint GCP acceptance of all three selected endpoints: 3027 root jobs, 446 exact theorem/axiom audits, 135 captured proof/check/config identities, zero warnings or added axioms, and verified task-owned VM shutdown. The full lower result is accepted; the decision does not rely on conditional helper lemmas as a substitute.

## Proposed claims and exact proof map

| Paper claim | Accepted source and required qualifications |
| --- | --- |
| One measurable estimator of a single unlabeled n-point directed order has uniform 95% full-square error at most `min(1/2,650(log n/n)^(1/4))`, for every n>=2 and original-K density, modulo one global axis exchange. | `fourth_root_order_only_estimator` and `InDensityClass.fourth_root_density_estimation`. The estimator is independent of the unknown density. K retains its range, uniform marginals, smooth-neighborhood and Euclidean Lipschitz assumptions. Finite classical selection proves existence; efficient implementation is not asserted. |
| The actual single-n order laws obey `d_conf <= min(1,1300(log n/n)^(1/4)+(10/9)TV)`. | `InDensityClass.fourth_root_actual_law_inverse`. This compares laws; it does not claim to estimate TV from one observed order. |
| A full-original-K lower benchmark applies to every estimator, including arbitrary independent randomization. For n>=16, strict error exceeds `n^(-1/4)/6` with probability >1/4 under some admissible density. | `fourth_root_randomized_lower_bound`, `fourth_root_lower_exists`, `fourth_root_minimax_obstruction`. Include the exact all-n finite expression and explicit measurability of success events. The likelihood/product divergence and data processing concern the actual iid and order laws. |

The upper and lower polynomial exponents agree. The two-point lower proof does not settle the logarithmic minimax gap, establish an additional cost of observing only order, or introduce a new general density-estimation exponent. The ordinary random-width band consequence must retain the sum of coverage-failure probability and excessive-width probability; no conditional-on-acceptance guarantee follows.

## Literature and significance

The [bounded refreshed comparison](finite-data-manuscript-literature-refresh.md) credits earlier coordinate forcing, stronger flat-model rank recovery, rank-based copula estimation, supremum rates and qualitative spacetime reconstruction. It adds the published 2024 Seck–Mamane theorem, whose conditions and rank-based rate differ from the 2023 preprint previously inspected. One later conditional-copula-parameter article remains a search-level screen because its full text returned 403; it supports no proof-level exclusion. Broader priority remains provisional.

The defensible difference is the observation model and the complete finite reduction: no coordinate ranks are supplied, retained points obey one common geometric alignment, deep-cell counts incur no global discarded-mass penalty, and the boundary extension covers the closed square. Formal verification supplies an inspectable end-to-end guarantee. It does not by itself establish originality. The inspected precedents do not supply this complete observation/class/confidence statement directly.

This warrants a theory paper even though the frozen practical study was uninformative. All thirty pilot reports validate and retain full-width bands; twenty exact LP witness pairs explain the retained corner limitation. The eighty conditional confirmation samples were not generated. The proposed theoretical estimator changes the boundary argument and was not run as a third pilot method. Conservative upper constants do not justify useful error bands at the pilot sample size.

## Concrete manuscript scope

Working title: **Finite-sample density reconstruction from a single causal order**.

1. State the restricted 1+1 model, observation, original K, one global transpose and the three exact theorems before motivating applications.
2. Credit the earlier realizer/rank theorem as a dependency; prove the observable degree filter, retained/deep-cell inclusions and boundary handling in full.
3. Present fixed-latent-rectangle concentration, simultaneous error, measurable selection and every small-sample branch. Use the accepted concentration constants, which preserve the final radius but are weaker than one intermediate Bernstein estimate in the ordinary derivation.
4. Give the complete original-K Gaussian alternatives, separation, actual product-law divergence, order-law data processing and randomized testing proof. Label the lower method as a standard transferred information obstruction.
5. Derive the law-distance corollary; provide a Lean statement/source/evidence appendix. Include the negative pilot as a concise calibration limitation, with links to its frozen reproducible evidence.
6. Close with the unresolved logarithmic gap, conservative constants, efficient computation and practical calibration. Higher-dimensional reconstruction remains parked and is outside this paper.

The reconstruction manuscript (published 0.4.0) concerns inverse-law reconstruction, identifiability and proper time. The separate 2+1 manuscript (published 0.1.0) concerns a coordinate-gauge counterexample and its isometry. This proposed paper instead centers finite single-observation statistical guarantees; it should cite both where relevant and avoid reproducing either as its main contribution. Existing published artifacts remain immutable. A future manuscript may share this proof repository and receive its own manuscript record when publication is selected.

This decision and scope complete S033. They create neither a manuscript PDF nor a DOI. Drafting, PDF review and publication are subsequent work, with open-source decentralized informal feedback and no specialist-review or adoption gate.

Remaining to-do list: none for S033. Proposed next work: prepare the separately scoped manuscript.
