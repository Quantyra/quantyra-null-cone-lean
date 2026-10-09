# Fourth-root finite-data certification campaign

S032, selected 2026-10-08 under the goal "complete steps 1-3". Baseline `436e36a05b4234870200871bd1adc8c082163c7f`. **All three selected endpoints now pass together on GCP: full upper guarantee, actual-law corollary and full randomized lower bound.** Final acceptance is recorded below; historical component milestones retain their original scope. The complete ordinary arguments remain in [the upper proof](finite-data-interior-degree-rate.md) and [the lower proof](finite-data-information-limit.md), with their [audit](finite-data-feasibility-proof-audit.md). S031's completed pilot and its negative practical disposition are preserved.

## Frozen mathematical endpoints

1. For each n>=2, construct one measurable estimator on actual directed-order isomorphism classes, independent of the unknown density. For every original-K density, with probability at least 19/20 its full closed-square sup-norm error, under one global identity/transpose, is at most `min(1/2,650(log n/n)^(1/4))`. The output may be a clipped, boundary-extended histogram and need not itself belong to K.
2. Derive for the actual unlabeled n-point laws `d_conf <= min(1,1300(log n/n)^(1/4)+(10/9)TV)`. No observed ranks, latent coordinates or time-reversal quotient enter these endpoints.
3. Certify the explicit odd-Gaussian alternatives in the full original K, quotient separation, product chi-square and data-processing/testing argument. For n>=16, every measurable estimator, including randomized estimators, has error greater than n^(-1/4)/6 with probability greater than 1/4 under some admissible density. Preserve the exact finite inequality for h=min(1/2,n^(-1/4)) and the random-width confidence-band distinction in the ordinary proof.

The polynomial exponents match but the logarithmic minimax gap remains open. The lower obstruction also holds with full coordinate observations. Conservative upper constants do not establish practical usefulness at n=3072. These limitations are part of the selected result, not deferred proof obligations that can silently strengthen its claim.

## Proof work order and dependency contract

| Stage | Required advancement toward the endpoints |
| --- | --- |
| Degree filter | Define strict predecessor/successor counts from the observed relation. Prove the inclusive joint-CDF minus self-count identity and the successor inclusion-exclusion identity. On the accepted grid event derive `deep square subset retained subset interior`, with the exact thresholds 6rn, 4r and 7sqrt(r). |
| Recovered cell counts | Compose the filter with the existing one-orientation rank theorem. Prove erosion/dilation inclusions without a discarded-mass term, including all boundary conventions and transpose transport. |
| Concentration | Derive mass-sensitive finite concentration for the deterministic shifted rectangles under the actual iid sample measure, mass bound 8r and tolerance 4r^(3/2), then the simultaneous union budget. Do not assume a concentration event or iid recovered points in the main theorem. The simpler Chernoff route below replaces the sharper intermediate Bernstein estimate while preserving the selected endpoints. |
| Density and scale | Prove the cell-average, clipping, clamping and full-square error, exact constants, floor estimates, and every flat-output branch. Assemble the probability event and finite order-only measurable selector. |
| Lower bound and law consequence | Prove original-K membership and divergence/testing for the explicit alternatives; derive the law-distance consequence from the same upper estimator and actual laws. |
| Acceptance | Root build, exact theorem/type and axiom map, source/dependency checks before and after, retained failures/logs, focused delivery and task-owned VM cleanup. |

Accepted dependencies include `Cumulative.finite_realizer_coordinate_rigidity`, the marginal and joint-grid results in `GridAccuracy`, and the actual occupancy/concentration measures in `GoodSamples`/`LogGridRate`. Source names live in namespace `QuantyraNullCone`. `rank` is already **inclusive** (`1 + predecessor count`); no additional offset may be inserted when using `normalized_coordinate_rank_eq_marginalCDF`. The strict joint predecessor count instead subtracts the sample point once. All new helper preconditions must ultimately be discharged from original K and n>=2; proving helpers alone does not certify any endpoint above.

## Critical-route progress and concentration derivation

The first three new modules cover the deterministic bottleneck rather than assuming it: `DegreeFilter` proves the strict count identities and retained-point accuracy; `DegreeMass` derives the actual lower rectangle masses and retention of every deep point from original K; `DegreeCells` combines them into simultaneous eroded/recovered/expanded count bounds with one global orientation. GCP development run `space-degree-cells-20261009T040421Z-26c605` passed all three modules (2901 jobs), with standard axiom reports and no warnings. The two earlier failed attempts and their exact inputs are retained. This is development evidence for those lemmas, not acceptance of a full fourth-root theorem.

The route still covers the original upper endpoint: the count sandwich removes the global discarded-mass term. The remaining probabilistic input must be derived for fixed latent rectangles; recovered points are not assumed independent. The selected formal concentration route uses the following complete elementary argument:

1. For a Bernoulli indicator of mass p, the centered MGF is `exp(-tp) (1+p(exp(t)-1))`. Since `1+x <= exp(x)` and `exp(t)-1-t <= t²` for `|t|<=1`, it is at most `exp(p t²)`.
2. Actual iid independence gives the product MGF. Chernoff at `t=h/4` on each tail, with `p<=8h²` and tolerance `4h³`, yields `2 exp(-nh⁴/2)`. Here `h²=r`; the selected grid implies `nr²>=8 log n`, so each bound is at most `2/n⁴`.
3. There are at most `2k²` shifted rectangles; transposing permutes the square grid. The union failure is at most `4k²/n⁴ <= 4/n³` when `k²<=n`. Even counting both orientations separately gives at most `8/n³`. Combined with the existing geometric-event bound `1/(8n³)+1/n^15`, this is below `1/20` for n>=8; the active branch has a much larger cutoff. Flat-output branches are deterministic.

This formal route has a weaker intermediate tail estimate than the ordinary proof's `4/n^5`, but leaves the histogram tolerance and intended deterministic `270h` estimate, constant 650 and final 19/20 coverage unchanged. It does not certify the sharper intermediate Bernstein bound. The combined 19/20 sample event is now certified with explicit grid/rectangle parameters. Their discharge for the actual histogram and the full estimator remain proof obligations.

## First component acceptance

GCP run **`space-degree-components-acceptance-20261009T042345Z-eee254`** passes the full root build (3008 jobs) and all **328 exact-type/axiom audits, including 33 new exports**. The [receipt](../evidence/gcp/space-degree-components-acceptance-20261009T042345Z-eee254/receipt.json), [source/dependency capture](../evidence/gcp/space-degree-components-acceptance-20261009T042345Z-eee254/capture-manifest.json), [full audit](../evidence/gcp/space-degree-components-acceptance-20261009T042345Z-eee254/logs/audit.stdout.txt) and [campaign index](../evidence/gcp/fourth-root-components-20261008.json) identify the accepted bytes and every attempt. There are no warnings or added axioms; dependencies are only `propext`, `Classical.choice` and `Quot.sound`. Source and pinned dependencies are checked before/after execution, and the retained capture matches the delivered proof/check files after LF normalization. Six failed attempts and the earlier successful development build are retained alongside acceptance, with inputs, terminal state and complete raw diagnostics.

| Module / principal export | Exact contribution and remaining premises |
| --- | --- |
| `DegreeFilter.degree_retained_coordinate_rigidity` | Original K and `SampleGood`, positive n/r, m>=16 and mr=1 imply one alignment with coordinate error 32r for every observed-degree-retained point. Strict predecessor self-subtraction and successor inclusion-exclusion are proved. |
| `DegreeMass.deep_point_degree_retained` | Original K and the same sample event imply every point in `[7h,1-7h]^2` is retained, with h>=0, h²=r and 1/n<=r explicit. Rectangle lower/upper masses are derived from K. |
| `DegreeCells.degree_filtered_cell_counts` | Under those conditions, one alignment works for every cell whose eroded rectangle lies in the deep square. Counts are bounded by true eroded/expanded counts without a global discarded-count term. |
| `BernoulliMGF.centered_indicator_mgf_le` | Exact Bernoulli MGF and local quadratic upper bound for any probability measure and measurable set, with `abs(t)<=1`. |
| `SmallMassConcentration.InDensityClass.small_mass_family_failure` | Actual iid sample measure and any fixed finite measurable family of mass <=8h² give union failure <=`2 card(family) exp(-nh⁴/2)`. Recovered points are never assumed iid. |
| `DegreeProbability.InDensityClass.degree_event_probability` | For n>=65536, m>=16, the logarithmic mesh inequality, mr=1, h²=r, 0<=h<=4, family size <=4n and those actual mass bounds, the intersection of `SampleGood` and all count tolerances has probability >=19/20. |
| `DegreeCellBias.InDensityClass.shifted_cell_point_error` | The count sandwich and two count deviations give clipped pointwise error <=`6s/w + 6(s/w)^2 + eps/w^2 + 2w` at every closed-cell point. Shell masses come from density bounds and area; the stated cell/shift/domain conditions remain explicit. |

Names in the table are file-qualified for navigation; all declarations live in namespace `QuantyraNullCone`, with `InDensityClass` where shown in the source/audit. The public root and integrity checker include every new export. The exact accepted statements, rather than this abbreviated table, define the milestone.

The second route assessment finds the concentration and cell-error steps sufficient for the selected upper proof: neither uses independence of recovered points, observed latent coordinates or a strengthened K. The remaining work is concrete composition and parameter discharge, then the separately selected lower construction/testing argument and actual-law consequence. The full endpoints are still absent. This component acceptance is not S032 completion and does not authorize a manuscript claim that those endpoints are Lean certified.

Supplementary delivery checks verify UTF-8/no unfinished proof tokens, Python checker syntax, current local links and checkpoint JSON. All 391 baseline proof-module, manuscript and frozen-study files are preserved; only the root import/audit surface and new proof modules extend the formal library. No numerical experiment or published artifact is changed. The task-owned instance is stopped after terminal evidence collection and a no-other-work preflight; the campaign index records its final state.

## Histogram assembly underway

The next stage uses the accepted component revision `e728230b12d19dbb95100f15d4dca9d76df00509`. The whole-square estimator clamps both query coordinates into `[H,1-H]` and selects index `min(floor((x-H)/w),k-1)` in each coordinate. This fixes internal query edges to the cell on their right and the upper edge to the last cell. Counts remain on Ioc cells. This harmless convention differs from the prose's query tie convention; the same error holds on every closed cell, so all points and the exact endpoint constants are preserved. The coordinatewise common index convention also commutes with transpose.

`InnerHistogram` proves index coverage, measurable output and a `3H` Euclidean-Lipschitz clamping penalty. `DegreeHistogram` defines the actual observed-degree/rank histogram, proves clipping bounds and transpose transport, and composes the accepted count and cell-error lemmas. The next parameter discharge uses `m>=65536`, `h=sqrt(1/m)`, `k=floor(sqrt(m))`, `H=8h` and `w=(1-16h)/k`: `h<=1/256`, `15h/16<=w<=2h`, `2s<=w`, `H-s>=7h`, fixed shifted mass <=8h² and the displayed cell error plus `24h` <=270h. This is the existing complete ordinary argument being translated, not an extra recovery hypothesis. These new files remain development work until their own exact-source acceptance.

Every Lean/Lake invocation runs on project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. The instance was observed TERMINATED at selection. Each attempt uses a unique captured source directory, pinned Lean 4.30.0/mathlib/dependencies, one compiler and retained terminal diagnostics. No workstation Lean compilation is permitted. Historical captures and published manuscripts remain intact.

## Full upper and actual-law acceptance

GCP run **`space-degree-upper-acceptance-20261009T050655Z-35cee0`** passes the complete root build (**3016 jobs**) and **379 exact-type/axiom audits, including 51 new exports**. The [receipt](../evidence/gcp/space-degree-upper-acceptance-20261009T050655Z-35cee0/receipt.json), [full audit](../evidence/gcp/space-degree-upper-acceptance-20261009T050655Z-35cee0/logs/audit.stdout.txt) and [campaign index](../evidence/gcp/fourth-root-upper-20261008.json) retain the exact accepted source/dependency identities and all seven attempts, including six compiler failures. All 126 captured source/check/config files are verified before and after execution; pinned dependency revisions and clean source states are also verified before and after. There are no warnings or added axioms; only `propext`, `Classical.choice` and `Quot.sound` occur. These new files supersede the development-only status in the histogram assembly record above.

| Export | Accepted endpoint or role |
| --- | --- |
| `fourth_root_order_only_estimator` | For every n>=2, there exists one measurable estimator on actual directed-order isomorphism classes, independent of rho. Every output is measurable and lies in [1/2,3/2]. For every original-K rho, its full closed-square error under one global identity/transpose is at most `min(1/2,650(log n/n)^(1/4))` with probability at least 19/20. |
| `InDensityClass.fourth_root_density_estimation` | The preceding probability bound for the explicitly defined `selectedDegreeDensity`, under the actual `unlabeledOrderLaw`. It assumes neither a good sample event nor observed coordinate orders. |
| `InDensityClass.fourth_root_actual_law_inverse` | For two original-K densities and n>=2, `d_conf <= min(1,1300(log n/n)^(1/4)+(10/9)TV)`, using their actual single-n unlabeled-order laws. No law-estimation hypothesis is introduced. |
| `DegreeHistogramProbability` / `DegreeRateNumbers` | Discharge the actual shifted-rectangle probability budget, integer floors, explicit logarithmic mesh and all flat-output cases. |
| `DegreeRelabel` / `DegreeEstimator` | Prove degree/rank-count invariance under vertex relabeling, transport reconstruction to a canonical quotient representative, and use almost-sure coordinate injectivity to obtain a realizer on actual samples. |
| `InnerHistogram` / `DegreeHistogram` / `DegreeMesh` | Prove query coverage, full-square clamping, output measurability and bounds, transpose transport, mesh margins and the complete `270h` deterministic estimate. |

The exact statements in the audit define the accepted scope. The selector uses finite classical choices; this theorem does not assert an efficient implementation. The practical pilot remains uninformative, the constants are conservative, and the logarithmic minimax gap remains open. The lower construction/testing proof is still ordinary mathematics only, so full S032 completion and S033's manuscript decision remain outstanding. Neither published manuscript is changed.

Delivery checks compare all captured proof/check/config bytes with staged Git objects and preserve every raw attempt file byte-for-byte. Existing proof modules, manuscript artifacts and frozen study data are unchanged; the public root/check surface extends the library with eight new modules. The task-owned instance is verified TERMINATED after full terminal evidence collection and a process preflight showing no other work. Local Lean/Lake invocations remain zero.

## Lower-bound proof order at the upper milestone (now discharged)

The selected lower endpoint retains the exact alternatives and finite inequality in [the ordinary lower proof](finite-data-information-limit.md). It is not replaced by a conditional testing lemma or a stronger density class.

1. Prove the odd-Gaussian profile `f(t)=t exp(-t^2)` is smooth, bounded by 1/2 in absolute value, and has derivative bounded by one. Scaling and an exact zero integral on the symmetric interval give the two uniform marginals. Derive the Euclidean Lipschitz condition and the original-K bounds for `rho_1=1+2h a_h(u)a_h(v)`, for `0<h<=1/2`; `rho_0=1` is the other admissible density.
2. Prove transpose invariance and the explicit in-square separation witness at coordinates `1/2+h/sqrt(2)`. Establish quotient distance `h/e>h/3`, including `e<3`, so the two closed success sets at radius `h/6` are disjoint. This must hold for arbitrary estimator outputs, not only outputs in K.
3. Derive the Gaussian second moment, the exact single-point squared-likelihood integral and its upper bound `pi*h^4/8`. Multiply likelihood ratios under the actual iid product measure. Prove the event/total-variation bound for its pushforward to actual unlabeled orders, retaining the explicit finite expression `sqrt(exp(n*pi*h^4/8)-1)/2`.
4. Prove the strict-error testing reduction, including arbitrary measurable independent random seeds. A direct route integrates finite-observation event sections over the seed measure; it must establish that adjoining the seed cannot increase the relevant event discrepancy. Discharge `h=min(1/2,n^(-1/4))`, `n*h^4<=1`, the strict 1/4 probability bound and the `n>=16` specialization. Preserve the separate consequence for random-width bands.

Every step needs exact-source GCP acceptance, with root type/axiom exports and retained diagnostics. After the full upper/lower/law requirements are met, S033 refreshes the bounded primary-source comparison and records a concrete third-manuscript decision. Neither a new manuscript nor publication is automatic.

The preceding work order is discharged by the final acceptance below.

## Full S032 acceptance, 2026-10-08

Run **`space-degree-final-acceptance-20261009T055238Z-7ba92d`** passes **3027 root-build jobs and 446 exact-type/axiom audits**, including **67 new lower-bound exports** (151 S032 additions in total). The [receipt](../evidence/gcp/space-degree-final-acceptance-20261009T055238Z-7ba92d/receipt.json), [exact statements and dependencies](../evidence/gcp/space-degree-final-acceptance-20261009T055238Z-7ba92d/logs/audit.stdout.txt), [source capture](../evidence/gcp/space-degree-final-acceptance-20261009T055238Z-7ba92d/capture-manifest.json) and [final campaign index](../evidence/gcp/fourth-root-final-20261008.json) are authoritative. All 135 source/check/config identities and pinned dependencies pass before/after checks. There are zero warnings and no dependencies beyond `propext`, `Classical.choice` and `Quot.sound`. Twelve lower-campaign attempts retain their immutable inputs and full terminal logs, including eleven failures. Initial SSH boot trouble is also retained. All Lean execution was remote GCP.

| Module / principal theorem | Accepted statement and scope |
| --- | --- |
| `OddGaussian`, `LowerAlternatives.lower_alternative_in_class` | Globally smooth odd-Gaussian profiles; exact zero marginal perturbations; original range and Euclidean Lipschitz 2. Both alternatives belong to the original K for `0<h<=1/2`. |
| `LowerSeparation.lower_quotient_separation`, `lower_success_disjoint` | Exact quotient separation `h/exp(1)`, attained at an in-square witness. The closed radius-h/6 success sets are disjoint for arbitrary function outputs under one global identity/transpose. |
| `LowerMoments.lower_single_point_divergence_bound` | Integration by parts proves the whole-line second moment; truncation and product integration give the single-point squared-likelihood bound `pi*h^4/8`. |
| `LowerProduct.lower_sample_withDensity`, `lower_product_divergence_identity` | The actual iid alternative sample measure has likelihood equal to the product of the one-point densities against the uniform sample law. Exact product identity and exponential upper bound are proved. |
| `LowerDataProcessing.lower_order_TV_bound` | Finite measurable observation contracts L1. Applied to the actual map from samples to directed-order isomorphism classes, TV is at most `sqrt(exp(n*pi*h^4/8)-1)/2`. |
| `LowerTesting`, `LowerScale` | Arbitrary independent seed probability spaces preserve the finite-event discrepancy bound. With `h=min(1/2,n^(-1/4))`, `n*h^4<=1` and the resulting finite risk lower bound is strictly greater than 1/4. |
| `LowerBound.fourth_root_randomized_lower_bound` | For all n>=1, maximum strict-error risk over the two explicit alternatives at radius h/6 is at least `(1-sqrt(exp(n*pi*h^4/8)-1)/2)/2`. Success-event measurability is explicit. |
| `LowerBound.fourth_root_lower_exists`, `fourth_root_minimax_obstruction` | An original-K density attains at least the finite bound. For n>=16, every estimator with measurable success events, including any independent randomization, has strict error greater than n^(-1/4)/6 with probability greater than 1/4 under some original-K density. Output membership in K is not assumed. |

The root acceptance checks these lower results together with the previously accepted upper estimator and law corollary. Deterministic finite-order estimators are included by choosing a one-point random seed; the formal theorem allows any output function with measurable success events. No product-likelihood identity, coordinate observation, independent suborder or stronger density class is left as an endpoint premise.

The [ordinary lower proof](finite-data-information-limit.md) retains the confidence-band distinction: random widths imply a bound on coverage failure **plus** the probability of excessive width; occasional narrow reports and coverage conditional on acceptance are not ruled out. This is an ordinary consequence of the accepted estimator theorem, not a separately claimed Lean theorem about a band implementation. The lower result transfers a coordinate-data obstruction and establishes no additional order-specific information cost. The logarithmic gap and conservative constants remain. The frozen pilot, both manuscript families and their published artifacts are unchanged.

Delivery verifies accepted normalized source bytes against staged Git objects and raw evidence byte-for-byte. The task-owned GCP instance is stopped after evidence collection and a no-other-work process check; its final state is verified TERMINATED in the campaign index. Hosted CI is supplementary and no unobserved CI result is claimed.

Remaining to-do list: S033 bounded literature refresh and concrete manuscript decision. None for the S032 mathematical scope.
