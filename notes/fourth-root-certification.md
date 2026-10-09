# Fourth-root finite-data certification campaign

S032, selected 2026-10-08 under the goal "complete steps 1-3". Baseline `436e36a05b4234870200871bd1adc8c082163c7f`. **Translation underway; full endpoints are not yet certified.** The complete ordinary arguments remain in [the upper proof](finite-data-interior-degree-rate.md) and [the lower proof](finite-data-information-limit.md), with their [audit](finite-data-feasibility-proof-audit.md). S031's completed pilot and its negative practical disposition are preserved.

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

Every Lean/Lake invocation runs on project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. The instance was observed TERMINATED at selection. Each attempt uses a unique captured source directory, pinned Lean 4.30.0/mathlib/dependencies, one compiler and retained terminal diagnostics. No workstation Lean compilation is permitted. Historical captures and published manuscripts remain intact.

Remaining to-do list: actual shifted grid and observable histogram; floor/scale/clamping/fallback bounds; measurable selection on actual unlabeled orders and full upper guarantee; same-class lower construction/divergence/testing; actual-law corollary; final S032 acceptance/delivery; then S033 manuscript reassessment.
