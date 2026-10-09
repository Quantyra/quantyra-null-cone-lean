# S036 logarithmic minimax certification

2026-10-09. The original finite-data density class, single unlabeled strict directed order and one-global-transpose full-square loss are preserved. [Ordinary proof](finite-data-logarithmic-lower-bound.md). Every Lean/Lake development and acceptance invocation in this campaign ran on GCP, project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` are unchanged.

## Complete endpoints

- `logarithmic_randomized_minimax_obstruction`: n>=2^64; any independent probability-space seed; any estimator with measurable simultaneous success events at the target radius; some original-K density has strict error greater than `(log n/n)^(1/4)/8192` with probability at least 1/2. Outputs need not belong to K.
- `logarithmic_lower_bound_at_radius`: the same conclusion at any smaller radius with its own success-event measurability. This prevents an implicit auxiliary-radius assumption.
- `logarithmic_minimax_radius_bounds`: for every seed law, the infimum of nonnegative uniformly achievable 95% radii lies between `(log n/n)^(1/4)/8192` and `min(1/2,650*(log n/n)^(1/4))`. Nonemptiness and boundedness of the infimum set are discharged. The lower theorem is combined with the actual accepted deterministic upper estimator, which ignores the seed.

`LogLowerProfile`, `LogLowerMoments`, `LogLowerAlternatives` and `LogLowerPacking` supply a globally smooth centered-Gaussian family with exact uniform marginals, original Euclidean Lipschitz and range bounds, transpose invariance and separated diagonal witnesses. `LogLowerTesting` proves the many-event inequality. `LogLowerProduct` proves actual iid withDensity identities and independent-seed moment control. `LogLowerScale` discharges the finite logarithmic scale and ceiling. `LogLowerBound` composes these into actual unlabeled-order probabilities and the minimax radius.

The coordinate-data endpoint and the infimum over all seed laws are ordinary consequences explained in the manuscript, not separately named Lean exports. The complete requested order-only endpoint is an exported theorem, not a conditional testing lemma. The rate is optimal up to constants at fixed confidence; sharp constants, expected risk and practical calibration are not claimed.

## Attempts and resolutions

Each immutable run directory retains its input archive, capture hashes, runner, raw logs and terminal status. Failed elaboration reports can contain `sorryAx` for incomplete goals; these failed runs are not acceptance. The final audit rejects such dependencies.

| Run suffix after `space-log-lower-` | Terminal result | Resolution |
| --- | --- | --- |
| `profile-20261009T164705Z-46533a` | 1 | A local hypothesis shadowed bandwidth h in the tail proof; rename to hEst. Initial IAP connection immediately after VM startup also failed; retry submitted the same frozen run once. |
| `alternatives-20261009T165128Z-200e1a` | 1 | `field_simp` already closed the algebra goal; remove the subsequent redundant `ring`. |
| `packing-20261009T165329Z-d31c7f` | 0, two style warnings | Split chained tactics into sequential commands; separation argument unchanged. |
| `testing-20261009T165542Z-99268e` | 0, one deprecation warning | Replace deprecated `push_neg` with `push Not`. |
| `product-20261009T165801Z-5a3121` | 1 | Supply the explicit squared likelihood function to `integral_fun_fst`; the seed integral is one. |
| `bound-20261009T170210Z-3da05e` | 1 | Reciprocal notation was not definitionally equal to one divided by the scale; use `simp only [logLowerScale,one_div]`. |
| `bound-final-20261009T170638Z-1861c9` | 0 | All eight modules and complete endpoints compile; 2962 target-build jobs, standard axioms only. |
| `final-acceptance-20261009T171053Z-0c7e20` | 0 | Full root build: 3035 jobs; 508 unique exact-type/axiom reports, 62 new; zero warnings, standard axioms only; 143 immutable input identities and pinned dependency identities checked before and after. |

There was no mathematical disproof of the proposed rate. The plan preferred compactly supported profiles; globally smooth translated Gaussians were chosen instead to reuse established calculus. Subtracting the exact interval mean preserves both marginals. Explicit tail control replaces disjoint support, and disjoint *success events* still follow from witness separation. Fano/KL machinery was unnecessary. Neither the compact-support preference nor the alternate Fano route is an outstanding obligation.

The general testing method is established: Guntuboyina, Section I, Theorem II.1 and Example II.8 equation (15), l=2. Its proof and relevant examples were inspected. The receipt `evidence/finite-data/s036-literature.json` records source identity and attribution limits. No new-general-testing or exhaustive-priority claim is made.

## Acceptance custody

Final run: `space-log-lower-final-acceptance-20261009T171053Z-0c7e20`; index: `evidence/gcp/s036-logarithmic-final.json`. Root and audit changes are additive. Existing individual Lean modules, pinned dependencies, published manuscripts, historical preparation snapshots and the frozen pilot remain unchanged from `fe7bf812570bd5f6e5b49c9cd7679f3d9dee496c`.

The instance was terminated before this task and started by the first run. Retained live-process checks and cleanup records in the final run document its return to TERMINATED after acceptance. No cache, campaign directory or historical evidence is removed.

Remaining to-do list: none for S036 proof and certification. The [reviewed manuscript revision](../manuscript/finite-data/revisions/v0.2.0/README.md) and its exact formal map are delivered; Zenodo publication and practical-estimator research are separate follow-ups.
