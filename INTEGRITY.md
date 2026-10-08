# Proof scope and integrity

The finite formal result is `QuantyraNullCone.finite_realizer_rank_rigidity_specified`, in [Bridges.lean](QuantyraNullCone/Bridges.lean). Every two-order realizer admits one globally chosen exchange giving both rank errors at most `30rn` at every interior event. Hypotheses specify distinct coordinates, an occupied open grid with `m >= 16`, empirical marginal error at most `2r`, and boundary count at most `20rn`, where `r = 1/m`. The stronger general theorem retains only the marginal assumptions actually used. The formal extension now also proves `InDensityClass.full_inverse` and `InDensityClass.all_law_identifiability` for the actual labeled directed-order laws, and their unlabeled isomorphism classes, with actual iid exchangeability and TV/Delta equivalence proved.

| Claim | Evidence | Verification status |
| --- | --- | --- |
| Transitive orientation and comparable-endpoint forcing | `Realizer.lean` | Lean verified; no axioms in the two abstract forcing exports |
| Grid witnesses and common orientation | `Grid.lean` | Lean verified |
| Strip and rank disagreement counts | `Counts.lean`, `Bridges.lean` | Lean verified |
| Both finite rank bounds with one global exchange | `Bridges.lean`, `checks/Audit.lean` | Lean verified; only `propext`, `Classical.choice`, `Quot.sound` dependencies |
| Inclusive rank identity, `32r` coordinate rigidity, deterministic `87r` CDF bridge | `Cumulative.lean` | Compiled deterministic results; concrete analytic/latent-accuracy premises remain explicit |
| Concrete density/order-law definitions and order observable measurability | `Model.lean` | GCP verified; the full original probability-to-density inverse theorem is complete in the later modules below |
| Normalization of the concrete density, iid sample and directed-order laws | `Measures.lean` | Compiled from the original density class; no assumed probability normalization |
| Uniform coordinate marginal measures, CDF threshold stability and unit-edge values | `DensityCDF.lean` | Compiled from K; concrete CDF threshold stability is proved rather than assumed |
| Grid-vertex deductions and concrete deterministic `87r` CDF reconstruction | `GridAccuracy.lean` | GCP compiled; actual K plus occupancy/distinctness/vertex accuracy, without assumed marginal/boundary/CDF conclusions |
| Iid support/null ties, occupancy, concentration and original fourth-root reconstruction probability | `Sampling.lean`, `Coordinates.lean`, `Concentration.lean`, `GoodSamples.lean`, `ProbabilityRate.lean` | GCP verified from original K; `9/10` success at `174 n^(-1/4)` for every `n>=65536` |
| Boundary-valid density interpolation and actual coefficient supremum attainment | `DensityInterpolation.lean` | GCP verified: actual K plus CDF error epsilon imply coefficient deviation cubed at most `2048 epsilon` |
| One measurable order-only selector, finite-law event TV bound and CDF orbit separation | `OrderSelector.lean`, `FiniteTV.lean` | GCP verified from actual K: `n>=65536` and observed TV below `4/5` give one global CDF orientation with error `348 n^(-1/4)` |
| Transpose closure of K, density-measure/CDF transport and coefficient isometry | `Transpose.lean` | GCP verified with the original Euclidean Lipschitz definition |
| `d_conf <= 100 (N^(-1/12) + Delta_N)` | `manuscript/finite-causal-order-reconstruction.tex`, `notes/finite-order-rate.md` | GCP verified in `InverseRate.lean` for actual labeled directed-order laws, every N>=2, only original K; `Unlabeled.lean` proves the same bound for actual directed-order isomorphism classes |
| All-law coefficient identifiability on the square under one global identity/transpose | `Identifiability.lean` | GCP verified from equality of every labeled iid directed-order law; no assumed coefficient equality |
| Iid relabeling invariance, exact labeled/unlabeled TV/Delta equivalence, quotient-law inverse and identifiability | `Exchangeability.lean`, `QuotientTV.lean`, `Unlabeled.lean` | GCP verified from actual K and iid laws; quotient is directed-order isomorphism, without time-dual identification |
| `d_conf <=130 ((log N/N)^(1/6)+Delta_N)` | `LogGridRate.lean`, `ImprovedInverse.lean` | GCP verified from original K for all N>=2, actual labeled/unlabeled laws; [acceptance](notes/logarithmic-certification.md) |
| Proper-time comparison and original/improved unlabeled-law consequences | `ProperTime.lean` | GCP verified for actual AC future curves, including empty-class zero and one global orientation for every pair; [acceptance](notes/proper-time-certification.md) |
| Originality and significance | `notes/novelty-search.md`, `notes/winkler-full-text-comparison.md` | Provisional; earlier forcing and stronger flat-model recovery credited; no priority certificate |

No new axioms, admitted proofs, exact realizer uniqueness assumption, or hypotheses equivalent to the final rank conclusion are introduced. `checks/check_integrity.py` rejects forbidden declarations and audits Lean's printed dependencies. The sanity scripts falsify particular witness/count errors; they do not establish the universal theorem.

## Reproduce the formal result

Quantyra development/acceptance Lean commands below run on remote GCP under the established compute protocol. Authoritative exact-source evidence is retained; hosted CI is supplementary. Local editing, hashing, inspection and the separate Python finite-data tests do not invoke Lean. [Research navigation](RESEARCH.md) and [contribution handling](CONTRIBUTING.md) distinguish current formal results, prose arguments and feedback evidence.

Install elan and Python 3. The toolchain file selects Lean 4.30.0; the manifest and lakefile pin mathlib to `c5ea00351c28e24afc9f0f84379aa41082b1188f`. From this repository:

```powershell
$previousCacheSetting = $env:MATHLIB_NO_CACHE_ON_UPDATE
try {
  $env:MATHLIB_NO_CACHE_ON_UPDATE = "1"
  lake update
} finally { $env:MATHLIB_NO_CACHE_ON_UPDATE = $previousCacheSetting }
lake exe cache get Mathlib.Data.Real.Archimedean Mathlib.Algebra.Order.Floor.Semiring Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
lake exe cache get Mathlib.Analysis.Calculus.ContDiff.Basic Mathlib.MeasureTheory.Measure.WithDensity Mathlib.MeasureTheory.Measure.Lebesgue.Basic Mathlib.MeasureTheory.Constructions.Pi Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
lake exe cache get Mathlib.MeasureTheory.Integral.Prod Mathlib.MeasureTheory.Function.LocallyIntegrable
lake exe cache get Mathlib.Probability.Moments.SubGaussian Mathlib.Probability.Independence.Basic Mathlib.Analysis.SpecialFunctions.Exp Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
lake build QuantyraNullCone
python checks/check_integrity.py
python checks/check_grid_witnesses.py
python checks/check_small_realizers.py
python checks/check_grid_scale.py
```

Use `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` on POSIX shells. Stop on a nonzero command exit. The focused cache avoids downloading the entire mathlib build. Authoritative GCP verification is recorded in [Lean verification](notes/lean-verification.md), alongside historical local results; supplementary CI records the tested commit and uploads its logs.

## Research and publication boundary

The coefficient estimate applies only to the stated regular two-dimensional class with fixed marginal gauge and residual axis exchange. It controls no curvature or derivatives, proves no new dynamics, and demonstrates no carrying-capacity improvement. The manuscript reports AI assistance. No AI system is listed as an author and no independent review is represented as completed.

GitHub release `v0.1.0` targets commit `51846e81eecbc24d004ef0ec6c621c8ad90e8e52`. Both jobs passed in [CI run 37570765299](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37570765299). Zenodo archived that release as [10.5281/zenodo.23202763](https://doi.org/10.5281/zenodo.23202763), concept DOI [10.5281/zenodo.23202762](https://doi.org/10.5281/zenodo.23202762). The public record confirms author, version, license and tag; its ZIP checksum and included PDF were verified against the release artifact. The separate manuscript v0.2.0 is published at [10.5281/zenodo.23206773](https://doi.org/10.5281/zenodo.23206773), under CC-BY-4.0, with frozen source commit and verified downloads in `manuscript/deposit/published-record.json`. It retains the full inverse theorem's prose status and provisional originality. Existing release artifacts remain unchanged. No arXiv submission or scholarly-profile update is automatic.

Current manuscript [0.3.0](https://doi.org/10.5281/zenodo.23214579) documents the completed original formalization, with [publication receipt](manuscript/deposit/v0.3.0/published-record.json). Earlier archives retain historical verification wording. The [unpublished literature revision](manuscript/working/README.md) credits newly inspected precedents. [Community evidence](notes/community-evidence.md) records actual internal/outside tests and reports without requiring specialist review or adoption.
