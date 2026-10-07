# Proof scope and integrity

The principal formal result is `QuantyraNullCone.finite_realizer_rank_rigidity_specified`, in [Bridges.lean](QuantyraNullCone/Bridges.lean). Every two-order realizer admits one globally chosen exchange giving both rank errors at most `30rn` at every interior event. Hypotheses specify distinct coordinates, an occupied open grid with `m >= 16`, empirical marginal error at most `2r`, and boundary count at most `20rn`, where `r = 1/m`. The stronger general theorem retains only the marginal assumptions actually used.

| Claim | Evidence | Verification status |
| --- | --- | --- |
| Transitive orientation and comparable-endpoint forcing | `Realizer.lean` | Lean verified; no axioms in the two abstract forcing exports |
| Grid witnesses and common orientation | `Grid.lean` | Lean verified |
| Strip and rank disagreement counts | `Counts.lean`, `Bridges.lean` | Lean verified |
| Both finite rank bounds with one global exchange | `Bridges.lean`, `checks/Audit.lean` | Lean verified; only `propext`, `Classical.choice`, `Quot.sound` dependencies |
| Inclusive rank identity, `32r` coordinate rigidity, deterministic `87r` CDF bridge | `Cumulative.lean` | Compiled deterministic results; concrete analytic/latent-accuracy premises remain explicit |
| Concrete density/order-law definitions and order observable measurability | `Model.lean` | Compiled; full probability-to-density theorem remains incomplete |
| Normalization of the concrete density, iid sample and directed-order laws | `Measures.lean` | Compiled from the original density class; no assumed probability normalization |
| Uniform coordinate marginal measures, CDF threshold stability and unit-edge values | `DensityCDF.lean` | Compiled from K; concrete CDF threshold stability is proved rather than assumed |
| Grid-vertex deductions and concrete deterministic `87r` CDF reconstruction | `GridAccuracy.lean` | GCP compiled; actual K plus occupancy/distinctness/vertex accuracy, without assumed marginal/boundary/CDF conclusions |
| Iid support/null ties, occupancy, concentration and original fourth-root reconstruction probability | `Sampling.lean`, `Coordinates.lean`, `Concentration.lean`, `GoodSamples.lean`, `ProbabilityRate.lean` | GCP verified from original K; `9/10` success at `174 n^(-1/4)` for every `n>=65536` |
| `d_conf <= 100 (N^(-1/12) + Delta_N)` | `manuscript/finite-causal-order-reconstruction.tex`, `notes/finite-order-rate.md` | Mathematical proof draft; reconstruction probability is formalized, while interpolation, observable-TV separation and all-N assembly remain unverified |
| Identifiability, label-law equivalence, proper-time comparison | Manuscript and `notes/observable-and-time-audit.md` | Prose consequences |
| Originality and significance | `notes/novelty-search.md`, `notes/openai-math-review.md` | Provisional; no independent specialist review |

No new axioms, admitted proofs, exact realizer uniqueness assumption, or hypotheses equivalent to the final rank conclusion are introduced. `checks/check_integrity.py` rejects forbidden declarations and audits Lean's printed dependencies. The sanity scripts falsify particular witness/count errors; they do not establish the universal theorem.

## Reproduce the formal result

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
lake exe cache get Mathlib.Probability.Moments.SubGaussian Mathlib.Probability.Independence.Basic Mathlib.Analysis.SpecialFunctions.Exp Mathlib.Analysis.SpecialFunctions.Pow.Real
lake build QuantyraNullCone
python checks/check_integrity.py
python checks/check_grid_witnesses.py
python checks/check_small_realizers.py
python checks/check_grid_scale.py
```

Use `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` on POSIX shells. Stop on a nonzero command exit. The focused cache avoids downloading the entire mathlib build. Successful local verification is recorded in [Lean verification](notes/lean-verification.md); CI records the tested commit and uploads its logs.

## Research and publication boundary

The coefficient estimate applies only to the stated regular two-dimensional class with fixed marginal gauge and residual axis exchange. It controls no curvature or derivatives, proves no new dynamics, and demonstrates no carrying-capacity improvement. The manuscript reports AI assistance. No AI system is listed as an author and no independent review is represented as completed.

GitHub release `v0.1.0` targets commit `51846e81eecbc24d004ef0ec6c621c8ad90e8e52`. Both jobs passed in [CI run 37570765299](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37570765299). Zenodo archived that release as [10.5281/zenodo.23202763](https://doi.org/10.5281/zenodo.23202763), concept DOI [10.5281/zenodo.23202762](https://doi.org/10.5281/zenodo.23202762). The public record confirms author, version, license and tag; its ZIP checksum and included PDF were verified against the release artifact. The separate manuscript v0.2.0 is published at [10.5281/zenodo.23206773](https://doi.org/10.5281/zenodo.23206773), under CC-BY-4.0, with frozen source commit and verified downloads in `manuscript/deposit/published-record.json`. It retains the full inverse theorem's prose status and provisional originality. Existing release artifacts remain unchanged. No arXiv submission or scholarly-profile update is automatic.
