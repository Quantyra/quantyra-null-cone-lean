# Quantitative reconstruction from finite causal orders

[![Verify proofs and manuscript](https://github.com/Quantyra/quantyra-null-cone-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/Quantyra/quantyra-null-cone-lean/actions/workflows/verify.yml)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23202762.svg)](https://doi.org/10.5281/zenodo.23202762)

Lean 4 proof software and a draft preprint by **Daniel Eric Fredriksen, Quantyra Inc.** Developed with OpenAI Codex assistance under the author's research direction.

**Read the [preprint PDF](manuscript/finite-causal-order-reconstruction.pdf)** or its [TeX source](manuscript/finite-causal-order-reconstruction.tex). [Integrity and reproducibility](INTEGRITY.md) Â· [Citation metadata](CITATION.cff) Â· [Zenodo metadata](.zenodo.json) Â· [Changelog](CHANGELOG.md).

## Result and verification scope

For every two-order realizer of a sufficiently covered finite sample, **one global exchange of the null axes** gives **both** interior rank error bounds at most `30rn`, under explicit occupancy, marginal and boundary conditions. This complete finite theorem is Lean verified, including the original specified specialization.

The accompanying mathematical draft derives

```text
d_conf(rho, sigma) <= 100 (N^(-1/12) + Delta_N(rho, sigma)).
Improved prose bound: d_conf <= 130 ((log N / N)^(1/6) + Delta_N).
```

The class comprises smooth densities on the square between `1/2` and `3/2`, with uniform marginals and Euclidean Lipschitz constant at most two. `Delta_N` compares iid finite causal-order laws; `d_conf` compares density coefficients in supremum norm modulo axis exchange. Only abstract orders are observed. The original grid reconstruction probability bound is Lean verified. The [density interpolation bound](QuantyraNullCone/DensityInterpolation.lean) is also Lean verified. The [order-only selector](QuantyraNullCone/OrderSelector.lean) and [observable-TV CDF separation](QuantyraNullCone/FiniteTV.lean) are Lean verified. The [original all-N coefficient bound](QuantyraNullCone/InverseRate.lean) and [all-law identifiability](QuantyraNullCone/Identifiability.lean) are now Lean verified for the actual **labeled directed-order laws**. The labeled/unlabeled TV bridge is still a prose proof, so formal verification does not yet cover the quotient observable. The logarithmic-grid improvement and proper-time consequence retain their separate prose status. Originality and independent review remain unconfirmed. Constants are conservative; no practical sample budget or optimal exponent is claimed.

The active formal extension adds [deterministic coordinate/CDF bridges](QuantyraNullCone/Cumulative.lean), [concrete density/order-law definitions](QuantyraNullCone/Model.lean), [probability normalization](QuantyraNullCone/Measures.lean) and [uniform marginals/CDF threshold stability](QuantyraNullCone/DensityCDF.lean), followed by the [grid-to-CDF bridge](QuantyraNullCone/GridAccuracy.lean). Grid vertices supply the marginal, boundary and latent-CDF accuracy premises. [Sampling and concentration](QuantyraNullCone/ProbabilityRate.lean) now give the original `9/10` reconstruction success bound at `174 n^(-1/4)` for `n>=65536`; density interpolation and observable-TV CDF separation are now proved, and [transpose closure/transport](QuantyraNullCone/Transpose.lean), the original all-N coefficient theorem and all-law identifiability are proved. The labeled/unlabeled law equivalence and final scope reconciliation remain before closing S013.

This is restricted theoretical geometry. It establishes no new physics, general spacetime reconstruction, curvature control or carrying-capacity gain.

## Build

Use elan and Python 3; [INTEGRITY.md](INTEGRITY.md) gives the fresh-checkout dependency and focused-cache commands. Once dependencies are present:

```text
lake build QuantyraNullCone
python checks/check_integrity.py
python checks/check_grid_witnesses.py
python checks/check_small_realizers.py
```

Lean is pinned to **4.30.0**, mathlib to **c5ea00351c28e24afc9f0f84379aa41082b1188f**. All selected export dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`, with no added axioms or admitted proofs. [Verification evidence](notes/lean-verification.md) records the exact statements and retained GCP build provenance, alongside historical local results. CI verifies the library, dependency reports, sanity checks and manuscript compilation.

## Manuscript and research notes

- [Manuscript build and license](manuscript/README.md).
- [Finite-order inverse derivation](notes/finite-order-rate.md) and [author audit](notes/rate-audit.md).
- [Logarithmic-grid optimization](notes/grid-scale-optimization.md): complete improved prose derivation, cutoff, exact constants, audit and finite checks.
- [Full inverse Lean development contracts](notes/full-inverse-lean-plan.md): active extension; unfinished analytic/probability stages are not claimed verified.
- [Further proof review and continuation requirements](notes/proof-review-2026-10-06.md), including explicit cumulative-error and orbit-separation checks. This remains AI-assisted review, not independent refereeing.
- [Selected formal statement](notes/lean-target.md).
- [Label equivalence and proper-time comparison](notes/observable-and-time-audit.md).
- [Novelty assessment](notes/novelty-search.md) and [OpenAI mathematics release comparison](notes/openai-math-review.md).
- [Earlier qualitative kernel argument](notes/identifiability.md) and [historical conditional reduction](notes/quantitative-reduction.md); the later finite derivation supplies its formerly missing hypothesis.

## Citation, archive and licenses

The archived manuscript version **0.2.0** describes the formal scope at its publication; subsequent Lean extensions are documented above and in the verification notes. It has its own open preprint DOI: [10.5281/zenodo.23206773](https://doi.org/10.5281/zenodo.23206773). [Verified deposit evidence](manuscript/deposit/published-record.json) includes the frozen source commit and downloaded PDF/source-bundle hashes. Cite this DOI for the manuscript and the software DOI below for the proof software.

[Version **0.1.0**](https://github.com/Quantyra/quantyra-null-cone-lean/releases/tag/v0.1.0) is published and archived: software version DOI [10.5281/zenodo.23202763](https://doi.org/10.5281/zenodo.23202763); concept DOI [10.5281/zenodo.23202762](https://doi.org/10.5281/zenodo.23202762) covers all versions. Use [CITATION.cff](CITATION.cff) to cite the exact release. [Release text](releases/v0.1.0.md) documents its bounded scope. Zenodo dates the release 7 October 2026 in UTC (6 October locally). The archive includes the preprint but is a **software deposit**, not a manuscript-specific DOI. The main-branch PDF adds the verified software DOI as a post-archive citation annotation; the immutable release PDF predates that annotation. The preprint has not been submitted to arXiv or a journal.

Software, Lean proofs, scripts and repository documentation: [Apache-2.0](LICENSE). Files under `manuscript/`: [CC-BY-4.0](LICENSES/CC-BY-4.0.txt). See [NOTICE](NOTICE) for attribution and license boundaries. Dependencies retain their own licenses.

This is the technical satellite of Quantyra Space Planning E002/S005-S007. The mathematical model and full proof are self-contained here; no private planning checkout is needed to read or build the artifacts.
