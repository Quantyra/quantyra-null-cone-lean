# Quantitative reconstruction from finite causal orders

[![Verify proofs and manuscript](https://github.com/Quantyra/quantyra-null-cone-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/Quantyra/quantyra-null-cone-lean/actions/workflows/verify.yml)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23202762.svg)](https://doi.org/10.5281/zenodo.23202762)

Lean 4 proof software and a preprint by **Daniel Eric Fredriksen, Quantyra Inc.** Developed with OpenAI Codex assistance under the author's research direction.

[Research and exact-proof navigation](RESEARCH.md) · [Contribute an error, prior-work report or test](CONTRIBUTING.md) · [Observed community evidence](notes/community-evidence.md) · [Finite-data CLI](tools/FINITE_DATA.md).

**Read the [preprint PDF](manuscript/finite-causal-order-reconstruction.pdf)** or its [TeX source](manuscript/finite-causal-order-reconstruction.tex). [Integrity and reproducibility](INTEGRITY.md) Â· [Citation metadata](CITATION.cff) Â· [Zenodo metadata](.zenodo.json) Â· [Changelog](CHANGELOG.md).

## Result and verification scope

The original inverse estimate and all-size identifiability are **Lean verified for actual unlabeled directed-order laws**:

```text
d_conf(rho, sigma) <= 100 (N^(-1/12) + Delta_N(rho, sigma)), N >= 2.
Improved prose bound: d_conf <= 130 ((log N / N)^(1/6) + Delta_N).
```

The class comprises smooth densities on the square between `1/2` and `3/2`, with uniform marginals and Euclidean Lipschitz constant at most two. `Delta_N` compares iid finite causal-order laws; `d_conf` compares density coefficients in supremum norm modulo one global axis exchange. Equal laws at every size imply equality of the densities on the square up to that exchange. Observations contain only the directed order, without latent coordinates or rankings; time reversal is not included in the quotient.

The formal proof includes finite realizer rank rigidity, normalization, cumulative reconstruction, occupancy/concentration, density interpolation, an order-only selector, TV separation, transpose transport, iid exchangeability and exact equality of labeled/unlabeled TV and `Delta_N`. Final statements are in [InverseRate.lean](QuantyraNullCone/InverseRate.lean), [Identifiability.lean](QuantyraNullCone/Identifiability.lean) and [Unlabeled.lean](QuantyraNullCone/Unlabeled.lean). The [verification notes](notes/lean-verification.md) map all stages to their source and retained GCP evidence.

The logarithmic-grid improvement and proper-time consequence remain prose proofs. Their Lean formalization is optional future work. Originality remains provisional; constants are conservative and no practical sample budget or optimal exponent is claimed. Quantyra follows open-source, decentralized informal feedback and downstream testing; specialist review is not a publication gate.

The [full Winkler comparison](notes/winkler-full-text-comparison.md) now establishes earlier coordinate-forcing and stronger flat-model rank recovery precedents. An [unpublished literature revision](manuscript/working/README.md) credits those results; the published artifacts remain intact. Next research is scoped in [finite-data estimation](notes/finite-data-follow-up-scope.md). The [higher-dimensional feasibility check](notes/higher-dimensional-feasibility.md) rejects a naive coordinate-density extension through an explicit conformal-gauge counterexample and records the reopening requirements.

This is restricted theoretical geometry. It establishes no new physics, general spacetime reconstruction, curvature control or carrying-capacity gain.

## Build

Quantyra development and acceptance Lean commands below execute on remote GCP. Existing GCP evidence remains authoritative; hosted CI is supplementary. The finite-data Python CLI and tests are separate and do not compile Lean.

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
- [Full inverse Lean development contracts](notes/full-inverse-lean-plan.md): completed original inverse and identifiability scope, with separately optional extensions.
- [Further proof review and continuation requirements](notes/proof-review-2026-10-06.md), including explicit cumulative-error and orbit-separation checks. This remains AI-assisted review, not independent refereeing.
- [Selected formal statement](notes/lean-target.md).
- [Label equivalence and proper-time comparison](notes/observable-and-time-audit.md).
- [Novelty assessment](notes/novelty-search.md) and [OpenAI mathematics release comparison](notes/openai-math-review.md).
- [Earlier qualitative kernel argument](notes/identifiability.md) and [historical conditional reduction](notes/quantitative-reduction.md); the later finite derivation supplies its formerly missing hypothesis.

## Citation, archive and licenses

Manuscript version **0.3.0** updates the verification scope to cover the original inverse theorem, identifiability and actual labeled/unlabeled laws. [Verified publication receipt](manuscript/deposit/v0.3.0/published-record.json); published manuscript DOI [10.5281/zenodo.23214579](https://doi.org/10.5281/zenodo.23214579). Its exact proof/evidence revision is [`b7d762acc9c10ca881f8366f545f3998b0528448`](https://github.com/Quantyra/quantyra-null-cone-lean/tree/b7d762acc9c10ca881f8366f545f3998b0528448).

Historical manuscript **0.2.0** remains at [10.5281/zenodo.23206773](https://doi.org/10.5281/zenodo.23206773), with its [unchanged receipt and frozen artifacts](manuscript/deposit/published-record.json). Its PDF describes the earlier formal scope. Use the manuscript DOI for the paper and the software DOI below for the historical proof software release.

[Version **0.1.0**](https://github.com/Quantyra/quantyra-null-cone-lean/releases/tag/v0.1.0) is published and archived: software version DOI [10.5281/zenodo.23202763](https://doi.org/10.5281/zenodo.23202763); concept DOI [10.5281/zenodo.23202762](https://doi.org/10.5281/zenodo.23202762) covers all versions. Use [CITATION.cff](CITATION.cff) to cite the exact release. [Release text](releases/v0.1.0.md) documents its bounded scope. Zenodo dates the release 7 October 2026 in UTC (6 October locally). The archive includes the preprint but is a **software deposit**, not a manuscript-specific DOI. The current manuscript cites the archived software release and the later formalization by its exact source commit. The preprint has not been submitted to arXiv or a journal.

Software, Lean proofs, scripts and repository documentation: [Apache-2.0](LICENSE). Files under `manuscript/`: [CC-BY-4.0](LICENSES/CC-BY-4.0.txt). See [NOTICE](NOTICE) for attribution and license boundaries. Dependencies retain their own licenses.

This is the technical satellite of Quantyra Space Planning E002/S005-S007. The mathematical model and full proof are self-contained here; no private planning checkout is needed to read or build the artifacts.
