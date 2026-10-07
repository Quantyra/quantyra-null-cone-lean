# Quantitative reconstruction from finite causal orders

[![Verify proofs and manuscript](https://github.com/Quantyra/quantyra-null-cone-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/Quantyra/quantyra-null-cone-lean/actions/workflows/verify.yml)

Lean 4 proof software and a draft preprint by **Daniel Eric Fredriksen, Quantyra Inc.** Developed with OpenAI Codex assistance under the author's research direction.

**Read the [preprint PDF](manuscript/finite-causal-order-reconstruction.pdf)** or its [TeX source](manuscript/finite-causal-order-reconstruction.tex). [Integrity and reproducibility](INTEGRITY.md) · [Citation metadata](CITATION.cff) · [Zenodo metadata](.zenodo.json) · [Changelog](CHANGELOG.md).

## Result and verification scope

For every two-order realizer of a sufficiently covered finite sample, **one global exchange of the null axes** gives **both** interior rank error bounds at most `30rn`, under explicit occupancy, marginal and boundary conditions. This complete finite theorem is Lean verified, including the original specified specialization.

The accompanying mathematical draft derives

```text
d_conf(rho, sigma) <= 100 (N^(-1/12) + Delta_N(rho, sigma)).
```

The class comprises smooth densities on the square between `1/2` and `3/2`, with uniform marginals and Euclidean Lipschitz constant at most two. `Delta_N` compares iid finite causal-order laws; `d_conf` compares density coefficients in supremum norm modulo axis exchange. Only abstract orders are observed. The full inverse theorem's probability and continuum arguments are **prose proofs, not Lean verified**. Originality and independent review remain unconfirmed. Constants are conservative; no practical sample budget or optimal exponent is claimed.

This is restricted theoretical geometry. It establishes no new physics, general spacetime reconstruction, curvature control or carrying-capacity gain.

## Build

Use elan and Python 3; [INTEGRITY.md](INTEGRITY.md) gives the fresh-checkout dependency and focused-cache commands. Once dependencies are present:

```text
lake build QuantyraNullCone
python checks/check_integrity.py
python checks/check_grid_witnesses.py
python checks/check_small_realizers.py
```

Lean is pinned to **4.30.0**, mathlib to **c5ea00351c28e24afc9f0f84379aa41082b1188f**. Both final theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`, with no added axioms or admitted proofs. [Verification evidence](notes/lean-verification.md) records the exact statements and local build provenance. CI verifies the library, dependency reports, sanity checks and manuscript compilation.

## Manuscript and research notes

- [Manuscript build and license](manuscript/README.md).
- [Finite-order inverse derivation](notes/finite-order-rate.md) and [author audit](notes/rate-audit.md).
- [Selected formal statement](notes/lean-target.md).
- [Label equivalence and proper-time comparison](notes/observable-and-time-audit.md).
- [Novelty assessment](notes/novelty-search.md) and [OpenAI mathematics release comparison](notes/openai-math-review.md).
- [Earlier qualitative kernel argument](notes/identifiability.md) and [historical conditional reduction](notes/quantitative-reduction.md); the later finite derivation supplies its formerly missing hypothesis.

## Citation, archive and licenses

Version **0.1.0** publication package is prepared. Cite the author, repository and exact release or commit using [CITATION.cff](CITATION.cff). Zenodo's GitHub integration is enabled; **no DOI is asserted until a published record is verified**. [Release text](releases/v0.1.0.md) documents the bounded scope. The preprint has not been submitted to arXiv or a journal.

Software, Lean proofs, scripts and repository documentation: [Apache-2.0](LICENSE). Files under `manuscript/`: [CC-BY-4.0](LICENSES/CC-BY-4.0.txt). See [NOTICE](NOTICE) for attribution and license boundaries. Dependencies retain their own licenses.

This is the technical satellite of Quantyra Space Planning E002/S005-S007. The mathematical model and full proof are self-contained here; no private planning checkout is needed to read or build the artifacts.
