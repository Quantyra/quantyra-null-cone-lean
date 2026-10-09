# Finite-data theory manuscript: working revision 0.2.0

**[Read the revised PDF](finite-sample-order-density.pdf)** · [TeX](finite-sample-order-density.tex) · [formal map](formal-map.json) · [statement review](verification.md) · [page review](review.json) · [source verification](source-verification.json).

This unpublished revision of *Finite-sample density reconstruction from a single causal order* closes the logarithmic minimax gap. For n>=2^64, every eligible estimator, including an arbitrary independent probability-space seed, has strict quotient error greater than `(log n/n)^(1/4)/8192` with probability at least 1/2 under some original-class density. Together with the existing 95% upper radius `min(1/2,650*(log n/n)^(1/4))`, this establishes the fixed-confidence minimax rate up to constants. All main endpoints have exact-source GCP Lean acceptance.

The construction, complete proofs, attribution, original two-point bound, 101-export manuscript map and practical limitations are included. The original density class, observations and one-global-transpose loss are unchanged. Conservative constants and the threshold are explicit. The degree estimator remains unimplemented as a new practical method; the frozen negative pilot is preserved.

The [published 0.1.0 edition](https://doi.org/10.5281/zenodo.23265067) and its [frozen package](../../deposit/v0.1.0/README.md) remain intact. That DOI identifies the published baseline, not this PDF. A subsequent Zenodo version is separate scope. This is a revision in the same finite-data manuscript family, not a fourth research paper.

Run `python manuscript/finite-data/revisions/v0.2.0/verify_sources.py` from the repository to inspect retained source/audit identities without compiling Lean. Run `python manuscript/finite-data/revisions/v0.2.0/build.py --tectonic /path/to/tectonic` to rebuild and render with Tectonic 0.17.0 and PyMuPDF. Rendering is separate from visual review. The proof library is pinned to Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; Quantyra Lean/Lake execution remains GCP-only.

The GCP campaign and all eight attempts are indexed in `evidence/gcp/s036-logarithmic-final.json` at the repository root. The final acceptance checks 143 source/check/config identities, 3035 root jobs and 508 theorem/type/axiom reports, including 62 new exports, with zero warnings and standard axioms only. No conditional packing or likelihood premise remains in the final lower theorem.

Manuscript materials: CC-BY-4.0. Proof library and reused repository helpers: Apache-2.0. Review is AI-assisted, open-source, decentralized and informal; no independent specialist review is claimed.

Remaining to-do list: none for this reviewed revision; publication and practical-estimator research are separate follow-ups.
