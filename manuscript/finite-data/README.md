# Finite-sample density reconstruction from a single causal order

Daniel Eric Fredriksen, Quantyra Inc. Version 0.1.0, 8 October 2026. **Unpublished manuscript; no manuscript DOI assigned.** Prepared under selected S034.

**[Read the 12-page PDF](finite-sample-order-density.pdf)** · [TeX source](finite-sample-order-density.tex) · [Theorem map](formal-map.json) · [Source verification](source-verification.json) · [Page and mathematical review](review.json) · [Review scope](verification.md).

The paper proves a uniform 95% full-square density guarantee from one unlabeled directed order, with radius min(1/2,650(log n/n)^(1/4)), modulo one global coordinate exchange. It includes the actual-law inverse corollary, smooth original-class Gaussian alternatives, the explicit randomized finite lower risk, and the n>=16 radius obstruction n^(-1/4)/6. The main reduction retains points using observed degrees while retaining every true point needed in deep cells. The earlier geometric forcing proof is included and attributed.

This is a theory result. Constants are conservative; the selector uses finite classical choices; the frozen practical pilot remains uninformative. The lower bound holds even with coordinate data, and a logarithmic gap remains. Priority is provisional. The random-width band consequence is ordinary mathematics, not a separately exported Lean band theorem.

This third manuscript family shares the proof repository with the published [reconstruction 0.4.0](https://doi.org/10.5281/zenodo.23247720) and [coordinate-gauge 0.1.0](https://doi.org/10.5281/zenodo.23249816) papers. Their files and the frozen study remain unchanged. Publication and a separate manuscript DOI are subsequent scope.

## Reproduce the package

From the repository root, with Python, PyMuPDF 1.28.2 and Tectonic 0.17.0:

    python manuscript/finite-data/verify_sources.py
    python manuscript/finite-data/build.py --tectonic /path/to/tectonic

The verifier reads source/evidence and checks 135 captured identities against the cited proof commit, 446 retained audit reports, 39 mapped exports and preservation of existing artifacts. Historical utilities with CRLF workstation checkouts are individually identified in the receipt, with their raw hashes and comparison after LF normalization. Accepted Git bytes match exactly. Raw GCP evidence is never normalized.

The builder retains compiler logs and renders every page under ignored tmp/finite-data-manuscript-review. It rejects unresolved references, missing characters and LaTeX layout warnings. Inspect every rendered page before issuing a new review receipt. The recorded preparation review saw correctly rendered fonts despite the machine's nonfatal Fontconfig configuration notice.

Both commands avoid Lean/Lake. The unchanged proofs are supported by commit 6752732882862bc848c7a96722a7660456d6da38, GCP run space-degree-final-acceptance-20261009T055238Z-7ba92d: 3027 root jobs, 446 exact-type/axiom audits, zero warnings, standard axioms only. Every future Lean invocation must run on remote GCP under [INTEGRITY.md](../../INTEGRITY.md) and the existing compute protocol.

All files in this manuscript package are CC-BY-4.0; the proof library is Apache-2.0. AI assistance is disclosed in the paper. Review remains open-source, decentralized and informal; specialist review and adoption are not gates.

Remaining to-do list: none for S034 preparation. Separate publication/DOI work is subsequent scope.
