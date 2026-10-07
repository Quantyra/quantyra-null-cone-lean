# Quantitative reconstruction preprint

Author: Daniel Eric Fredriksen, Quantyra Inc. Current manuscript version 0.3.0, 7 October 2026. The archived software release retains its original version 0.1.0 manuscript.

An [unpublished literature revision](working/README.md), with [review PDF](working/finite-causal-order-reconstruction.pdf), now credits the fully inspected Winkler precedents and narrows the candidate contribution. The published 0.3.0 source/PDF and DOI package below remain preserved.

[TeX source](finite-causal-order-reconstruction.tex) and [compiled PDF](finite-causal-order-reconstruction.pdf) present the fixed class, the original `100(N^(-1/12) + Delta_N)` inverse estimate and the improved `130((log N/N)^(1/6) + Delta_N)` estimate, the finite realizer theorem, label-law equivalence, and the proper-time consequence. The finite realizer theorem, original all-N inverse estimate, all-size identifiability and actual labeled/unlabeled law equivalence are formalized in Lean. The optimized logarithmic-grid estimate and proper-time consequence remain prose proofs. Exact proof commit `b7d762acc9c10ca881f8366f545f3998b0528448` has authoritative GCP verification with 68 export audits; see [the retained evidence](../evidence/gcp/space-unlabeled-20261007T123238Z-759aaa/receipt.json). Originality remains provisional. Quantyra supports open-source, decentralized informal feedback and downstream use/testing; specialist review is not a publication prerequisite.

## Build

With TeX Live or MiKTeX (including latexmk, amsmath, geometry, lmodern, microtype, xurl and hyperref), run from the repository root:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=manuscript manuscript/finite-causal-order-reconstruction.tex
```

Alternatively run `pdflatex` twice with the same `-interaction`, `-halt-on-error` and `-output-directory=manuscript` options. The second pass resolves references. Inspect the log for unresolved citations and overfull boxes, and render the PDF for visual review. The PDF is tracked for direct reading and archival inclusion; intermediate TeX files are ignored.

## License and citation

Every file under `manuscript/` is licensed under [CC-BY-4.0](../LICENSES/CC-BY-4.0.txt), copyright 2026 Quantyra Inc. Attribution: Daniel Eric Fredriksen, *Quantitative reconstruction from finite causal orders in a conformal diamond*, preprint, version 0.3.0 (2026), Quantyra Inc., [10.5281/zenodo.23214579](https://doi.org/10.5281/zenodo.23214579). Software elsewhere in the repository is Apache-2.0.

Version 0.3.0 is published as an open Zenodo preprint at [record 23214579](https://zenodo.org/records/23214579). The [publication receipt](deposit/v0.3.0/published-record.json) verifies metadata, both downloaded files, the shared version family and preservation of the previous manuscript/software archives. The [versioned package](deposit/v0.3.0/README.md) identifies the artifacts and verification. This revision documents the completed original inverse/identifiability formalization, its observable-law equivalence and precise source/evidence links. The mathematical estimates are unchanged. It also clarifies that the density-independent order selector may use classical choice; a lexicographic selector is one possible construction.

Version 0.2.0 remains archived at [10.5281/zenodo.23206773](https://doi.org/10.5281/zenodo.23206773), with its [original receipt](deposit/published-record.json) and frozen bundle. It added the logarithmic-grid bound and explanatory corrections. The historical software release v0.1.0 remains archived at [10.5281/zenodo.23202763](https://doi.org/10.5281/zenodo.23202763), including its original preprint; that release predates the full inverse formalization. No arXiv or journal submission has been made.
