# Quantitative reconstruction preprint

Author: Daniel Eric Fredriksen, Quantyra Inc. Latest published manuscript: [0.4.0](https://doi.org/10.5281/zenodo.23247720), 8 October 2026. [Read the PDF](https://zenodo.org/records/23247720/files/finite-causal-order-reconstruction.pdf?download=1), [TeX and frozen package](deposit/v0.4.0/README.md), [publication receipt](deposit/v0.4.0/published-record.json) and [independent DOI/download verification](deposit/v0.4.0/resolution-check.json). The historical [unpublished review candidate](revisions/v0.4.0/README.md) and [paper portfolio decision](../notes/manuscript-portfolio.md) are preserved. Root-level TeX/PDF preserve 0.3.0; the archived software release retains its original 0.1.0 manuscript.

Version 0.4.0 documents the original `100(N^(-1/12) + Delta_N)` and improved `130((log N/N)^(1/6) + Delta_N)` inverse estimates, finite realizer theorem, all-size identifiability, labeled/unlabeled directed-law equivalence, and proper-time comparison for actual absolutely continuous future curves with one shared orientation. These results are now Lean certified. Exact proof/evidence revision `74c1f743d085c63b45ac2bf30008ad5d29b98fbc` has authoritative remote GCP acceptance with 295 selected audits across the library, including separate finite-data and 2+1 modules. No new Lean compilation was needed for this publication. All seven mathematical statement environments remain unchanged from 0.3.1.

The historical [0.3.1 literature revision](https://doi.org/10.5281/zenodo.23225029) credits the inspected Winkler precedents and narrows the candidate contribution; its description of logarithmic-grid and proper-time results as prose reflects its publication date. Originality remains provisional. Quantyra supports open-source decentralized informal feedback and downstream use/testing; specialist review is not a publication prerequisite. The separate [2+1 technical paper](conformal-gauge/README.md) is published as version 0.1.0 under its own [DOI 10.5281/zenodo.23249816](https://doi.org/10.5281/zenodo.23249816); [publication evidence](conformal-gauge/PUBLICATION.md) verifies the independent family and both downloads. The finite-data paper remains deferred.

## Build

With TeX Live or MiKTeX (including latexmk, amsmath, geometry, lmodern, microtype, xurl and hyperref), run from the repository root:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=manuscript/deposit/v0.4.0 manuscript/deposit/v0.4.0/finite-causal-order-reconstruction.tex
```

Alternatively run `pdflatex` twice with the same `-interaction`, `-halt-on-error` and `-output-directory=manuscript` options. The second pass resolves references. Inspect the log for unresolved citations and overfull boxes, and render the PDF for visual review. The PDF is tracked for direct reading and archival inclusion; intermediate TeX files are ignored.

## License and citation

Every file under `manuscript/` is licensed under [CC-BY-4.0](../LICENSES/CC-BY-4.0.txt), copyright 2026 Quantyra Inc. Attribution: Daniel Eric Fredriksen, *Quantitative reconstruction from finite causal orders in a conformal diamond*, preprint, version 0.4.0 (2026), Quantyra Inc., [10.5281/zenodo.23247720](https://doi.org/10.5281/zenodo.23247720). Software elsewhere in the repository is Apache-2.0.

Version 0.3.1 is published at [record 23225029](https://zenodo.org/records/23225029). [Publication receipt](deposit/v0.3.1/published-record.json), [DOI resolution check](deposit/v0.3.1/resolution-check.json) and [frozen package](deposit/v0.3.1/README.md) verify the reviewed files, metadata, same manuscript family and preservation of earlier artifacts. All seven mathematical statements and accepted GCP proof sources are unchanged; finite-data confidence work remains separate.

Version 0.3.0 is published as an open Zenodo preprint at [record 23214579](https://zenodo.org/records/23214579). The [publication receipt](deposit/v0.3.0/published-record.json) verifies metadata, both downloaded files, the shared version family and preservation of the previous manuscript/software archives. The [versioned package](deposit/v0.3.0/README.md) identifies the artifacts and verification. This revision documents the completed original inverse/identifiability formalization, its observable-law equivalence and precise source/evidence links. The mathematical estimates are unchanged. It also clarifies that the density-independent order selector may use classical choice; a lexicographic selector is one possible construction.

Version 0.2.0 remains archived at [10.5281/zenodo.23206773](https://doi.org/10.5281/zenodo.23206773), with its [original receipt](deposit/published-record.json) and frozen bundle. It added the logarithmic-grid bound and explanatory corrections. The historical software release v0.1.0 remains archived at [10.5281/zenodo.23202763](https://doi.org/10.5281/zenodo.23202763), including its original preprint; that release predates the full inverse formalization. No arXiv or journal submission has been made.
