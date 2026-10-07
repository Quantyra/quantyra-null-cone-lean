# Quantitative reconstruction preprint

Author: Daniel Eric Fredriksen, Quantyra Inc. Current manuscript version 0.2.0, 6 October 2026. The archived software release retains its original version 0.1.0 manuscript.

[TeX source](finite-causal-order-reconstruction.tex) and [compiled PDF](finite-causal-order-reconstruction.pdf) present the fixed class, the original `100(N^(-1/12) + Delta_N)` inverse estimate and the improved `130((log N/N)^(1/6) + Delta_N)` estimate, the finite realizer theorem, label-law equivalence, and the proper-time consequence. Only the finite realizer theorem is currently formalized in Lean. Originality remains provisional. Quantyra supports open-source, decentralized informal feedback and downstream use/testing; specialist review is not a publication prerequisite.

## Build

With TeX Live or MiKTeX (including latexmk, amsmath, geometry, lmodern, microtype, xurl and hyperref), run from the repository root:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=manuscript manuscript/finite-causal-order-reconstruction.tex
```

Alternatively run `pdflatex` twice with the same `-interaction`, `-halt-on-error` and `-output-directory=manuscript` options. The second pass resolves references. Inspect the log for unresolved citations and overfull boxes, and render the PDF for visual review. The PDF is tracked for direct reading and archival inclusion; intermediate TeX files are ignored.

## License and citation

Every file under `manuscript/` is licensed under [CC-BY-4.0](../LICENSES/CC-BY-4.0.txt), copyright 2026 Quantyra Inc. Attribution: Daniel Eric Fredriksen, *Quantitative reconstruction from finite causal orders in a conformal diamond*, preprint, version 0.2.0 (2026), Quantyra Inc., [10.5281/zenodo.23206773](https://doi.org/10.5281/zenodo.23206773). Software elsewhere in the repository is Apache-2.0.

The manuscript is published as an open Zenodo preprint at [record 23206773](https://zenodo.org/records/23206773); it has not been submitted to arXiv or a journal. The [verified deposit receipt](deposit/published-record.json) records the exact source commit, metadata checks and downloaded-file hashes. The archived source bundle retains the README as it stood before publication; current citation documentation adds the assigned DOI.

Software release v0.1.0 is archived at [10.5281/zenodo.23202763](https://doi.org/10.5281/zenodo.23202763). Its release asset and Zenodo ZIP retain the original preprint. Version 0.2.0 adds the logarithmic-grid bound and explanatory corrections. The old software DOI remains a software citation, not an identifier for a separate manuscript deposit.
