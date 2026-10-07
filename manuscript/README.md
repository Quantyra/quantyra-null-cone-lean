# Quantitative reconstruction preprint

Author: Daniel Eric Fredriksen, Quantyra Inc. Version 0.1.0, 6 October 2026.

[TeX source](finite-causal-order-reconstruction.tex) and [compiled PDF](finite-causal-order-reconstruction.pdf) present the fixed class, the complete mathematical derivation of the `100(N^(-1/12) + Delta_N)` inverse estimate, the finite realizer theorem, label-law equivalence, and the proper-time consequence. Only the finite realizer theorem is currently formalized in Lean. Originality and independent review remain unconfirmed.

## Build

With TeX Live or MiKTeX (including latexmk, amsmath, geometry, lmodern, microtype, xurl and hyperref), run from the repository root:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=manuscript manuscript/finite-causal-order-reconstruction.tex
```

Alternatively run `pdflatex` twice with the same `-interaction`, `-halt-on-error` and `-output-directory=manuscript` options. The second pass resolves references. Inspect the log for unresolved citations and overfull boxes, and render the PDF for visual review. The PDF is tracked for direct reading and archival inclusion; intermediate TeX files are ignored.

## License and citation

Every file under `manuscript/` is licensed under [CC-BY-4.0](../LICENSES/CC-BY-4.0.txt), copyright 2026 Quantyra Inc. Attribution: Daniel Eric Fredriksen, *Quantitative reconstruction from finite causal orders in a conformal diamond*, draft preprint, version 0.1.0 (2026), Quantyra Inc. Cite the repository's exact release/commit until a manuscript-specific DOI exists. Software elsewhere in the repository is Apache-2.0.

The manuscript is prepared for public review; it has not been submitted to arXiv or a journal, and no manuscript-specific DOI is claimed.

Software release v0.1.0 is archived at [10.5281/zenodo.23202763](https://doi.org/10.5281/zenodo.23202763). The main-branch TeX/PDF adds this citation after archival; the release asset and Zenodo ZIP retain the original preprint. The mathematics is unchanged. This is a software DOI, not a separate preprint deposit.
