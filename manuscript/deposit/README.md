# Separate manuscript deposit package

Version 0.2.0 of *Quantitative reconstruction from finite causal orders in a conformal diamond*, by Daniel Eric Fredriksen, Quantyra Inc., dated 6 October 2026. Intended destination: a separate Zenodo record of type publication/preprint, with open access and CC-BY-4.0. Dan's instruction to complete the manuscript-deposit story authorizes that deposit; authentication is still needed to execute it.

The package includes the reviewed eight-page PDF and TeX source, manuscript instructions, license, prepared metadata, content hashes and a deterministic source ZIP. The full inverse theorem remains prose in this version; only the finite realizer rank theorem is currently Lean verified. The logarithmic-grid estimate has an author-directed mathematical audit and high-precision finite checks. Originality remains provisional. Source and artifacts support Quantyra's decentralized informal review philosophy.

Run `python checks/prepare_manuscript_deposit.py` from the repository root to regenerate and verify the package. [Metadata](zenodo-metadata.json), [file manifest](manifest.json), and [bundle receipt](bundle.json) identify the exact payload. The software version DOI `10.5281/zenodo.23202763` remains a citation to the existing software release. No manuscript DOI is assigned by these files; a real published record must supply it.

Local verification: Tectonic 0.17.0 compiled the revised TeX without unresolved references or overfull boxes; all eight pages rendered with PyMuPDF 1.28.2 were visually inspected. Preserve the original v0.1.0 GitHub/Zenodo release artifacts. A deposit receipt will record the source commit, record URL/DOI, actual metadata and downloaded-file identity after publication.

Remaining to-do list: authenticate, publish the separate manuscript record, verify its metadata/downloads, and update citations and planning with the actual identifier.
