# Manuscript 0.3.0 publication audit

2026-10-07. Dan requested manuscript revision, PDF compilation/review and publication of the new version. This closes the technical scope of Space Planning S015.

| Requirement | Evidence and result |
| --- | --- |
| Reflect completed formalization | Abstract, theorem commentary, Section 7, metadata and current citation documentation describe the original all-N inverse theorem and all-size identifiability for actual labeled/unlabeled directed-order laws. Exact audited exports were inspected. The logarithmic-grid and proper-time results retain prose status. |
| Preserve the mathematical claims | All seven theorem/lemma/proposition/corollary environments are byte-identical to manuscript 0.2.0. The selector exposition now explicitly allows the density-independent classical choice used in Lean. No stronger geometry, physics or originality claim was introduced. |
| Compile and inspect the PDF | [Review record](../manuscript/deposit/v0.3.0/review.json) and [raw Tectonic log](../manuscript/deposit/v0.3.0/tex-build.log): nine pages, resolved references, no overfull/underfull boxes or LaTeX warnings. Every page was visually inspected; a stale scope sentence found during review was corrected and its final page re-inspected. The other final page renders matched their inspected images byte-for-byte. |
| Cite authoritative formal evidence | Exact proof/evidence commit `b7d762acc9c10ca881f8366f545f3998b0528448`; current captured proof/check/configuration bytes and that commit were compared against the accepted GCP manifest. The GCP run retains 68 exact-type/axiom reports, 2907 build jobs, zero compiler warnings and no added axioms/admitted proofs. This manuscript revision required no new Lean execution. |
| Freeze the reviewable publication package | [Manifest](../manuscript/deposit/v0.3.0/manifest.json), [bundle receipt](../manuscript/deposit/v0.3.0/bundle.json), reserved DOI inside the PDF, and frozen Git commit `8e32c97ac9cde872efb16b6335cb16a3e9fb369c`. Repeated preparation produced the identical ZIP hash. The dry run verified frozen metadata, source and upload bytes before publication. |
| Publish a linked new version | [Publication receipt](../manuscript/deposit/v0.3.0/published-record.json) and [public record response](../manuscript/deposit/v0.3.0/public-record.json). Published manuscript DOI [10.5281/zenodo.23214579](https://doi.org/10.5281/zenodo.23214579), version 0.3.0, open preprint, CC-BY-4.0. Same manuscript family `10.5281/zenodo.23206772` as 0.2.0. |
| Verify access and content | [DOI resolution and direct-PDF check](../manuscript/deposit/v0.3.0/resolution-check.json). The DOI resolves through Zenodo's DOI route to record 23214579. Both public PDF and ZIP downloads match local/frozen SHA256 and Zenodo MD5 checksums. Title, author, date, version, description, license, type, access, keywords and related identifiers were checked. |
| Preserve history | Both 0.2.0 files were freshly downloaded and matched their original receipt before and after publication. Software 0.1.0 retains its DOI/version and file checksum; its ZIP was downloaded and verified. Original deposit manifests, metadata and bundle remain unchanged. |
| Verify publication tooling | Four offline tests passed, including credential URL restrictions, explicit publication-mode requirements and recovery of the existing family draft without another creation. Six existing credential regressions passed. The preparation guard was exercised after publication and refused to overwrite the package. |
| Supplementary hosted verification | [CI run 37634924986](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37634924986) passed both jobs at frozen commit `8e32c97ac9cde872efb16b6335cb16a3e9fb369c`, including manuscript compilation and existing proof/sanity checks. GCP evidence remains authoritative for the formal claims. |

PDF SHA256: `8abd7fb702dc235a6cfaafc0e8534b396bf380984e401d99fece6afafc2a4c5f`.

Source ZIP SHA256: `09eed732539a559baf36504b0f75a23496ca9ac45a494d1385d042fe9176a9e1`.

The archived source README describes the preparation state, including the reserved DOI. Current repository documentation and the separate publication receipt record the verified publication. That status update does not regenerate the frozen artifacts.

Remaining to-do list: none for manuscript revision and publication. Proper-time/logarithmic-grid Lean extensions and literature/feedback work retain their separate scopes.
