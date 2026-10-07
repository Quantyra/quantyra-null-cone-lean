# Manuscript version 0.3.0

*Quantitative reconstruction from finite causal orders in a conformal diamond*, Daniel Eric Fredriksen, Quantyra Inc., 7 October 2026. CC-BY-4.0. This package updates formal-verification scope after S013; the original mathematical statements remain unchanged.

The original all-N inverse and all-law identifiability for actual labeled and unlabeled directed orders are Lean verified. The logarithmic-grid improvement and proper-time comparison retain their prose status. Originality is provisional and the workflow supports decentralized informal feedback, use and testing.

Exact proof/evidence commit: [`b7d762acc9c10ca881f8366f545f3998b0528448`](https://github.com/Quantyra/quantyra-null-cone-lean/tree/b7d762acc9c10ca881f8366f545f3998b0528448). Authoritative GCP run: `space-unlabeled-20261007T123238Z-759aaa`, 2907 build jobs, 68 selected exact-type/axiom reports, zero compiler warnings. Current proof/check/config bytes match that capture; this manuscript update requires no new Lean execution.

Reserved version DOI: [10.5281/zenodo.23214579](https://doi.org/10.5281/zenodo.23214579), in manuscript family [10.5281/zenodo.23206772](https://doi.org/10.5281/zenodo.23206772). [Draft identity](draft-record.json) records the assigned identifiers. This is a new version of record 23206773, using Zenodo's [versioning workflow](https://help.zenodo.org/docs/deposit/manage-versions/). The historical 0.2.0 bundle/manifests and software 0.1.0 DOI remain preserved.

The package freezes TeX, PDF, manuscript instructions, license, metadata and review evidence. `manifest.json` and `bundle.json` identify the payload. `review.json` records the exact reviewed PDF and proof evidence. After publication, `published-record.json` records the frozen Git commit, live metadata checks, downloaded SHA256/MD5 values and previous-version preservation. This README describes preparation; the publication receipt is authoritative for publication status.

Rebuild locally with Tectonic 0.17.0, or follow the manuscript README's TeX instructions. Lean execution uses the established GCP-only protocol. Prepare with `python checks/prepare_manuscript_version.py`. The preparation guard prevents regeneration once published. Verify the frozen commit with `python checks/publish_manuscript_version.py --commit COMMIT`; the explicit `--publish` mode performs the authorized publication and public download checks.
