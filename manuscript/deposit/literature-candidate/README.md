# Optional literature-revision publication candidate

Prepared 7 October 2026 for review. The [nine-page working PDF](../../working/finite-causal-order-reconstruction.pdf) credits both fully inspected Winkler articles and narrows the candidate contribution. [Review source bundle](literature-revision-review-source.zip), [exact manifest](manifest.json) and [proposed metadata](proposed-zenodo-metadata.json) make the optional publication decision concrete. No Zenodo draft, new DOI or publication is asserted.

Proposed next version: 0.3.1 in the existing manuscript family, following DOI 10.5281/zenodo.23214579. This is a **review candidate**: the enclosed working PDF remains visibly unpublished and refers to its 0.3.0 baseline. If publication is selected, reserve the actual new version, finalize version/DOI labels, rebuild and inspect all pages, freeze the final payload and verify published metadata/downloaded files. Do not upload this candidate as if those finalization steps were complete.

The original 0.3.0 PDF/ZIP and all earlier DOI artifacts remain immutable. The new Python estimator is not silently inserted into this literature-only manuscript revision; it has its own method, experiments and publication gate. Broader priority remains provisional.

Reproduce the review bundle with `python checks/prepare_literature_candidate.py` (no network writes or Lean). The bundle hash is in [bundle.json](bundle.json); it includes the working TeX/PDF, its preserved baseline TeX for the revision helper, README, license and proposed metadata. The enclosed working source can be compiled directly without retrieving the repository.

Remaining to-do list: optional publication selection and finalization; none for preparing this review candidate.
