# Conformal-gauge manuscript 0.1.0

Daniel Eric Fredriksen, Quantyra Inc., 8 October 2026. *A certified coordinate-gauge obstruction for causal-order reconstruction in a 2+1 diamond*. CC-BY-4.0.

Version DOI: [10.5281/zenodo.23249816](https://doi.org/10.5281/zenodo.23249816). Independent manuscript family: [10.5281/zenodo.23249815](https://doi.org/10.5281/zenodo.23249815). [PDF](conformal-gauge-counterexample.pdf), [TeX](conformal-gauge-counterexample.tex), [source archive](conformal-gauge-counterexample-v0.1.0-source.zip). The identifiers were reserved for this package; publication and public verification are recorded separately in `published-record.json` and `resolution-check.json` once complete.

This is a separate paper from the reconstruction manuscript [0.4.0](https://doi.org/10.5281/zenodo.23247720). The two papers share the proof repository. The metrics in this construction are isometric, and the conformal flow is established. The contribution is a certified explicit density-class example and coordinate-gauge audit, with formal and prose refinements distinguished. It makes no new-flow, priority, physical nonidentifiability or higher-dimensional inverse-rate claim.

The complete mathematical body is unchanged from the reviewed S028 draft at commit `3b35dc99847a52ed9133557ef2845cf62020640a`. Only the title-page status and DOI label change. That draft, its build artifacts and its review receipt remain preserved two directories above. `review.json` here identifies this final DOI-bearing PDF and its page review. Supporting claim maps, literature comparisons and algebra/source verification are included in the archive at their original repository-relative paths. Third-party papers are not redistributed.

Exact accepted Lean proof/evidence revision: [`74c1f743d085c63b45ac2bf30008ad5d29b98fbc`](https://github.com/Quantyra/quantyra-null-cone-lean/tree/74c1f743d085c63b45ac2bf30008ad5d29b98fbc). GCP run `space-lorentz-acceptance-20261008T071627Z-221cd8` accepted 3001 root build jobs and 295 selected export audits across the shared library. Of the 28 statements mapped to this paper, 27 have separate type/axiom reports and one is a compiled dependency of the audited metric isometry. The manuscript archive links this proof software, licensed Apache-2.0; it does not contain a new software release or Lean binary cache.

Build the final PDF from the repository root using Tectonic 0.17.0:

```text
tectonic --keep-logs -o manuscript/conformal-gauge/deposit/v0.1.0 manuscript/conformal-gauge/deposit/v0.1.0/conformal-gauge-counterexample.tex
```

Inspect every rendered page and the compiler log. The repository's `checks/publish_conformal_gauge.py --prepare` freezes the reviewed package and deterministic source ZIP; `--commit FULL_HASH` checks exact Git/local identities without network calls. `--publish --commit FULL_HASH` uses the existing AWS-held credential only after those checks, and resumes the reserved independent record. `--verify-public --commit FULL_HASH` checks public metadata, file hashes, DOI resolution and preservation of earlier records without credentials. Published package payloads must remain frozen; later changes need a new versioned package.

Lean development/acceptance runs only on remote GCP with the pinned dependencies. This publication reuses verified accepted source identities and needs no new Lean invocation. OpenAI Codex assistance is disclosed; open-source decentralized informal feedback and downstream testing remain the review workflow.

Remaining to-do list for package preparation: none once `review.json` and the frozen manifest are complete. Publication completion is established by the separate public receipts.
