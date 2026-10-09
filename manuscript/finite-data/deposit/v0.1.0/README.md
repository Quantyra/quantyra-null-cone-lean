# Finite-data theory manuscript 0.1.0

Daniel Eric Fredriksen, Quantyra Inc. 9 October 2026. *Finite-sample density reconstruction from a single causal order*. Manuscript: CC-BY-4.0.

Version DOI: [10.5281/zenodo.23265067](https://doi.org/10.5281/zenodo.23265067). Independent manuscript family: [10.5281/zenodo.23265066](https://doi.org/10.5281/zenodo.23265066). [PDF](finite-sample-order-density.pdf), [TeX](finite-sample-order-density.tex), [source archive](finite-sample-order-density-v0.1.0-source.zip). These identifiers are reserved for this edition; public availability is established by the separate published-record and resolution-check receipts.

This third manuscript family is separate from the reconstruction paper [0.4.0](https://doi.org/10.5281/zenodo.23247720) and coordinate-gauge paper [0.1.0](https://doi.org/10.5281/zenodo.23249816). All share the proof repository. The main results are the finite one-order fourth-root upper guarantee, actual-law inverse corollary and randomized lower inequality in the original density class. Conservative constants, classical-choice efficiency limits, uninformative pilot, logarithmic gap and transferred coordinate-data lower obstruction remain explicit.

The mathematical content and bibliography are unchanged from the reviewed S034 draft at b2678573f937f4fb3322a80006e211d11221535d. Exactly two replacements update the title date/status/DOI and one publication-status sentence. Every final page was inspected. Original preparation files and their historical review are preserved two directories above and included at their original paths in the archive.

Proof revision: [6752732882862bc848c7a96722a7660456d6da38](https://github.com/Quantyra/quantyra-null-cone-lean/tree/6752732882862bc848c7a96722a7660456d6da38). Remote GCP run space-degree-final-acceptance-20261009T055238Z-7ba92d accepted 3027 root jobs and 446 selected type/axiom audits across the shared library, with zero warnings and standard axioms only. The paper maps 39 exports. Publication rechecks 135 source identities without invoking Lean/Lake. Every future Lean invocation remains remote GCP-only.

Compile from the repository root with Tectonic 0.17.0:

    tectonic --keep-logs -o manuscript/finite-data/deposit/v0.1.0 manuscript/finite-data/deposit/v0.1.0/finite-sample-order-density.tex

Inspect every page and compiler diagnostics. The new manuscript/finite-data/publish.py reuses the established independent-record publisher: --prepare builds the deterministic archive; --commit FULL_HASH checks exact local/Git bytes without credential access; --publish --commit FULL_HASH uploads and publishes only the reserved independent record; --verify-public --commit FULL_HASH downloads public files and checks metadata, DOI and earlier publications. Publication requires explicit user authorization, supplied for S035 on 9 October 2026. Tests are offline and use no credential.

The source archive retains manuscript/support files under CC-BY-4.0 and the reused checks/ publication helpers under the repository's Apache-2.0 license, with both license texts. It links the exact proof repository rather than redistributing third-party papers, secrets, full cloud logs or Lean caches. Build/source checks that require Git history should run in the full repository at the frozen revision.

OpenAI Codex assistance is disclosed. Review remains open-source, decentralized and informal; specialist review and adoption are not gates.

Remaining to-do list for package preparation: none. Publication completion is recorded separately in published-record.json and resolution-check.json.
