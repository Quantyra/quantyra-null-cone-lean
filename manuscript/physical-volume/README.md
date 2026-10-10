# Interval volume from thinned causal orders

Version 0.1.0, 10 October 2026. **Prepared, unpublished manuscript** under
Quantyra Space story S048. Author: Daniel Eric Fredriksen, Quantyra Inc.

[Read the 14-page PDF](interval-volume-detection.pdf).
[Frozen PDF](prepared/v0.1.0/interval-volume-detection.pdf),
[source and evidence archive](prepared/v0.1.0/interval-volume-detection-source.zip),
[preparation audit](PREPARATION.md).

The paper combines independent thinning, certified finite binomial reporting
and the joint sampling/calibration minimax rate for one marked normalized
interval volume. It includes complete ordinary proofs, randomized full-order
lower bounds and the zero-sample case. The target is a volume fraction; no
absolute physical scale or actual detector performance is inferred.

The original pilot and later geometric finite comparison remain separate.
The exact-binomial report remains the practical choice. Aronow–Lee's binary
transforms and classical confidence calibration receive explicit attribution.
Three other manuscript families remain published and unchanged. This fourth
prepared manuscript has no DOI or deposit. Publication is a separate action.

## Verification and reproduction

The original GCP acceptance is at proof commit
`354fa1f8dc8746328077041ef79d3621837f99e7`, run
`space-volumerate-acceptance-20261010T023105Z-5d08cf`.
Its 797 exact type/axiom reports include 69 distinct exports mapped to this
paper's 13 labeled mathematical statements. The 198-file input snapshot,
raw logs, pinned Lean/mathlib identities and task-owned shutdown are retained.
Preparation did not alter proofs, invoke Lean or collect new samples.

From a full Git checkout containing the historical proof commit:

```text
python manuscript/physical-volume/prepare.py
python manuscript/physical-volume/build.py --tectonic /path/to/tectonic
python manuscript/physical-volume/freeze.py
```

`prepare.py` uses only Python's standard library. It verifies original Git
blobs and the accepted archive, current captured proof dependencies, every
mapped type/axiom report, preserved study sources and manuscript tables.
It regenerates expected artifacts in memory and checks equality; `--write`
is for preparing a reviewed new revision. It never executes Lean/Lake.

`build.py` uses Tectonic 0.17.0 and PyMuPDF; this preparation used Python
3.13.7. It builds the TeX, rejects layout/reference warnings, extracts text
and renders every page under `tmp/s048-manuscript-review`. Rendering alone
does not mark visual review complete. New PDFs require renewed review;
rebuilding may change PDF metadata, so frozen PDF bytes are authoritative.
The retained Windows build has a nonfatal Fontconfig configuration diagnostic;
all 22 PDF fonts are embedded and every page was inspected.

`freeze.py` verifies the prepared PDF, source archive and file manifests.
Its `--write` mode creates the initial immutable package only after the
recorded review; it refuses to replace different bytes in that version.
The archive preserves repository paths and includes its own
`SOURCE-MANIFEST.json`. After unpacking it into a separate directory, run:

```text
python manuscript/physical-volume/verify_bundle.py
python manuscript/physical-volume/build.py --tectonic /path/to/tectonic
```

The portable verifier needs no Git history, Lean, network or third-party
Python package. Build before changing any source, or keep the unpacked
archive immutable for repeated hash verification. To reproduce formal
acceptance, extract the included original `inputs.tar.gz` in a separate
GCP workspace with its pinned dependencies; follow the repository's
GCP-only Lean protocol. No workstation Lean execution is part of these
instructions. Numerical study reruns are unnecessary to verify the preserved
results; their original protocols, code, inputs, failed attempt and audits
are included for inspection.

## Companion records

- `CLAIMS.md` freezes the intended scope.
- `formal-map.json` records exact accepted types, source hashes and the
  distinction between exported statements and elementary prose packaging.
- `literature-map.json` records reviewed editions and source identities.
  `source-review.snapshot.txt` preserves the earlier planning audit verbatim;
  its relative links resolve in the original planning repository identified
  in that map, and its progress wording is historical.
- `table-data.json` and both table TeX files are extracted from preserved
  results, with expected and realized widths kept distinct.
- `evidence-manifest.json` lists the original artifacts and source hashes.
- `review.json` records all-page inspection and claim/source checks.

Manuscript text and PDF: CC BY 4.0, see `LICENSES/CC-BY-4.0.txt` in the
repository/package. Existing source-code licensing is retained in `LICENSE`.
Purchased source PDFs and credentials are excluded.

## Publication handoff

If publication is selected, use a separate manuscript record sharing this
proof repository. Upload the exact reviewed PDF and source archive, use the
PDF as the primary manuscript file, and verify public downloads and DOI
resolution. Do not replace the three existing manuscript records. Confirm
metadata and any text change against this frozen scope; a substantive new
theorem requires GCP acceptance, and a changed PDF requires page review.
Open-source decentralized informal review remains the protocol; specialist
review and adoption are not publication prerequisites.

Remaining to-do list: none for manuscript preparation. Publication is a
separate, unselected follow-up.
