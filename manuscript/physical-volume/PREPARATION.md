# S048 manuscript preparation audit

2026-10-10. **Complete unpublished preparation**, version 0.1.0:
*Interval volume from thinned causal orders: finite confidence and calibration
limits*, Daniel Eric Fredriksen, Quantyra Inc.

[Reviewed 14-page PDF](prepared/v0.1.0/interval-volume-detection.pdf),
[source/evidence archive](prepared/v0.1.0/interval-volume-detection-source.zip),
[frozen manifest](prepared/v0.1.0/manifest.json), [reproduction instructions](README.md).
Planning: Quantyra-Space-Planning/S048, selected by Dan's manuscript goal.

## Acceptance evidence

| Requirement | Verified result |
| --- | --- |
| Frozen scope and observation model | `CLAIMS.md` and Section 2 specify neighborhood smoothness, Euclidean Lipschitz class, normalized units, global detector bounds, fixed distinguished anchors, full marked order and arbitrary independent seed. |
| Complete proofs and accepted endpoints | Sections 2–5 give geometry, finite/mixed/Poisson/stopped thinning, confidence inversion, rational certificates, actual likelihoods, admitted detector alternatives, joint upper/lower theorem and n=0. `formal-map.json` maps all 13 labeled mathematical statements to 69 distinct accepted exports and distinguishes elementary prose packaging. |
| Source attribution | Binary transforms credited to Aronow–Lee; confidence calibration to Clopper–Pearson and Hoeffding. Reviewed editions of Imbens–Manski, Stoye and Tudball are identified. Original source audit is preserved with its Git provenance. Purchased article and supplement hashes rechecked privately. |
| Preserved studies and method decision | Section 6 separates the 1,200-row generic pilot and its geometric checks from the 1,108 paired reports and 1,656 exact coverage cells of the later study. Expected and realized widths differ explicitly. The original 187/200 fluctuation and failed dependency attempt remain visible. The exact-binomial practical report is retained. |
| PDF and reproducibility | Tectonic build passes without TeX layout/reference warnings. All 14 pages visually inspected; bibliography pagination repaired and checked again. All 22 fonts embedded. Portable package hash verification passes, and a fresh extraction rebuilds all 14 pages with identical rendered image hashes. `review.json` and `package-verification.json` retain the evidence. |

The original full GCP acceptance at proof commit
`354fa1f8dc8746328077041ef79d3621837f99e7` remains authoritative:
198 captured files, 797 exact type/axiom reports, 3,097 root jobs, zero
warnings and verified task-owned instance shutdown. The source verifier
checks original archive/Git equality and current captured proof dependencies.
Only `propext`, `Classical.choice` and `Quot.sound` occur in the accepted
reports. The mapped exports are a subset of that audit, not new proofs.

No new Lean invocation or sample collection was needed. Every pre-existing
tracked artifact at baseline `1085d086dd77d50f59114cad5cb0d8f0a35520c9`
is preserved except the explicitly allowed navigation/licensing attributes:
root README, manuscript portfolio and `.gitattributes`. Earlier manuscripts,
DOI artifacts, Lean sources and frozen studies are unchanged.

## Frozen bytes

- PDF SHA256: `38c6dc47d341e38e69817d4f18301d6810d8c147d6ffb23b1ee405974d235ee5`.
- Source ZIP SHA256: `c271f631b5159d5408264e893539ed7a4b2dacf8a695ac61282e7a1bddbca478`.
- ZIP size: 1,121,285 bytes; 71 payload files plus its manifest.
- The working PDF and frozen PDF are byte-identical. A rebuilt PDF may have
  different metadata; identical page renders establish the verified build's
  visual equivalence, not a promise of globally deterministic PDF binaries.

The preserved Tectonic log includes a nonfatal Windows Fontconfig diagnostic.
It did not prevent compilation, font embedding or clean page review. Python
and SciPy semantics remain software evidence, not kernel certification.
The review is an agent manuscript review, not independent specialist review.

## Publication handoff

Preparation has created no Zenodo deposit or DOI. There are three published
families and this fourth unpublished manuscript. If publication is selected,
create a separate manuscript record using the frozen PDF as the primary
file and the source ZIP as its companion. Verify metadata, public download
hashes and DOI resolution at that time. Existing manuscript records remain
separate. The [handoff](README.md#publication-handoff) requires review of any
changed PDF and GCP acceptance for a substantive new theorem, with the
existing open-source informal review protocol.

The planning completion audit records focused repository delivery identities.

Remaining to-do list: none for S048 preparation. Publication is a separate,
unselected follow-up.
