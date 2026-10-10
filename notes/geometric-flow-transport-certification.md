# Conformal flow transport for actual causal curves

S042 component, 2026-10-09 (Hawaii). **Full GCP acceptance passes: 1,107 exact type/axiom reports, including 29 new results, with zero warnings.** The accepted conformal-flow pair has zero geometric distortion despite its positive coordinate distance. S042 remains incomplete and S043 remains gated.

## Curve and time transport

[LorentzFlowCone.lean](../QuantyraNullCone/LorentzFlowCone.lean) proves that the actual Cartesian derivative preserves the future cone at every point of the closed diamond. For timelike velocities, the conformal bilinear identity keeps the Lorentz square negative along the parameter path from the identity flow. Continuity and the intermediate value theorem prevent the time component from changing sign. Approximating a null velocity by timelike ones gives the closed-cone result, including the zero velocity. The proper speed scales by the positive conformal factor.

[LorentzCurveMap.lean](../QuantyraNullCone/LorentzCurveMap.lean) proves absolute continuity under Lipschitz composition from the actual interval definition, derives vector absolute continuity and the almost-everywhere derivative from the existing coordinatewise curve fields, and constructs mapped curves in the same `FutureCurve3` class. The chain rule gives their actual derivatives. A pointwise weighted-speed identity then gives exact equality of the length integrals and a one-sided comparison of the existing time suprema. The generic map hypotheses are explicit; the subsequent flow specialization proves them.

[LorentzFlowTime.lean](../QuantyraNullCone/LorentzFlowTime.lean) proves convexity of the closed diamond and obtains a Lipschitz bound from the accepted smoothness and compactness. It instantiates every causal-map hypothesis for each flow parameter `abs(a)<1`. The conformal weight action `z(F_a(p))*factor_a(p)=w(p)` and the inverse flow give equality of the actual weighted AC time separations. The accepted normalized gauge density has exactly the required cube-root weight. Both forward and inverse time identities hold on the full closed diamond, including its boundary.

## Geometric loss and scope

[LorentzGaugeDistortion.lean](../QuantyraNullCone/LorentzGaugeDistortion.lean) lifts original measure transport to the closed-diamond laws. Pushing one source point to its source profile and its mapped target profile constructs a coupling of the exact quotient laws. Time preservation holds for two independent draws, so this is a zero coupling. For the accepted gauge pair, the previously proved original measure transport and the new actual time identity yield

    geometricDistortion3(gauge density, flat density) = 0,
    gaugeO2Distance3 > 0.

Thus the selected geometric loss removes the known coordinate-gauge obstruction. The earlier zero-isomorphy theorem also supplies a measure-preserving time homeomorphism of these particular quotient spaces.

The result covers the explicit conformal-flow family with its weight action and the accepted normalized counterexample. The full intended equivalence with arbitrary future-preserving smooth metric isometries of the open spacetimes retains its general bridge and the explicit external journal reconstruction dependency. No external theorem is introduced as a Lean axiom. Density forward control, quantitative conditioning and finite confidence remain open; this component does not establish physical applicability or finite reconstruction.

## Verification and delivery

The 29 endpoints comprise six derivative/cone results, ten AC-map results, seven flow/time results and six measure/loss results. The 5 failed development runs retain their immutable inputs and complete diagnostics. `space-flow3-dev6-20261010T091219Z-df623c` passes all 29 new reports and 3,009 jobs with zero warnings. Its remote runner completed with exit zero; the local SSH process then returned Windows status 3221225477 after printing remote success. Separate observation and collection verify the saved remote terminal state and source receipt; the transport error is retained and is not treated as a compiler failure or a successful controller exit. The campaign initially encountered expired GCP authentication before remote submission. Dan completed the requested browser sign-in; the existing immutable capture was then submitted. Authentication credentials and browser-authentication logs remain outside Git.

Proof commit `172bba9b05332d5dbd2c261e52ac309cf855939d` is pushed before full acceptance. Run `space-flow3-acceptance-20261010T091935Z-26b822` passes 3,156 root jobs and all 1,107 reports. The [receipt](../evidence/gcp/space-flow3-acceptance-20261010T091935Z-26b822/receipt.json) and [independent verification](../evidence/gcp/space-flow3-acceptance-20261010T091935Z-26b822/delivery-verification.json) check all 229 captured files, including 195 Lean inputs, against the immutable archive, raw committed Git blobs and normalized local sources. Source and pinned dependency identities are checked before and after execution. All axioms are standard, all 1,078 previous audit statements remain verbatim, and earlier mathematical modules are unchanged. Archive SHA-256: `11e72787421692613314aaf5b3afd52c7a916d519749f60b6edc478f41892616`.

After the first three development runs, the bounded storage cleanup verified the manifest, immutable archive and every extracted source hash for those three runs and `space-zero3-dev4-20261010T082227Z-23c984`. It then removed only redundant extracted source files from those four terminal development runs. The first receipt is [retained](../evidence/gcp/space-flow3-dev3-20261010T085415Z-a1bdae/read-090125.stdout.txt). A [second cleanup](../evidence/gcp/space-flow3-dev5-20261010T090651Z-0bfd3f/read-091134.stdout.txt) applies the same complete validation to development runs four and five. Immutable archives, manifests, logs, receipts, shared dependencies, shared caches and acceptance source extractions remain preserved. Each collected development run also records bounded cleanup of its own ephemeral build-cache link and cache when present.

The [cleanup receipt](../evidence/gcp/space-flow3-acceptance-20261010T091935Z-26b822/cleanup.json) confirms task ownership, no other Lean work, evidence collection before shutdown and final state `TERMINATED` at `2026-10-10T09:28:22.197562+00:00`. All Lean/Lake execution is on GCP. Earlier publications and frozen experiments are preserved.

Remaining to-do list: the general smooth gauge bridge, density forward bounds and finite-confidence proofs for S042; then gated S043 and queued S047. S048 remains proposed separately.
