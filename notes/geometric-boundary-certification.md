# Lorentz diamond boundary and chronological profiles

S042 component, 2026-10-09 (Hawaii). **Full GCP acceptance passes: 844 exact type/axiom reports, including 35 new boundary endpoints, with zero warnings. S042 remains incomplete and S043 remains gated.** This component proves actual chronological geometry. The weighted proper-time representation and geometric distortion loss still have separate proof obligations.

## Concrete model and results

[LorentzBoundary.lean](../QuantyraNullCone/LorentzBoundary.lean) retains the existing genuine 2+1 coordinates and spatial Euclidean norm. The closed future relation is `spatialRadius3(q-p)<=q_0-p_0`. The open and closed diamonds are exactly the strict/closed intervals between the two tips. No product order on three axes is introduced.

The module proves 35 endpoints, all listed with exact types and dependencies in the root audit. Principal results are:

| Mathematical fact | Formal endpoint |
| --- | --- |
| Closed causal relation is reflexive, transitive and antisymmetric; both strict/closed mixed transitivity rules hold | `causal3_refl`, `causal3_transitive`, `causal3_antisymmetric`, `chronological3_trans_causal3`, `causal3_trans_chronological3` |
| Actual closed causal diamonds are compact and remain inside the open diamond when their endpoints are interior | `isCompact_causalDiamond3`, `open_lorentz_causal_diamond3` |
| An interior predecessor exists exactly when `spatialRadius3(p)-p_0<1`, and a successor exactly when `spatialRadius3(p)+p_0<1` | `interior_past_iff3`, `interior_future_iff3` |
| Interior membership is equivalent to having both an interior chronological predecessor and successor | `lorentz_interior_iff_neighbors3` |
| The waist circle is compact and has no chronological predecessor or successor even in the whole closed diamond | `isCompact_lorentzWaist3`, `lorentz_waist_no_closed_neighbors3` |
| Closed-diamond points have identical incoming/outgoing chronological profiles against all interior points iff they are equal or both belong to the waist circle | `chronological_profile_eq_iff3` |

The separation proof is concrete. A small positive time shift, keeping spatial coordinates fixed, moves a point into its interior past or future whenever the corresponding margin is positive. Nonempty past inclusion forces the closed causal relation; the future version gives the reverse relation. Equal nonempty profiles therefore give equality by antisymmetry. Points with both profiles empty are exactly the waist circle. This proves the chronological equivalence classes without assuming a boundary theorem or importing an external reconstruction axiom.

The compact-diamond result is the model-specific hypothesis needed in the ordinary global-hyperbolicity argument. It is not a formalization of a general globally hyperbolic manifold library. Likewise, the profile result concerns binary chronology, not yet the full weighted time-separation function, the topology of its quotient, or its measure support.

## Cloud evidence

Proof/source commit: `27ca7c4babac503134d685d413d7c5233e930157`, pushed before full acceptance. Run: `space-boundary-acceptance-20261010T052744Z-609276`, on the established GCP instance/project/zone. The manifest captures 202 files, including 168 Lean inputs. Input archive SHA-256: `a0ce860c8ef4668e0bffc28cac5ef106c1270ddf32b323968791cc40e798e57b`. Module SHA-256: `c0b94c912fa02620fc7eb2db84ea2fbc77427abbfd8725697a72b722c62b7e45`. The root audit was expanded from 809 to 844 exact type/axiom reports.

The [accepted receipt](../evidence/gcp/space-boundary-acceptance-20261010T052744Z-609276/receipt.json), raw logs and [delivery verification](../evidence/gcp/space-boundary-acceptance-20261010T052744Z-609276/delivery-verification.json) pass the full 3,099-job root build and all 844 named reports. There are no unfinished proof tokens or added axioms; dependencies are limited to `propext`, `Classical.choice` and `Quot.sound`. Source and pinned dependency identities are verified before and after execution. All captured inputs also match raw committed blobs and normalized local files. The previous 809 audit statements remain verbatim before the additions; no earlier mathematical module is modified.

The initial SSH preflight failed before input submission; the same frozen development input was then submitted successfully. Its terminal Lean failure and raw diagnostics remain in `space-boundary-dev1-20261010T051945Z-89541c`. The corrected, expanded module passed the separate `space-boundary-dev2-20261010T052500Z-88557a` development build with 35 named standard-axiom reports and no warnings. Both development outcomes and their immutable archives are preserved. No local Lean/Lake invocation occurred.

The [cleanup receipt](../evidence/gcp/space-boundary-acceptance-20261010T052744Z-609276/cleanup.json) verifies that the instance was initially stopped, was started for this campaign, and had no other Lean work at cleanup. Acceptance evidence was collected before shutdown. The final state is `TERMINATED`, verified at `2026-10-10T05:33:47.695543+00:00`.

## Next decisive proof

Define actual coordinatewise absolutely continuous future curves on the same closed diamond. Their derivative must satisfy the genuine Lorentz cone inequality almost everywhere. Let `v` be the spatial velocity and `u` the nonnegative time derivative; flat proper speed is `sqrt(u^2-|v|^2)`. The Euclidean vector formed from this proper speed and the two spatial velocities has norm exactly `u`. The Bochner integral norm inequality and coordinatewise fundamental theorem then bound the total flat proper length by the endpoint Lorentz separation. A straight causal segment supplies the converse extremal construction.

This supplies a concrete route to the positive-time/strict-chronology bridge for the actual weighted curve supremum. Positive density bounds then transfer the chronological profile classification to weighted time profiles. Further obligations include continuity up to the boundary, the compact quotient topology and full measure support, the Jacobian/isometry action and a verified coupling bound. These cannot be inferred solely from the 35 boundary endpoints.

The [restricted pair calculation](geometric-pair-conditioning.md) still needs actual geometric integrals, its finite sampling law and confidence transport. Earlier [labeling acceptance](geometric-label-certification.md), the full original class and known conformal-flow obstruction remain preserved.

Remaining to-do list: complete weighted proper time, quotient/loss and finite-observation proofs; resolve S042's gate before S043. S047 remains queued separately.
