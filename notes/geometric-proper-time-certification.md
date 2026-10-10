# Actual 2+1 proper time and weighted boundary profiles

S042 component, 2026-10-09 (Hawaii). **Full GCP acceptance passes: 893 exact type/axiom reports, including 49 new curve and weighted-time results, with zero warnings.** S042 is incomplete and S043 remains gated.

## Definitions and proof scope

[LorentzProperTime.lean](../QuantyraNullCone/LorentzProperTime.lean) defines actual coordinatewise absolutely continuous curves on `[0,1]`, with their endpoints, containment in the original closed diamond, and a future Lorentz-cone constraint on the derivative almost everywhere. Endpoint causality and length bounds are conclusions. There is no assumed length bound or replacement by a coordinatewise product order.

Let `u` be the time derivative and `v` the two spatial derivatives. Flat proper speed is `sqrt(u^2-|v|^2)`. The Euclidean vector `(flat proper speed,v)` has norm `u` on the future cone. Integrating that vector, using coordinatewise absolute continuity and the fundamental theorem, gives

    L_flat^2 + |q_x-p_x|^2 <= (q_t-p_t)^2.

Every admissible curve therefore has causally related endpoints and flat length at most the endpoint Lorentz separation. The straight causal segment is a member of the same curve class and attains equality. This proves the exact flat supremum formula, the empty-class zero result and strict positivity exactly on chronology. The closed-diamond length bound is two.

[LorentzWeightedTime.lean](../QuantyraNullCone/LorentzWeightedTime.lean) defines weighted lengths by the actual integral and time separation by their supremum with zero included. The general weight class consists of continuous weights on the same closed diamond with explicit positive lower and finite upper bounds. It is used to prove a result applicable to the original density class; the original class is retained.

| Conclusion | Principal formal endpoint |
| --- | --- |
| Actual AC flat length is bounded by endpoint separation; the straight segment attains it | `FutureCurve3.flatLength_le_endpoint`, `straight_curve_flatLength3`, `flat_time_separation_eq3` |
| Weighted integrands are integrable and `lo*tau_flat <= tau_w <= hi*tau_flat` | `FutureCurve3.integrable_weightedSpeed`, `weighted_time_separation_bounds3` |
| Weighted time is positive exactly on strict chronology, and zero otherwise | `weighted_time_separation_pos_iff3`, `weighted_time_separation_zero_iff3` |
| Numerical incoming/outgoing profiles against **all closed-diamond points** agree iff the points coincide or both belong to the waist circle | `weighted_time_profile_eq_iff3` |
| The original density class gives the positive continuous weight `(rho/V)^(1/3)` with explicit bounds | `InDensityClass3.timeWeight` |
| The integrand is exactly `sqrt(-g_rho(velocity,velocity))` for the existing normalized density metric | `density_metric_proper_speed3`, `FutureCurve3.weightedLength_eq_metric` |
| `sup_C |w-v|<=delta` implies `sup_(p,q) |tau_w-tau_v|<=2*delta` | `weighted_time_separation_difference3` |

The profile proof uses the previously accepted chronological classification for its forward direction. For the reverse direction, every waist point has zero time separation to and from all closed-diamond points. The explicit original-class corollaries preserve the genuine spatial norm, original normalization and known conformal-flow obstruction.

## Acceptance and custody

The fifth development run, `space-curve3-dev5-20261010T055203Z-d33534`, passes 2,945 jobs, all 49 new named reports and zero warnings. The initial SSH preflight failure and four terminal development failures are retained. The root audit includes 29 new flat-curve and 20 new weighted-time results, for a total of 893.

The first full attempt, `space-curve3-acceptance-20261010T055422Z-5d3081`, failed because the new import followed the root module documentation command. Its immutable source and terminal failure are preserved. Commit `ee649c57d0765bb3ed4380c6f4a6054c0b61bdc4` moves that import into the import block, without changing either mathematical module. The corrected source is pushed before the new acceptance run. The corrected full acceptance run is `space-curve3-acceptance-20261010T055732Z-52f68b`. Its [receipt](../evidence/gcp/space-curve3-acceptance-20261010T055732Z-52f68b/receipt.json) and [independent delivery verification](../evidence/gcp/space-curve3-acceptance-20261010T055732Z-52f68b/delivery-verification.json) pass all 3,103 root jobs and 893 named reports. The 204 captured files, including 170 Lean inputs, match the immutable archive, raw committed blobs and normalized local files. Source and pinned dependency identities are checked before and after execution; all reported theorem axioms are limited to `propext`, `Classical.choice` and `Quot.sound`. The previous 844 audit statements remain verbatim and all earlier mathematical modules are unchanged. Input archive SHA-256: `83db37f775d9a9218db45b37785ade7f76b0a26d210e955c02e309e02d1ec026`. All Lean/Lake execution was remote GCP-only.

The [cleanup receipt](../evidence/gcp/space-curve3-acceptance-20261010T055732Z-52f68b/cleanup.json) verifies original task ownership, no other Lean work, collection before shutdown and final instance state `TERMINATED` at `2026-10-10T06:02:58.908724+00:00`. The original stopped instance was started by this campaign and is now stopped again.

## Remaining representation obligations

Uniform dependence on the weight is proved separately from continuity in the two endpoints. The latter still needs its own proof, including at the boundary. No time-separation quotient topology, full measure support or coupling-distortion metric theorem follows merely from the profile classification.

Subsequent [GCP acceptance of concatenation and reverse triangle](geometric-concatenation-certification.md) closes those two formal obligations for this same AC supremum. The [ordinary representation argument](geometric-diamond-representation.md#direct-ac-endpoint-perturbation-route-ordinary) now supplies a direct AC endpoint perturbation route to continuity. Its formalization remains open. The earlier compactness route is retained; using that alternative would require the reparametrization bridge.

Subsequent obligations are the quotient topology/support, isometry/Jacobian action and coupling loss, then the actual restricted pair-law integrals and randomized-label confidence construction. The current weight-difference estimate does not itself give the density-specific coupling bound or an inverse from finite order data.

Remaining to-do list: prove endpoint continuity, quotient/loss and finite-observation results; resolve S042 before S043. S047 remains queued separately.
