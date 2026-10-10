# Actual curve concatenation and the causal reverse triangle

S042 component, 2026-10-09 (Hawaii). **Full GCP acceptance passes: 919 exact type/axiom reports, including 26 new results, with zero warnings.** S042 remains incomplete and S043 remains gated.

## Construction in the existing curve class

[LorentzConcatenation.lean](../QuantyraNullCone/LorentzConcatenation.lean) extends the [actual proper-time construction](geometric-proper-time-certification.md). For two coordinatewise absolutely continuous future curves `c:p→q` and `d:q→r`, define the joined coordinate by integrating the scalar velocity

    v(t) = 2*c'(2*t)          for t <= 1/2,
           2*d'(2*t - 1)      for t > 1/2.

The proof establishes interval integrability, changes variables on each half interval, and applies the fundamental theorem for absolutely continuous functions. The resulting coordinate equals `c(2*t)` on the first half and `d(2*t-1)` on the second half, including their common joining value. It is absolutely continuous on the full interval and has derivative `v` almost everywhere.

Affine rescaling preserves null sets. This transports the almost-everywhere future-cone constraints to each half interval. Positive homogeneity of the spatial norm then proves the joined curve's future constraint. The coordinate formulas give its endpoints and containment in the original closed Lorentz diamond. Thus `FutureCurve3.concat` belongs to the same curve class used by the existing supremum.

## Length addition and reverse triangle

Flat proper speed obeys `speed(s*v)=|s|*speed(v)`. Combining this homogeneity with the point and velocity formulas, and changing variables in the integrals, gives the exact identity

    L_w(c.concat d) = L_w(c) + L_w(d)

for every continuous positive bounded weight in `InTimeWeightClass3`. The integrals and supremum are the previously defined ones. No existence assumption for maximizing curves is used.

For closed-diamond points `p <= q <= r` in the causal order, straight causal segments ensure that both admissible curve classes are nonempty. Every pair of curves gives a joined curve, so successive supremum bounds yield

    tau_w(p,q) + tau_w(q,r) <= tau_w(p,r).

The proof handles the inserted zero in the supremum by the nonnegative length of a straight segment. It therefore covers null or identical endpoint pieces as well as timelike pieces. The original normalized density weight `(rho/V)^(1/3)` inherits the result through `InDensityClass3.time_reverse_triangle3`.

| Result | Principal endpoint |
| --- | --- |
| Coordinate absolute continuity and the two half-interval formulas | `joined_coord_AC3`, `joined_coord_left3`, `joined_coord_right3` |
| Actual almost-everywhere velocity and future constraint | `joined_velocity3`, `joined_future3` |
| Flat proper-speed homogeneity | `flat_proper_speed_smul3` |
| Exact weighted-length addition | `FutureCurve3.concat_weightedLength` |
| Causal reverse triangle for general weights | `weighted_time_reverse_triangle3` |
| Causal reverse triangle for the original density class | `InDensityClass3.time_reverse_triangle3` |

## Verification and remaining scope

The first two immutable development runs retain their terminal proof errors. The third, `space-join3-dev3-20261010T061740Z-9a6e85`, passes 2,946 jobs and all 26 new standard-axiom reports with zero warnings. Its local SSH process returned a transport failure after printing remote terminal exit zero; the separately collected remote exit file and receipt confirm successful completion. The job was not rerun to repair that observation failure.

The source and development evidence are pushed at `f112c7a83a995fcd66c1606fbfcb1cdced2aa5a7`. The new module is imported by the root, and the full audit appends 26 exact type/axiom checks to the preserved 893-check prefix. The full run `space-join3-acceptance-20261010T061927Z-25e511` passes all 3,104 root jobs and 919 named reports. Its [receipt](../evidence/gcp/space-join3-acceptance-20261010T061927Z-25e511/receipt.json) and [independent delivery verification](../evidence/gcp/space-join3-acceptance-20261010T061927Z-25e511/delivery-verification.json) confirm exact agreement of all 205 captured files, including 171 Lean inputs, with the immutable archive, raw committed blobs and normalized local source. Source and pinned dependency identities are checked before and after execution. The new mathematical module is the only changed mathematical module, and the previous 893 audit statements are retained verbatim. All reported axioms are limited to `propext`, `Classical.choice` and `Quot.sound`. Input archive SHA-256: `ff11cf0ad516e7b8e7d7127ca32d8e05a8b884fb4623fbf68ca36807fbdba097`. All Lean/Lake execution was remote GCP-only. The acceptance SSH process also returned a local transport error after printing terminal exit zero; separately collected remote evidence confirms success.

The [cleanup receipt](../evidence/gcp/space-join3-acceptance-20261010T061927Z-25e511/cleanup.json) verifies ownership from the initially stopped instance, no other Lean work, evidence collection before shutdown and final state `TERMINATED` at `2026-10-10T06:24:52.248704+00:00`.

This component establishes length addition and the causal reverse triangle for the original AC-curve supremum. Joint endpoint continuity still needs a formal proof, including boundary cases. The [ordinary direct endpoint perturbation argument](geometric-diamond-representation.md#direct-ac-endpoint-perturbation-route-ordinary) adjusts each actual AC curve using its time coordinate. It provides a length comparison without changing the curve class; the earlier compactness/reparametrization route remains an alternative. The next formal work is subinterval causal monotonicity, speed superadditivity, the explicit perturbation and its uniform length comparison, then continuity. Quotient topology/full support, the Jacobian/isometry action, coupling-loss properties and finite-observation confidence transport remain separate obligations.

Remaining to-do list: endpoint continuity, quotient/loss and finite-confidence proofs for S042; then gated S043 and queued S047. S048 remains proposed separately.
