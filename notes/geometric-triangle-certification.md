# Coupling gluing and the distortion triangle

S042 component, 2026-10-09 (Hawaii). **Full GCP acceptance passes: 1,054 exact type/axiom reports, including 13 new results, with zero warnings.** S042 remains incomplete and S043 remains gated.

## Mathematical result

[TimeCouplingGluing.lean](../QuantyraNullCone/TimeCouplingGluing.lean) constructs a joint law on `((X x Y) x Z)` from two probability couplings with the same middle marginal. It disintegrates the second coupling, pulls its conditional kernel back along the first coupling's Y coordinate, and takes their composition product. Both adjacent marginal identities are proved as equalities of complete measures. Projection to X and Z is therefore an actual coupling of the endpoint laws. The generic construction requires Z to be standard Borel; nonemptiness follows from its probability law.

[TimeDistortionTriangle.lean](../QuantyraNullCone/TimeDistortionTriangle.lean) takes two independent draws of this joint law. If the endpoint time discrepancy exceeds epsilon plus eta, one adjacent discrepancy must exceed its own threshold. Exact product/map identities and the union bound give bad-pair probability at most epsilon plus eta. Thus admissible thresholds compose additively.

The final infimum argument chooses admissible thresholds arbitrarily close to each existing infimum. It proves the triangle inequality for the previously selected `timeDistortionLoss`, without assuming an optimizing coupling. The definition, threshold convention, original experiment and earlier proofs are preserved.

[LorentzDistortionTriangle.lean](../QuantyraNullCone/LorentzDistortionTriangle.lean) specializes the result to the original smooth normalized 2+1 density class, its compact time-profile spaces, density laws and actual AC-curve time separations. It also proves the reverse bound

    |d_G(rho,omega) - d_G(sigma,omega)| <= d_G(rho,sigma).

Together with the previously accepted nonnegativity, symmetry and zero self-loss, this establishes the pseudometric inequalities on the original class. The zero-distance/isomorphy converse and actual conformal gauge transport remain separate proof obligations. The whole-story loss requirement is therefore still open; no S043 go decision follows from this component.

## Verification

The component adds six gluing results, five generic discrepancy/triangle results and two original-class results. Development run `space-glue3-dev1-20261010T074847Z-785695` passes the six gluing endpoints. Its initial read-only preflight retries one transient SSH failure before any build begins. Run `space-glue3-dev2-20261010T075259Z-cb0e20` compiles all 13 results but has two linter warnings, preserved in its logs. Replacing the deprecated tactic and omitting unused section assumptions gives clean development run `space-glue3-dev3-20261010T075558Z-cfd099`: 2,970 jobs, all 13 new reports, zero warnings and standard axioms only. The warnings are corrected without disabling linters or changing the mathematical assertions.

Proof commit `8ddb78190e979635a2213c26b3f7a88fea9b5a81` is pushed before full acceptance. Run `space-glue3-acceptance-20261010T075902Z-42255f` passes 3,116 root build jobs and all 1,054 reports. The [receipt](../evidence/gcp/space-glue3-acceptance-20261010T075902Z-42255f/receipt.json) and [independent verification](../evidence/gcp/space-glue3-acceptance-20261010T075902Z-42255f/delivery-verification.json) verify all 217 captured files, including 183 Lean inputs, against the immutable archive, raw committed Git blobs and normalized local files. Source and dependency identities are verified before and after execution. The previous 1,041 audit statements remain verbatim and all earlier mathematical modules are unchanged. Every reported axiom is standard, and the full acceptance controller exits successfully. Archive SHA-256: `32c09f3c29cb8e0b5a3c3ff76e930364bb96651d93ca1c005425568cd7d62c8d`.

The [cleanup receipt](../evidence/gcp/space-glue3-acceptance-20261010T075902Z-42255f/cleanup.json) confirms original task ownership, no other Lean work, evidence collection before shutdown and final state `TERMINATED` at `2026-10-10T08:03:59.033564+00:00`. All Lean/Lake execution is on GCP. Previous publications, experiments and accepted proof evidence remain preserved.

## Next proof sequence

1. Prove zero-loss attainment using compact probability measures on the compact profile product. Continuous pushforward preserves the limiting marginals; continuous probability products and the open-set portmanteau inequality should force every positive discrepancy threshold to have zero limiting mass. Relevant source APIs are `ProbabilityMeasure.continuous_map`, `ProbabilityMeasure.continuous_prod`, `ProbabilityMeasure.le_liminf_measure_open_of_tendsto`, and the compactness and metrizability instances in `Prokhorov.lean` and `LevyProkhorovMetric.lean`. These are available ingredients, not an accepted attainment proof.
2. Prove the zero-coupling support relation projects onto both full-support spaces. Continuity and the accepted point-distinguishing time profiles should turn this relation into a measure-preserving time isomorphism; the support and graph arguments remain to be formalized.
3. Complete actual conformal curve-length/time transport, the density common-part/residual coupling forward bound, restricted pair integrals and finite-confidence transport. Resolve S042 and the S043 quantitative gate from those results.

Remaining to-do list: zero-isomorphy, actual conformal transport, density forward bounds and finite-confidence proofs for S042; then gated S043 and queued S047. S048 remains proposed separately.
