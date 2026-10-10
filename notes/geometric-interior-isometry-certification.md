# Interior isometries and the geometric gauge

S042 component, 2026-10-10 (Hawaii). **Full GCP acceptance passes: 1,165 exact type/axiom reports, including 34 new results, with zero warnings.** A time-oriented C1 isometry with C1 inverse on the open diamond has zero actual geometric distortion. Its sampling-measure transport and time-separation preservation are derived from the metric identity. The converse smooth reconstruction remains an explicit external theorem.

## General forward result

The original normalized smooth density class and geometric loss are retained. `InteriorDensityIsometry3 rho sigma F G DF DG` specifies inverse maps on the open diamond, C1 regularity there, their actual Frechet derivatives, preservation of the future cone in both directions, and one forward metric pullback identity. No volume law or time-separation equality is an input. The contract does not require a continuous or differentiable extension to the closed boundary. Smooth time-oriented isometries satisfy this C1 contract.

The main theorem proves `geometricDistortion3 hR hS = 0`. The accepted compact zero-isomorphy theorem also supplies a measure-preserving time homeomorphism of the compact profile quotients. The new contract is instantiated by the original nontrivial conformal-flow gauge pair, and its zero loss is recovered through this general route. The earlier counterexample and its positive coordinate distance remain preserved.

## Proof chain

[LorentzInteriorCurveMap.lean](../QuantyraNullCone/LorentzInteriorCurveMap.lean) proves convexity of each causal diamond and places every actual future AC curve with interior endpoints inside that compact set. A C1 map is Lipschitz on that compact convex set. Composition, the almost-everywhere chain rule, future-cone preservation and the proper-speed metric identity then transport the original curve class and its lengths. This proves one-sided time transport using only interior hypotheses.

[LorentzMetricJacobian.lean](../QuantyraNullCone/LorentzMetricJacobian.lean) derives the volume factor from the bilinear metric identity. In Cartesian coordinates the Lorentz Gram matrix has determinant minus one. Taking determinants of the weighted pullback matrix gives `b^3 * abs(det L) = a^3` for the nonnegative proper-speed weights. Their accepted cube identity yields `sigma(F p) * abs(det DF(p)) = rho(p)`.

[LorentzInteriorIsometry.lean](../QuantyraNullCone/LorentzInteriorIsometry.lean) derives the inverse differential identity by differentiating the local inverse equation. It consequently derives inverse metric preservation from the one assumed forward identity. Applying the curve argument in both directions proves equality of the actual weighted time separations for all interior endpoint pairs. It also specializes the derived Jacobian relation to the original density class.

[LorentzInteriorMeasure.lean](../QuantyraNullCone/LorentzInteriorMeasure.lean) completes the open map measurably by assigning zero outside the open diamond. The completion agrees locally with the isometry at every interior point. Change of variables on each measurable preimage, with the derived Jacobian relation, proves transport of the actual normalized density laws. Both the original and closed-diamond laws give full mass to the open diamond, so the arbitrary completion has no statistical effect.

[LorentzInteriorDistortion.lean](../QuantyraNullCone/LorentzInteriorDistortion.lean) maps the original measure into pairs of profile projections. Its marginals are the actual quotient laws. The product coupling preserves time almost everywhere because both sampled endpoints are interior almost surely. This constructs an actual zero-distortion coupling, and the accepted compact characterization supplies the quotient time homeomorphism. The last three endpoints verify the explicit conformal-flow specialization.

## Smooth equivalence and the external converse

Combining the accepted forward result, the earlier [zero-loss all-law theorem](geometric-zero-isomorphy-certification.md), and the external reconstruction theorem establishes the intended interpretation on the original smooth class:

    zero geometric distortion <=> time-oriented smooth isometry of (D,g_rho) and (D,g_sigma).

This displayed equivalence has an **external ordinary-mathematics dependency** in its reverse reconstruction step. It is not a newly Lean-certified equivalence to smooth manifolds. The formal forward theorem, compact metric properties and zero-loss equality of every finite order law are certified. Braun's reconstruction theorem is not introduced into Lean as an axiom, and neither it nor all its cited dependencies are independently formalized here.

The [journal theorem 1.4](https://doi.org/10.1088/1361-6382/ae456c), page 3, suffices for the original smooth class. Its full reconstruction assembly is in sections 3.1–3.4. The retained 15-page PDF was rechecked against SHA-256 `5477a946875959d9390fbdc5e500ffa195336d0020a84c2f784d5ddbbd32c762`; the theorem, conventions and relevant assembly were re-inspected for this bridge. The model-specific hypotheses are as follows.

- `D` is a connected open subset of R3, hence a Hausdorff, second-countable smooth manifold without boundary. The normalized positive smooth coefficients give smooth Lorentzian metrics and the increasing-time orientation. The source uses the opposite overall metric-sign convention; reversing that convention changes neither chronology nor volume nor isometry.
- Positivity of the coefficient leaves the flat causal cones unchanged. The time coordinate rules out causal cycles. The closed causal diamond between interior endpoints is compact and contained in `D`, as already formally proved. These facts verify global hyperbolicity under the source's definition 2.9.
- The metric volume density is `sqrt(abs(det g_rho)) = rho/V`, so its total volume is one and its normalized volume law is exactly the existing sampling law. This standard coordinate volume identification and the manifold interpretation are ordinary model checks; the new derivative/change-of-variables transport is formally certified.
- The source's labeled chronological adjacency laws agree with the original strict directed order laws. Zero distortion gives equality at every sample size by the prior accepted theorem. The accepted exchangeability/labeling bridge also permits starting from equality of all unlabeled laws. This argument uses equality of each finite law, without an infinite random permutation.

For the compact continuous-density superclass, the separate weighted journal theorem 1.5 and remark 1.6 remain the relevant ordinary route on the smooth flat base with continuous potentials `log rho`. The present formal class is the original smooth class; it does not certify the continuous-class compactness argument or any explicit inverse modulus.

The S042 density-action/loss-properties requirement can therefore close with this external dependency recorded. Restricted inverse conditioning and finite-confidence reconstruction remain unresolved, and S043 remains gated.

## Verification and custody

The 34 new endpoints comprise 11 interior curve facts, three metric/determinant facts, five inverse/time/Jacobian facts, nine completion/measure facts and six coupling/specialization facts. The first development run passes the 11 interior-curve endpoints. The 3 failed combined development runs retain their immutable inputs and diagnostics. `space-open3-dev5-20261010T103623Z-3c4b89` passes all 34 new reports and 3,016 jobs with zero warnings.

Proof commit `b5aa9aed937a1dca8fbcf0c7928e9dc4061f1c02` is pushed before full acceptance. Run `space-open3-acceptance-20261010T104116Z-16cc4f` passes 3,166 root jobs and all 1,165 reports. [Independent verification](../evidence/gcp/space-open3-acceptance-20261010T104116Z-16cc4f/delivery-verification.json) matches all 239 captured files, including 205 Lean inputs, to their immutable archive, raw committed Git blobs and normalized local sources. Source and pinned dependency identities are verified before and after execution. All reported axioms are standard; all 1,131 preceding audit statements and earlier mathematical modules remain unchanged. Archive SHA-256: `95da42f3b55226bff00dc971ac58d384f12967f06612f931715acce01cbf0bd2`.

The first post-startup SSH preflight connection closed before source submission; the controller retained the failure and passed a subsequent preflight before uploading the same immutable capture. A [bounded cleanup](../evidence/gcp/space-open3-dev1-20261010T101428Z-2daefc/read-102034.stdout.txt) verifies local/remote archives and every source hash in four terminal density development runs before removing 5,982,305 redundant extracted source bytes. Its [exact script](../evidence/gcp/space-open3-dev1-20261010T101428Z-2daefc/archive-verified-density-source-cleanup.sh) and receipts are retained. All immutable archives, manifests, logs, shared dependencies, shared caches and acceptance extractions are preserved. Collected current development runs also record cleanup of their own ephemeral build caches.

The fifth development run's launch SSH connection closed after submission. The retained [observation](../evidence/gcp/space-open3-dev5-20261010T103623Z-3c4b89/observation-103836.stdout.txt) found that exact remote run still compiling; it was observed and collected without resubmission. Its compiler outcome is taken from the remote terminal receipt and complete logs, separately from the failed SSH process. The full acceptance preflight also retained an SSH-process failure before submission, followed by a [successful retry](../evidence/gcp/space-open3-acceptance-20261010T104116Z-16cc4f/preflight-104149.stdout.txt) before the immutable inputs were uploaded.

A second [bounded cleanup receipt](../evidence/gcp/space-open3-dev4-20261010T103115Z-1f5d77/read-103556.stdout.txt) records the same archive/member/source verification for the first four collected interior development runs, removing 6,104,056 redundant extracted source bytes. Its [exact script](../evidence/gcp/space-open3-dev4-20261010T103115Z-1f5d77/archive-verified-open3-source-cleanup.sh) preserves the same evidence and dependency boundaries.

[Shutdown](../evidence/gcp/space-open3-acceptance-20261010T104116Z-16cc4f/cleanup.json) verifies task ownership, no other Lean work, evidence collection before stopping, and `TERMINATED` at `2026-10-10T10:47:51.989988+00:00`. Every Lean/Lake invocation was on GCP. Existing publications and frozen experiments remain preserved.

Remaining to-do list: certify restricted-family membership and pair integrals, inverse conditioning and finite-confidence transport for S042; then resolve gated S043 and proceed to queued S047. S048 remains proposed separately.
