# Density forward stability for the actual geometric loss

S042 component, 2026-10-10 (Hawaii). **Full GCP acceptance passes: 1,131 exact type/axiom reports, including 24 new results, with zero warnings.** The original normalized 2+1 class now satisfies the forward bound with constant one. S042 remains active and S043 remains gated.

## Result

For any two densities in the original smooth class, if `abs(rho(p)-sigma(p)) <= delta` on the closed diamond and `delta >= 0`, then

    geometricDistortion3(rho,sigma) <= delta.

Thus `d_G(rho,sigma) <= supnorm_C(rho-sigma)`. This is the actual coupling-distortion infimum on the accepted compact time-profile quotients. It uses the existing normalized sampling measures and weighted AC-curve time separations. There is no replacement loss or additional observation.

Changing both inputs by uniform errors `delta` and `eta` changes their geometric distortion by at most `delta+eta`. Equality of the densities on the closed diamond implies zero loss even if their values elsewhere differ. These statements provide forward stability; they give no inverse bound from one finite observed order.

## Proof chain

[CommonMeasureCoupling.lean](../QuantyraNullCone/CommonMeasureCoupling.lean) constructs a coupling from a common submeasure `omega <= mu,nu`. It puts `omega` on the diagonal and couples the residual measures by their normalized product. Both marginals, equal residual masses and finiteness are proved, including the case of zero residual mass. It also proves marginal transport under two measurable maps.

[TimeCommonCoupling.lean](../QuantyraNullCone/TimeCommonCoupling.lean) proves that the diagonal-diagonal part gives no bad time pairs once the threshold dominates the uniform time discrepancy. Expanding the product coupling leaves two terms whose total mass is at most twice the residual mass. Transporting the coupling through the two profile projections and approaching the desired threshold from above bounds the existing infimum, including error zero.

[LorentzDensityWeight.lean](../QuantyraNullCone/LorentzDensityWeight.lean) proves `2 < V < 9/4`, the exact cube identity `w_rho^3=rho/V`, and the rational lower bound `w_rho >= 3/5`. Factoring the difference of cubes yields `2*abs(w_rho-w_sigma) <= abs(rho-sigma)`. The accepted curve-length estimate then gives a uniform time-separation error at most `delta`. This sufficient rational weight estimate proves the same final constant-one bound as the ordinary derivative argument; no optimality of that constant is asserted.

[LorentzCommonDensity.lean](../QuantyraNullCone/LorentzCommonDensity.lean) uses the actual closed-diamond measure with density `min(rho,sigma)`. It proves domination by both original laws and identifies its mass with the integral of the minimum. Normalization and the uniform density error give missing mass at most `delta/2`.

[LorentzDensityForward.lean](../QuantyraNullCone/LorentzDensityForward.lean) combines these results through the actual quotient projections. Twice the missing mass is at most `delta`, as is the diagonal time discrepancy. The accepted reverse triangle gives the joint perturbation estimate.

## Verification and delivery

The 24 endpoints comprise seven common-coupling facts, three generic time-distortion facts, five weight/time estimates, six original common-density facts and three geometric consequences. The 3 failed development runs retain their immutable inputs and diagnostics. `space-density3-dev4-20261010T095808Z-10e2f9` passes all 24 new reports and 2,976 jobs with zero warnings.

Proof commit `c4b434227aa879f233e0956a6e2f5d0172818e1e` is pushed before full acceptance. Run `space-density3-acceptance-20261010T100216Z-d92ca4` passes 3,161 root jobs and all 1,131 reports. The [receipt](../evidence/gcp/space-density3-acceptance-20261010T100216Z-d92ca4/receipt.json) and [independent verification](../evidence/gcp/space-density3-acceptance-20261010T100216Z-d92ca4/delivery-verification.json) compare all 234 captured files, including 200 Lean inputs, with the immutable archive, raw committed Git blobs and normalized local sources. Source and pinned dependency identities are checked before and after execution. All reported axioms are standard. All 1,107 previous audit statements remain verbatim and all earlier mathematical modules are unchanged. Archive SHA-256: `1a3169b91c02b0b7d9d7f9651c58d2d1ff7e27a92badf432057945e09fdb4b41`.

The first SSH connection after instance startup closed before any development build was submitted. A separate observation confirmed no active Lean work and all 229 prior development-source files intact. The bounded cleanup then verified every archived source hash before deleting that redundant extraction. The same immutable first input capture was submitted after recovery. Its failure and subsequent development diagnostics remain retained.

Two storage cleanups preserve the immutable archives, manifests, logs, receipts, shared dependencies, shared caches and acceptance extractions. The [first](../evidence/gcp/space-density3-dev1-20261010T093644Z-5882c8/read-094011.stdout.txt) removes the verified redundant extraction of the preceding successful flow development run. The [second](../evidence/gcp/space-density3-dev1-20261010T093644Z-5882c8/read-094454.stdout.txt) validates local/remote archive hashes and every extracted source in 20 terminal development runs before removing 24,337,034 source bytes. Its exact [script](../evidence/gcp/space-density3-dev1-20261010T093644Z-5882c8/archive-verified-source-cleanup.sh) is retained. Each collected current development run also records cleanup of its own ephemeral build cache.

The [cleanup receipt](../evidence/gcp/space-density3-acceptance-20261010T100216Z-d92ca4/cleanup.json) confirms task ownership, no other Lean work, evidence collection before shutdown and `TERMINATED` at `2026-10-10T10:08:57.451991+00:00`. All Lean/Lake execution is on GCP. Earlier publications, experiments and accepted mathematical modules remain preserved.

## Remaining scope

The smooth open-spacetime equivalence still requires its general bridge with the journal reconstruction dependency explicit. Restricted-family membership, pair integrals, inverse conditioning, random-label/disjoint-pair independence and finite confidence remain separate obligations. The bound here does not establish physical applicability or complete the broader roadmap.

Remaining to-do list: the general smooth gauge bridge, restricted conditioning and finite-confidence proofs for S042; then gated S043 and queued S047. S048 remains proposed separately.
