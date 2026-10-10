# Zero distortion, compact time isomorphy and original order laws

Subsequent progress: [actual conformal-flow curve/time transport and zero geometric distortion for the accepted gauge pair](geometric-flow-transport-certification.md) now have 1,107-report GCP acceptance. The historical zero-isomorphy acceptance below remains preserved.

S042 component, 2026-10-09 (Hawaii). **Full GCP acceptance passes: 1,078 exact type/axiom reports, including 24 new results, with zero warnings.** S042 remains incomplete and S043 remains gated.

## Attainment and isomorphy

[TimeZeroCoupling.lean](../QuantyraNullCone/TimeZeroCoupling.lean) defines an actual coupling whose two independent draws preserve time separation almost everywhere. Such a coupling gives zero for the existing distortion infimum. Conversely, [TimeCouplingLimit.lean](../QuantyraNullCone/TimeCouplingLimit.lean) proves that weak limits preserve both coupling marginals. Probability products converge continuously, and every positive discrepancy event is open when the two time functions are continuous. The portmanteau inequality therefore makes its limiting mass zero when the admissible thresholds tend to zero. Countably many positive thresholds give exact almost-everywhere time equality.

[TimeZeroAttainment.lean](../QuantyraNullCone/TimeZeroAttainment.lean) selects admissible thresholds below `1/(n+1)` from a zero infimum. Compactness and metrizability of probability laws on the compact product give a convergent subsequence. The preceding limit lemmas yield a genuine zero coupling. This proves both directions of the zero-loss/zero-coupling characterization without assuming an optimizer.

[TimeCouplingSupport.lean](../QuantyraNullCone/TimeCouplingSupport.lean) upgrades almost-everywhere preservation to preservation on every pair of support points. Closedness and full marginal support make both coordinate projections of the support surjective. Point-distinguishing incoming and outgoing time profiles make both projections injective. [TimeZeroIsomorphy.lean](../QuantyraNullCone/TimeZeroIsomorphy.lean) turns these continuous bijections from a compact space into homeomorphisms and proves exact probability-measure transport. Thus, for compact full-support time spaces with continuous, point-distinguishing profiles,

    zero distortion iff a measure-preserving, time-preserving homeomorphism exists.

[LorentzDistortionZero.lean](../QuantyraNullCone/LorentzDistortionZero.lean) and [LorentzDistortionIsomorphy.lean](../QuantyraNullCone/LorentzDistortionIsomorphy.lean) instantiate both characterizations on the actual quotient spaces, density measures and AC-curve time functions of the original normalized 2+1 class. Together with the accepted triangle, symmetry and bounds, the result supplies the metric properties on compact measured time-isomorphism classes.

## Original finite experiment and scope boundary

[LorentzZeroOrderLaws.lean](../QuantyraNullCone/LorentzZeroOrderLaws.lean) transports the finite iid sample measure coordinatewise under a measure-preserving time map. Positivity of time, and hence the entire directed order code, is preserved. The earlier exact quotient/original sampling bridge then gives equality of the original labeled and unlabeled order laws for every sample size, including zero, whenever geometric distortion is zero.

The intended S042 equivalence is a future-preserving smooth metric isometry of the open spacetimes. The certified compact time-space homeomorphism is one part of that bridge. Its smooth interpretation still uses the explicit external journal reconstruction dependency and the model-specific hypotheses described in [the representation study](geometric-diamond-representation.md). The new all-law equality supplies the corresponding finite-law premise; it does not formalize Braun's theorem or introduce it as an axiom. Actual conformal AC-curve length/time transport and zero loss for the accepted flow pair remain open. No finite inverse modulus or confidence result follows from this component alone.

## Verification and custody

The 24 new endpoints cover four zero-coupling facts, five weak-limit facts, two attainment facts, six support facts, two generic isomorphy facts, two original-class characterizations and three finite-law consequences. Run `space-zero3-dev1-20261010T080904Z-fef5cf` fails on missing product-topology assumptions; run `space-zero3-dev2-20261010T081545Z-d458a5` verifies attainment but fails on support API details and retains one linter warning. These failures remain preserved. Run `space-zero3-dev3-20261010T081834Z-d98aae` passes the 21-result isomorphy chain, and `space-zero3-dev4-20261010T082227Z-23c984` passes all 24 new results and 3,003 jobs with zero warnings.

Proof commit `d1b97ea937206641e84faa735155a8baf3cff215` is pushed before full acceptance. Run `space-zero3-acceptance-20261010T082610Z-4ccaba` passes 3,152 root jobs and all 1,078 reports. The [receipt](../evidence/gcp/space-zero3-acceptance-20261010T082610Z-4ccaba/receipt.json) and [independent verification](../evidence/gcp/space-zero3-acceptance-20261010T082610Z-4ccaba/delivery-verification.json) check all 225 captured files, including 191 Lean inputs, against immutable archives, committed raw Git blobs and normalized local source. Source and dependency identities are verified before and after execution. All axioms are standard; all 1,054 earlier audit statements remain verbatim and all earlier mathematical modules are unchanged. The full acceptance controller exits successfully. Archive SHA-256: `a8f5ad47d141941291dfcb2b211ddd92779d4ff12b37bd89aa3e3de5024fef83`.

When the existing root disk fell below the preflight threshold, two bounded cleanups verified every source file against its retained immutable archive before unlinking redundant extracted source files from 20 completed development runs in this workstream. The [first](../evidence/gcp/space-zero3-dev1-20261010T080904Z-fef5cf/read-081506.stdout.txt) and [second](../evidence/gcp/space-zero3-dev3-20261010T081834Z-d98aae/read-082146.stdout.txt) receipts record exact run identities, file counts and archive hashes. All input archives, manifests, logs, receipts, shared dependencies and caches remain preserved. No acceptance source extraction was removed.

The [cleanup receipt](../evidence/gcp/space-zero3-acceptance-20261010T082610Z-4ccaba/cleanup.json) verifies task ownership, no other Lean work, evidence collection before shutdown and final state `TERMINATED` at `2026-10-10T08:33:57.808729+00:00`. All Lean/Lake execution is on GCP. Earlier publications and frozen experiments are preserved.

## Next proof sequence

1. Complete the smooth gauge bridge with its external dependencies explicit. Prove actual AC-curve composition, proper-length preservation and time-supremum transport for the accepted conformal flow, then induce the quotient transport and certify zero distortion for that pair.
2. Prove the density forward estimate using the common-density part and a residual product coupling. Combine it with the existing weight dependence of time separation.
3. Certify the restricted pair integrals and conditioning, then random-label/disjoint-pair independence and confidence transport. Resolve S042 and the S043 quantitative gate from the resulting evidence.

Remaining to-do list: smooth gauge/curve transport, density forward bounds and finite-confidence proofs for S042; then gated S043 and queued S047. S048 remains proposed separately.
