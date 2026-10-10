# Quotient sampling and coupling-distortion foundations

S042 component, 2026-10-09 (Hawaii). **Full GCP acceptance passes: 1,041 exact type/axiom reports, including 37 new results, with zero warnings.** S042 remains incomplete and S043 remains gated.

## Exact original experiment

[LorentzQuotientLaws.lean](../QuantyraNullCone/LorentzQuotientLaws.lean) uses finite products of the accepted closed-diamond and quotient probability measures. Coordinatewise inclusion sends the former product to the original ambient sample law. Coordinatewise quotient projection sends it to the quotient iid law. The Boolean order obtained from positive quotient time agrees pointwise, after projection, with the original strict chronology code.

Consequently the full labeled order law on the quotient equals `orderLaw3 rho n`, for every natural sample size including zero. Forgetting labels gives exactly `unlabeledOrderLaw3 rho n`. These are equalities of complete probability measures, with no extra observations, anchors or chosen sample coordinates. This closes the sampling compatibility of the compact representation.

The transport holds for any weight in the existing positive continuous bounded class. With the sampling density fixed, changing that weight does not change the order law. The selected geometric model still ties its weight to the density by `(rho/V)^(1/3)`; this theorem does not change that model constraint. The separate random-label/disjoint-pair confidence construction is still open.

## The selected loss, as an actual infimum

[TimeCouplingLoss.lean](../QuantyraNullCone/TimeCouplingLoss.lean) defines a coupling by its two exact measure marginals. Such a coupling of probability laws is itself a probability law. For two real time-separation functions, the bad-pair event at threshold epsilon is

    |tau_X(x,x') - tau_Y(y,y')| > epsilon.

The functional is the infimum over positive epsilon for which some coupling pi makes this event have probability at most epsilon under `pi tensor pi`. This is the coupling-distortion target selected in the study. The admissible set is nonempty, since epsilon one always works with the product coupling, and is bounded below by zero. The resulting real value lies in `[0,1]`.

Swapping a coupling swaps its marginals and leaves the absolute-discrepancy probability unchanged. This proves symmetry. A measurable measure-preserving map F gives a graph coupling. If every time discrepancy between `(x,x')` and `(F(x),F(x'))` is at most delta, the bad event has zero probability at every threshold above delta. Taking the actual infimum proves loss at most delta. Exact time preservation therefore gives loss zero, and the identity gives zero self-loss. No optimizer is assumed or inserted.

[LorentzDistortion.lean](../QuantyraNullCone/LorentzDistortion.lean) instantiates this functional on the accepted compact profile spaces, actual density measures and actual AC-curve time separations for the original smooth normalized 2+1 class. It proves nonnegativity, the universal upper bound, symmetry, zero self-loss and the corresponding graph-transport bounds there.

The graph-transport theorem is conditional on an actual measure-preserving, time-preserving map. Constructing that map for the specified conformal gauge remains required. The triangle inequality, zero-distance/isomorphy characterization and density-supnorm forward bound also remain open; these elementary properties do not yet certify a metric on gauge classes. In particular a new definition of the loss does not close S042's whole-story loss requirement.

## Verification and remaining work

The new audit has 37 named endpoints: 12 sampling-law results, 19 generic coupling-loss results and six original-class specializations. Development run `space-qloss3-dev4-20261010T073120Z-e4f8ed` passes 2,967 jobs and all 37 named reports. The three earlier terminal development failures remain preserved: sampling elaboration, generic measurable/coupling API details and the final density-model type specialization. The initial read-only preflight retried one transient SSH failure before any build was launched. Proof commit `0dc998b24959239e71a3e2aebd00ab49d6edde4d` was pushed before full acceptance. Run `space-qloss3-acceptance-20261010T073440Z-25dd23` passes 3,113 root jobs and all 1,041 reports. The [receipt](../evidence/gcp/space-qloss3-acceptance-20261010T073440Z-25dd23/receipt.json) and [independent verification](../evidence/gcp/space-qloss3-acceptance-20261010T073440Z-25dd23/delivery-verification.json) confirm all 214 captured files, including 180 Lean inputs, match the immutable archive, committed raw Git blobs and normalized local source. Source and dependency identities are verified before and after execution. All reported axioms are standard; all earlier 1,004 audit statements remain verbatim, and earlier mathematical modules are unchanged. The acceptance controller exits successfully. Input archive SHA-256: `3bef942aed0153826215eca301ee26a96690dbaec74ead6336163f85ce93e56b`. Earlier accepted proof modules, publications and experiments are preserved. No Lean/Lake command runs on the workstation.

The [cleanup receipt](../evidence/gcp/space-qloss3-acceptance-20261010T073440Z-25dd23/cleanup.json) verifies original task ownership, no other Lean work, evidence collection before shutdown and final instance state `TERMINATED` at `2026-10-10T07:40:35.531685+00:00`.

The next generic loss route is to glue two couplings over their common middle marginal using a conditional kernel and `Measure.compProd`. On two independent draws from that glued law, the absolute-value triangle and a union bound should give admissibility at the sum of the two thresholds. For zero-loss attainment, the compact space of probability measures on the compact profile product provides a candidate limit route, with marginal preservation and distortion-event limits still to prove. Mathlib's `Measure.condKernel`, `Measure.fst_compProd` and compactness instance for `ProbabilityMeasure` are available source APIs, not completed proofs of these remaining steps. Actual conformal curve-length transport and the density-specific common-part/residual coupling remain separate requirements.

Remaining to-do list: gauge/length-isometry transport, triangle and zero-isomorphy properties, density forward bound, restricted pair-law and finite-confidence proofs for S042; then gated S043 and queued S047. S048 remains proposed separately.
