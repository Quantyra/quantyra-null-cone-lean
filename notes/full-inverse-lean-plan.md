# Full inverse theorem formalization contracts

2026-10-06, Quantyra Space E002/S013. Dan selected full inverse formalization together with the manuscript deposit and grid optimization. The required end state is the actual all-N coefficient theorem from the concrete density class and iid directed-order laws. An abstract theorem that assumes concentration, reconstruction or interpolation does not satisfy this objective.

## Frozen mathematical interfaces

Use the unit square represented by pairs of real coordinates, with product Lebesgue measure restricted to the square. K consists of a density smooth on a neighborhood of the square, bounded between 1/2 and 3/2 there, Euclidean Lipschitz constant at most two, and both uniform marginals. Smoothness may be retained as an unused hypothesis if the proof works on the larger Lipschitz class, but the exported specialization must include the stated K. Density integration produces a probability measure; iid n-samples use its finite product measure.

The observable is the law of the Boolean chronological relation on `Fin n`, computed by two strict coordinate inequalities. Neither total coordinate order is part of that law. A deterministic finite selector chooses a realizer of an observed order where one exists, with a fixed default elsewhere. The output is the empirical anchored-rectangle mass of normalized ranks. Every selector input/output and law must have a concrete finite/measurable representation.

Population CDF is the density-measure mass of an anchored rectangle. Coefficient discrepancy is the supremum absolute density difference on the square, minimized over identity and transpose. Finite-law TV is the half-sum over the finite observable space (or a proved equivalent event-supremum form), and Delta_N is the maximum over 2<=k<=N. Transpose is the same single axis swap as in the existing finite theorem.

## Required compiled stages

1. **Definitions and measures:** K, transpose, density probability measure, finite iid sample, directed-order law, CDF, coefficient quotient, TV and Delta_N. Prove the constructions' normalization/measurability properties.
2. **Deterministic cumulative bridge:** obtain both marginal and boundary inputs from grid-vertex accuracy; prove inclusive-rank identity, existing finite theorem application, clipped rectangle inclusions and the `87r` conclusion with one global swap.
3. **Uniform probability:** derive null ties/grid lines, cell mass lower bound, occupancy union bound, iid vertex concentration and floor estimates. Prove reconstruction success >=9/10 at `a_n=174n^(-1/4)` for n>=65536.
4. **Density interpolation:** prove the boundary-valid maximizing rectangle and integral inclusion-exclusion, ending in `delta^3<=2048 epsilon` for the concrete densities.
5. **Finite-law separation:** prove transpose isometry, orbit separation and measurable preimages of the same order-only selector; derive the 4/5 TV dichotomy.
6. **Assembly:** export `d_conf<=100(N^(-1/12)+Delta_N)` for every N>=2, including the small-N branch, then all-law identifiability.

Label/unlabel TV equivalence will be reported separately. Proper-time formalization is not included in the selected coefficient theorem's completion gate; its existing prose status must remain explicit. The new logarithmic-grid bound is a separate S014 prose result until its added analytic inequalities are also formalized.

## Verification and scope

Retain Lean 4.30.0 and pinned mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Add exports to the root library and `checks/Audit.lean`, run `lake build QuantyraNullCone` and `checks/check_integrity.py`, and inspect exact theorem types as well as final axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. No admitted proofs, new axioms, fake finite laws, or conclusion-equivalent hypotheses are acceptable.

Keep compilable intermediate results, state which bridges are still incomplete, and preserve the already checked finite theorem. Local tooling is being installed in the user-owned `QuantyraTools/SpaceProofs` directory; tool installations and dependency caches are not proof repository artifacts. Claims of full formal verification follow a requirement-by-requirement audit of the actual exported theorem.

Compiled local progress: F0 concrete definitions, observable measurability and density/sample/order-law probability normalization; F1 inclusive-rank identity, coordinate rigidity, rectangle sandwich and deterministic `87r` consequence with analytic/latent-accuracy premises explicit. The full inverse theorem is not yet exported.

Further compiled progress: `DensityCDF.lean` identifies the concrete measure with density integrals, proves both coordinate marginal measures equal restricted unit-interval volume, derives `|F(s,t)-F(s',t')|<=|s-s'|+|t-t'|` at all real thresholds, and proves `F(s,1)=s` and `F(1,t)=t` on [0,1]. None of those exports assumes the uniform-marginal measure or CDF conclusion.

Next deterministic obligations: bound latent empirical CDF by `3r` from grid-vertex accuracy and derive both `2r` marginal errors. Derive the `20rn` boundary count directly from the sharper `r` vertex error at 4r and 1-4r: merely using the coarser `2r` marginal bound would give 24rn and does not discharge the required constant. Then apply the existing `87r` theorem with the concrete threshold-stability export. Treat null coordinate/grid ties and occupancy/concentration as the separate probability stage.

Remaining to-do list: grid-vertex deductions and concrete deterministic reconstruction; F2 concentration/occupancy/null events; F3 density interpolation; F4 same observable-map separation; F5-F6 full all-N assembly/identifiability and final type/dependency/completion audit.
