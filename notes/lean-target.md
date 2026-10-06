# Finite realizer rank rigidity Lean target

2026-10-06, E002/S005. Selected substantive target: the deterministic finite rank-reconstruction theorem underlying `finite-order-rate.md`. It replaces the earlier tentative full continuum automorphism target because it directly carries the quantitative proof. The complete target now compiles as `finite_realizer_rank_rigidity_specified` in `QuantyraNullCone/Bridges.lean`, with a stronger general theorem alongside it.

Environment pinned: Lean v4.30.0 and mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` (verified remote tag v4.30.0). The final root-library build and explicit theorem-type audit both exit zero. `notes/lean-verification.md` records all component and final statements. Both final theorems report only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or added axioms.

## Exact mathematical statement

Let n>=1, m>=16, r=1/m, and let (u_i,v_i), i in Fin n, lie in (0,1)^2. Assume all u coordinates are distinct, all v coordinates are distinct, and no coordinate is a multiple of r. Assume every open grid cell (j*r,(j+1)*r) times (k*r,(k+1)*r), j,k in Fin m, contains at least one event.

Define P(i,j) iff u_i<u_j and v_i<v_j. Let L_1,L_2 be arbitrary strict total orders on Fin n satisfying P(i,j) iff L_1(i,j) and L_2(i,j).

Assume each empirical marginal cumulative function is within 2r of the uniform cumulative function at every threshold in [0,1]. Also assume the fraction of vertices outside [4r,1-4r]^2 is at most 20r.

For a strict order L define rank_L(i)=1+card {j : L(j,i)}. Define rank_u and rank_v by the corresponding coordinate comparisons. Then there exists a Boolean swap, chosen ONCE for the entire sample, such that for EVERY interior event i,

`abs(rank_(aligned L_1)(i) - rank_u(i)) <= 30*r*n`,

`abs(rank_(aligned L_2)(i) - rank_v(i)) <= 30*r*n`,

where subtraction, absolute value, and the right side are interpreted in the real numbers by explicit natural-to-real coercions. aligned orders are (L_1,L_2) or (L_2,L_1) according to swap.

This statement includes all realizers, missing coordinate orderings, one global residual swap, and rank counts. The marginal and boundary hypotheses are deterministic inputs proved separately by concentration in the main argument. They must not be replaced by the conclusion itself or by a latent-realizer uniqueness assumption.

## Proof components and completion criterion

1. Derive a transitive orientation of incomparable pairs from any two-order realizer.
2. Prove orientation propagation at a shared vertex with comparable other endpoints.
3. Obtain the anchors and interval witness from occupancy, and prove the five-edge forcing path for every interior incomparable pair with vertical gap >=3r.
4. Choose the orientation of AB once and propagate it to all such pairs.
5. Bound the number of remaining disagreements by the boundary count plus the vertical-strip count <=10rn.
6. Bound each rank difference by the disagreement count and conclude both inequalities with the same swap.

A compiled proof of only components 1 or 2 does not complete this target. Avoid `sorry`, new axioms, and assumptions equivalent to the target. Audit theorem dependencies with Lean's axiom printer; ordinary classical choice and foundational quotient/propositional extensionality dependencies are acceptable and should be reported.

All six components above are implemented and compiled. Remaining to-do list for the selected target: none. Probability, continuous-density interpolation, and the full spacetime theorem remain outside the claim of this first selected Lean target.
