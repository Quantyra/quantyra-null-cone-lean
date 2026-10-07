# Proof review and continuation requirements

Reviewed on 2026-10-06 Hawaii time for Quantyra Space, proof review and continuation plan (E002/S008). Baseline: `b0c8ce62e5ee9c5c7f4a21058063c03a116b2d9c`, including the manuscript, all four Lean modules, and the identifiability, quantitative-reduction, rate, label/time, and completion notes. This is a further Codex review under the author's direction, not independent specialist review.

**Current notice, 2026-10-07 (S009/S011):** the review below is historical. Its specialist-review gate is superseded by the open-source [contribution/feedback protocol](../CONTRIBUTING.md). Full inverse/identifiability and law equivalence now have retained GCP evidence; S010's full Winkler comparison is complete with a bounded originality verdict. [Current research navigation](../RESEARCH.md) maps those claims. Historical opinions, proof analysis and earlier to-do lists remain preserved and do not reinstate a specialist/adoption prerequisite.

**Verdict:** no blocking mathematical error found in the finite theorem or the probability-to-density argument. The stated constants and hypotheses are consistent. The finite theorem has matching Lean and prose statements; the full inverse bound remains a prose proof. Originality remains provisional. The immediate work is clearer exposition and historical-status reconciliation, followed by full-text comparison and independent review.

## Verification evidence

The local and remote main SHA matched the baseline. Both jobs in [the baseline CI run](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37571081623) succeeded. Its actual logs were inspected: 984 Lean build jobs; both final theorem dependency reports contained only `propext`, `Classical.choice`, and `Quot.sound`; source/dependency integrity passed; 36 grids and 865445 separated edges passed; 120 permutation orders and 771 realizers passed; the seven-page manuscript compiled successfully. These are existing checks of the exact reviewed commit, not checks newly executed locally by this review.

This workstation had no usable `lake` command or Python runtime (`python` resolved to the Windows Store alias). No fresh local Lean build or Python sanity run is claimed. A fresh source scan found no `sorry`, `admit`, or axiom declaration in the proof modules or audit. PowerShell arithmetic independently checked `20+10=30`, `30+2=32`, `20+64+3=87`, `12/256=0.046875`, and `4096*174=712704<100^3`. No mathematical source or manuscript was changed during this review.

## Finite theorem and statement audit

`Realizer.lean` defines two strict total orders whose intersection is exactly chronology. Opposite orientations are derived from those orders. Shared-vertex forcing follows from their transitivity and the comparable-endpoint contradiction; there is no assumed uniqueness or prime-graph hypothesis.

`Grid.lean` obtains A, B, W and the first-column witness from actual occupied open cells. Its grid-interval lemma supplies strict endpoints even when the vertical gap is exactly `3r`. Forcing through `xy, zy, Ay, AW, AB` uses one anchor orientation across all eligible pairs.

`Counts.lean` uses real differences of natural predecessor counts, avoiding truncated natural subtraction. `Bridges.lean` bounds the vertical strip by `10rn`, combines it with the `20rn` boundary count, and proves both rank errors. The final statement is `forall L, exists swap, forall interior i, bound1 AND bound2`; the swap cannot vary with the event or rank. The specified theorem retains the original unit-square, no-grid-line, and both-marginal hypotheses. The stronger general theorem's unused hypotheses do not weaken that specialization. Nothing equivalent to the final rank conclusion is assumed.

## Cumulative reconstruction bridge

The manuscript's Section 4 is correct but compressed. The following details should be inserted during proof exposition and status reconciliation (S009).

1. With distinct coordinates and inclusive empirical thresholds, `rank_u(i)/n = F_u,n(u_i)` exactly: one plus the strict predecessor count includes the event itself. There is no additional `1/n` error. The marginal discrepancy therefore adds `2r` to `30r`, giving `32r` coordinate error for interior events.
2. Write `q_i` for the reconstructed rank point after the single global swap, `x_i` for the latent point, `b=#B/n`, and `d=32r`. For `s,t` in the square set `s_- = max(0,s-d)`, `s_+ = min(1,s+d)` and likewise for t. Interior-point indicator inclusion gives, simultaneously for all thresholds,

   `C_n(s_-,t_-) - b <= A_n^S(s,t) <= C_n(s_+,t_+) + b`.

   If a lower threshold clips to zero, the latent lower rectangle contains no points because all latent coordinates are strictly positive. Upper clipping is valid because all points lie in the square. This also covers reconstructed ranks equal to one and values of d larger than one.
3. Uniform population marginals imply that changing the thresholds by at most d changes population mass by at most `2d`. The full empirical error is `3r`, and `b<=20r`. Thus the error is at most `20r+64r+3r=87r`. Each direction uses one boundary term and one empirical replacement. The same swap serves every rectangle.

The grid-vertex premise yields the required deterministic inputs by monotonicity: arbitrary marginal error at most `2r`, arbitrary rectangle error at most `3r`, and four boundary tails of at most `5r` each. No coordinate ordering is supplied to the reconstruction map: it enumerates realizers of the observed finite poset. Its finite domain also makes its selection and every preimage event used below measurable without a function-space measurability theorem.

## Probability and constants

The density floor gives each open cell mass at least `1/(2m^2)`. Independence is across sampled events, so the empty-cell probability is at most `exp(-n/(2m^2))`; union over `m^2` cells is valid without independence between cells.

For a fixed grid vertex, each rectangle indicator is Bernoulli. The standard Hoeffding step can also be checked directly: the centered Bernoulli log moment-generating function has value and derivative zero at zero, and second derivative at most `1/4` under exponential tilting. Hence it is bounded by `lambda^2/8`. Multiplication across n independent indicators and Markov's inequality with `lambda=4r` bound either tail of the empirical average by `exp(-2nr^2)`. A two-sided bound and the `(m+1)^2`-vertex union give the stated `2(m+1)^2 exp(-2n/m^2)`. This argument does not use independent overlapping suborders.

For `m=floor(n^(1/4))`, `n>=65536` implies `m>=16` and `n>=m^4`. The inequality `exp(t)>=t^2/2` bounds the two failure terms by `8/m^2` and `(m+1)^2/m^4<=4/m^2`. Thus success exceeds `9/10`. The rounding inequality `m>=n^(1/4)/2` gives `a_n=174n^(-1/4)`. Ties, endpoints, and grid-line events have probability zero by absolute continuity. All bounds are uniform over the stipulated class.

## Separation and density interpolation

The two transpose orbits each have two elements, possibly coincident. Transposition is a supremum-norm isometry, so the minimum of the four cross-orbit distances is exactly `epsilon_*` in the manuscript. If `epsilon_*>2a_n`, their closed good-output neighborhoods are disjoint. The preimage of the rho neighborhood under the same finite order-only map has probability at least `0.9` under rho and at most `0.1` under sigma. Thus `TV>=0.8`. Dependence of the successful alignment on the sample creates no problem because each neighborhood already includes both alignments.

For `TV<0.8`, interpolate in the orientation minimizing cumulative discrepancy. The density metric is no greater than the coefficient error in that orientation, even if another orientation minimizes the coefficient norm. For `TV>=0.8`, use `d_conf<=1<=1.25 TV`. Equality belongs to this second branch.

For interpolation, the density difference is 4-Lipschitz and has supremum delta at most one. A square of side `delta/16` directed into the domain from a maximizing point fits even at a corner. The difference retains one sign and magnitude at least `delta/2`; its integral has magnitude at least `delta^3/512`. Four cumulative corner values bound it by `4 epsilon`, yielding `delta^3<=2048 epsilon`. Combining with `epsilon_*<=2a_n` gives `(4096a_n)^(1/3)`. The coefficient `(712704)^(1/3)` is approximately `89.3243`, below 100. For the smaller-N branch, the claimed N term is already greater than one at `N=65536` and is larger for smaller N.

The localized mean-zero bump argument in `quantitative-reduction.md` also checks out: coefficient discrepancy scales as h, cumulative discrepancy as h cubed, marginals remain uniform, and the gradient bound is uniform. It establishes the cube-root obstruction for that intermediary only; it proves no optimality of the finite-order exponent.

## Consequences and the separate qualitative argument

All-size identification follows from the fixed pair of coefficient norms and the rate tending to zero. Exchangeability gives equal mass to every labeled representative in an isomorphism orbit, so summing the finite TV expression yields exactly the unlabeled TV. Neither assertion quotients by time reversal.

For proper time, the density floor bounds the difference of the square-root coefficients by the density discrepancy. Cauchy-Schwarz bounds the integrated curve factor by one. The common monotone curve class and finite suprema justify taking the difference of suprema. The coefficient-minimizing identity or swap works for all endpoints. No derivative or curvature conclusion follows.

The older positive-continuous-density argument is a separate, broader draft. [Janson, Theorem 7.1(iv),(ix)](https://arxiv.org/html/0902.0306v1#S7) was rechecked: Borel spaces and almost twinfree kernels are required for the conull measure-preserving bijection. The local proof uses both incoming and outgoing profiles, restricts to interior points, preserves positive past/future masses to keep limits in the interior, then recovers weak product order and fixes increasing coordinate maps by uniform marginals. No defect was found in these steps. Make the closed-square continuity/positivity convention explicit if this broader statement is retained for publication. Its profile-extension route is unnecessary for the current theorem in K and should remain outside the critical path. The two empty-profile corners must never be identified as distinct points of a profile metric on the closed square.

## Findings and disposition

| Finding | Severity and consequence | Continuation |
| --- | --- | --- |
| No mathematical counterexample or missing essential hypothesis found in the current theorem | Bounded positive review; does not establish independent correctness certification | Preserve the current statement and constants |
| Rank/CDF endpoint sandwich and orbit-distance argument are compressed | Exposition improvement; the derivations above close the presentation obligations | Proof exposition and status reconciliation (S009) |
| `quantitative-reduction.md` still says H has not been proved; older identifiability/completion to-do lists are obsolete | Handoff risk despite the existing historical notice | Add dated supersession notices and current destinations; preserve historical claims and provenance (S009) |
| Both Winkler full texts remain unassessed | Blocks stronger priority claims, not continuation of the mathematics | Full-text originality comparison (S010) |
| Another Codex pass is not independent specialist review | External correctness and significance assessment still outstanding | Specialist review and responses (S011) |
| Probability, CDF, interpolation, and proper-time bridges are outside Lean | Accurately disclosed scope, not a failed finite theorem | Optional full inverse formalization (S013) |
| Faster grid scale remains an unproved proposal in the existing notes | Optional improvement could distract from review gates | Optional rate optimization (S014) |

Publisher records were rechecked for [Winkler, Random orders (1985), pp. 317-331](https://doi.org/10.1007/BF00582738) and [Random orders of dimension 2 (1990), pp. 329-339](https://doi.org/10.1007/BF00383197). This review did not obtain or compare their full texts. Their metadata and abstracts cannot settle whether a structural result implies our finite lemma or inverse bound.

The execution order and acceptance gates are in the planning repository's `docs/proof-review-and-continuation-plan.md`. Remaining to-do list: proof exposition/status reconciliation (S009), full-text originality comparison (S010), specialist review (S011); optional manuscript deposit (S012), full inverse formalization (S013), and rate optimization (S014).
