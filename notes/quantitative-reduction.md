# Quantitative reduction through rectangle masses

2026-10-06, E002/S005. The explicit density comparison below is established by a direct mathematical argument. The reduction from finite abstract orders is conditional on an unproved reconstruction hypothesis. Neither is Lean verified. No novelty is claimed for Lipschitz interpolation or the statistical separation argument.

Later same-day update: `finite-order-rate.md` now supplies the reconstruction hypothesis through a grid-witness proof and derives explicit exponents and constants. The conditional derivation below is retained; its original open-hypothesis status is superseded by that proof draft, subject to audit and formal verification.

## Rectangle discrepancy controls the coefficient

For rho,sigma in K define C_rho(u,v) = integral over [0,u] times [0,v] of rho and epsilon = sup |C_rho-C_sigma|. Then

`||rho-sigma||_infinity^3 <= 2048 epsilon`.

Proof. Let f = rho-sigma and delta = ||f||_infinity. The density bounds give delta <= 1; f is 4-Lipschitz in Euclidean distance. If delta = 0 the claim is immediate. Otherwise compactness supplies x with |f(x)| = delta. Set h = delta/16. In each coordinate choose an interval of length h extending from x toward the half of the unit interval with more room; their product R is contained in D. Every z in R has Euclidean distance at most sqrt(2) h <= 2h from x. Hence |f(z)-f(x)| <= 8h = delta/2. The function retains its sign and absolute value at least delta/2 on R. Thus

`|integral_R f| >= (delta/2) h^2 = delta^3/512`.

Inclusion-exclusion expresses the rectangle integral as four signed corner values of C_rho-C_sigma, bounding it by 4 epsilon. Combining gives the claim. This handles maxima on edges and corners as well as the interior. The constant is deliberately conservative.

Apply the same lemma to sigma transposed when choosing the residual gauge. The cube-root bound controls the actual coefficient, independently of order statistics.

## The cube root cannot generally be improved for this intermediary

Choose a nonzero smooth mean-zero function psi supported in (-1,1), normalized to sup |psi|=1. Write D_psi = sup |psi'|. Fix 0 < a <= min(1,1/(sqrt(2) D_psi)). For 0 < h < 1/4 define

`rho_h(u,v) = 1 + a h psi((u-1/2)/h) psi((v-1/2)/h)` and `sigma = 1`.

The compact support and mean zero give exact uniform marginals. These are smooth positive densities with bounds 1/2 and 3/2, and Euclidean gradient norm at most a sqrt(2) D_psi <= 1, hence they belong to K. Their coefficient discrepancy is a h. If Psi is the primitive of psi from minus infinity, their cumulative discrepancy is exactly a h^3 sup |Psi|^2. Since psi is nonzero the primitive norm is positive. Therefore no uniform estimate delta <= C epsilon^gamma with gamma > 1/3 can hold even on K as h tends to zero. This is an obstruction for cumulative masses, not a refutation of the abstract-order conjecture: abstract orders can contain additional information.

## A sufficient finite-order reconstruction hypothesis

Suppose there is one deterministic function A_n of the labeled n-event partial order, taking values in cumulative functions on D. The function cannot use latent coordinates or either underlying total order. Suppose uniformly for every rho in K,

`P(min(sup |A_n(P)-C_rho|, sup |A_n(P)-C_(rho transposed)|) <= a_n) >= 9/10`.

Call this hypothesis H(n,a_n). It has NOT been proved. Allowing a different latent-coordinate-dependent function for each rho would not satisfy it.

Under H(n,a_n), the finite-law distance yields the explicit conditional bound

`d_conf(rho,sigma) <= (4096 a_n)^(1/3) + (5/4) TV(nu_n(rho),nu_n(sigma))`.

Proof. Let epsilon_* = min(sup |C_rho-C_sigma|, sup |C_rho-C_(sigma transposed)|). If epsilon_* > 2a_n, the two sets of outputs within a_n of the respective transpose-orbits are disjoint. The rho-good set has probability at least 9/10 under rho and at most 1/10 under sigma. Their order laws therefore have TV at least 4/5. Consequently TV < 4/5 implies epsilon_* <= 2a_n. The rectangle lemma then gives d_conf <= (4096 a_n)^(1/3). If TV >= 4/5, use d_conf <= 1 <= (5/4)TV. Both cases imply the displayed bound, including equality at the threshold. No assumption of independent overlapping suborders is involved.

If a_n <= A n^(-gamma), this proves the conjecture with alpha = gamma/3, beta = 1 and C = max((4096 A)^(1/3),5/4), using n=N and TV(nu_N) <= Delta_N. Thus a polynomial reconstruction theorem is sufficient; this observation alone does not establish one.

## Next mathematical gate

Reconstructing a realizer of a finite dimension-two poset is insufficient by itself: different realizers can give different coordinate rankings. A quantitative proof must show an order-only choice approximates the original sampled measure up to one global axis swap, uniformly with high probability. Small modules may permit local ambiguities, and a sample cannot simply be assumed prime.

Potential source route: [Klavik and Zeman, Automorphism Groups of Comparability Graphs](https://arxiv.org/abs/1506.05064) studies permutation-graph structure; [Koehler, Modular decomposition of transitive graphs and transitively orienting their complements](https://arxiv.org/abs/1710.04333) gives relevant complement-orientation machinery. Their abstracts do not supply H(n,a_n). Inspect their exact decomposition results, then derive a density-uniform probabilistic bound rather than borrowing uniqueness without its hypotheses.

Remaining to-do list: prove H with a polynomial rate or find an obstruction; audit identifiability; compare any completed inverse theorem with prior work; freeze a substantive Lean statement and compile its proof.
