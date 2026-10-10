# The diamond boundary and qualitative conditioning

S042, 2026-10-09 (Hawaii). **The compact weighted quotient, full support and compact time-space metric properties now have GCP acceptance; the smooth gauge bridge and inverse-conditioning arguments remain ordinary work.** The latest [zero-isomorphy component](geometric-zero-isomorphy-certification.md) proves zero-loss attainment, a measure-preserving time homeomorphism and equality of every original finite order law. The separate [finite labeling component](geometric-label-certification.md), [chronological boundary/compact-diamond component](geometric-boundary-certification.md), [actual weighted-curve/time-profile component](geometric-proper-time-certification.md), [AC concatenation/reverse-triangle component](geometric-concatenation-certification.md) [joint endpoint-continuity component](geometric-endpoint-continuity-certification.md) [compact quotient/support component](geometric-quotient-certification.md) and [exact sampling/loss-foundations component](geometric-sampling-loss-certification.md) have GCP acceptance. Retain the original genuine 2+1 class and its accepted conformal-flow obstruction. The arguments below identify the boundary quotient, a forward continuity bound, and a qualitative compactness route. An explicit useful inverse modulus on the full class remains missing. A [restricted-family ordinary pair calculation](geometric-pair-conditioning.md) supplies a candidate finite route with its own open proof obligations. S042 is incomplete and S043 remains gated.

## Model and dependencies

Let C={(t,x): |t|+|x|<=1}, with x in R^2, and let D be its interior. Write V=2pi/3, mu0=Lebesgue/V restricted to D, viewed as a measure on C, eta=-dt^2+dx_1^2+dx_2^2, mu_rho=rho mu0, and g_rho=(rho/V)^(2/3)eta. The original smooth K3 has density in [1/2,3/2], Euclidean Lipschitz constant at most two and integral one. The data are one iid unlabeled directed order, retaining time orientation.

For compactness use B, all continuous functions on C with those bounds, Lipschitz constant and integral. This compact superclass contains the uniform closure of K3; no smoothness of uniform limits is assumed. Its base metric g0=V^(-2/3)eta stays smooth, and log(rho) is a continuous sampling potential.

[Braun-Samann, definitions 2.5 and 4.10, remark 2.6, lemma 2.20 and theorems 4.11-4.12](https://arxiv.org/html/2506.10852v1) provide the established distance-quotient and coupling-distortion framework, including metric and zero-isomorphy properties. Here their hypotheses require verification on C. [Braun's journal weighted reconstruction theorem](https://doi.org/10.1088/1361-6382/ae456c), page 4 and sections 3.1-3.5, applies to smooth globally hyperbolic bases and continuous weights. It supplies qualitative reconstruction from all finite labeled laws. The inspected journal PDF has SHA-256 `5477a946875959d9390fbdc5e500ffa195336d0020a84c2f784d5ddbbd32c762`. Neither source provides our missing explicit inverse constants. No external theorem is introduced into Lean as an axiom.

## Time separation on the closed diamond

Put w_rho=(rho/V)^(1/3). Define tau_rho(p,q) as the supremum of weighted proper lengths of future causal curves from p to q in C, and zero if no such curve exists. Curve length integrates w_rho times the flat Lorentz proper-length integrand. Positive conformal weights leave the causal curve family unchanged.

C is the intersection of the closed future cone of (-1,0) and closed past cone of (1,0), hence is causally convex. D is likewise causally convex using strict tip relations. For p,q in D, their closed flat causal diamond is closed and bounded in R^3 and stays in D by transitivity with the strict tip relations. It is compact in D. The time coordinate excludes causal cycles. This verifies global hyperbolicity of the flat base and every smooth positive conformal rescaling.

The boundary is the union of the two Lipschitz graphs t=+/-(1-|x|) over the spatial unit disk. It has three-dimensional Lebesgue measure zero. Thus the measures on C and D have the same total mass one, while their topological representations still require the boundary analysis below.

Let tau0(p,q)=sqrt((q_t-p_t)^2-|q_x-p_x|^2) when q_t-p_t>=|q_x-p_x|, and zero otherwise. Concavity of the flat proper-length integrand gives curve length<=tau0; the straight causal segment attains equality. Therefore

    (1/(2V))^(1/3) tau0 <= tau_rho <= (3/(2V))^(1/3) tau0.

Thus tau_rho is finite and positive exactly on strict Minkowski chronology. Concatenation proves the reverse triangle inequality.

Continuity holds for continuous weights, including at boundary endpoints. For upper semicontinuity, choose nearly maximizing curves for convergent endpoint pairs and parametrize time affinely on [0,1]. If the limiting time difference is zero, the preceding bound suffices. Otherwise their spatial components are equi-Lipschitz and a subsequence converges uniformly to a causal curve gamma in C. On each interval of a fixed partition, bound the weight by its maximum and the flat length by the endpoint chord length, using concavity. This finite upper bound passes to the limit. Along nested uniform partitions the averaged spatial derivatives converge almost everywhere to gamma's derivative. Uniform continuity removes weight oscillation, and dominated convergence makes the partition bounds converge to gamma's weighted length. The limiting superior is consequently at most tau_rho at the limiting endpoints.

For lower semicontinuity only positive tau matters. Its endpoint chord is timelike. Interpolate a nearly maximizing curve's spatial component with that straight chord by a positive fraction a. The new curve has a uniform strict speed margin. As a tends to zero its lengths approach the original length by dominated convergence. For fixed a, small endpoint perturbations can be absorbed by affine perturbations of the curve while preserving causality. Causal convexity keeps these curves in C, and their lengths converge. Taking these limits and then the near-maximization error to zero proves lower semicontinuity. Hence tau_rho is continuous on C^2 without assuming smooth weights.

### Direct AC endpoint perturbation route (ordinary)

For formalization, a direct perturbation of the existing AC curves provides a shorter alternative to the compactness/reparametrization argument above. This direct route now has [exact-source GCP acceptance](geometric-endpoint-continuity-certification.md) for the actual AC supremum, including joint and uniform continuity on the closed diamond. The derivation below explains the certified construction.

Take a timelike increment `A=q-p`, write `T=A_t` and `alpha=T-|A_x|>0`, and perturb the endpoints to `p',q'` in C with increment `B`. Put `delta=B-A`, `eta=(|delta_t|+|delta_x|)/alpha`, and `k=1-eta`. For sufficiently close endpoints, `0<=eta<1`. The residual `e=B-k*A=delta+eta*A` is future causal because

    e_t-|e_x| >= delta_t-|delta_x|+eta*alpha >= 0.

For any original admissible curve c, its time coordinate is nondecreasing by the future derivative constraint and the AC fundamental theorem. Consequently `theta(t)=(c_t(t)-p_t)/T` lies in `[0,1]`. Define directly, in the same parameter,

    g(t)=p' + k*(c(t)-p) + theta(t)*e.

This curve is coordinatewise AC, has the desired endpoints, and has derivative `k*c' + (c'_t/T)*e` almost everywhere. Both terms are future causal. The integral of a future-cone-valued derivative is future causal: the spatial norm of its integral is at most the integral of its spatial norm, which is at most the time increment. Apply this on each subinterval to get `p'<=g(t)<=q'`. Causal convexity of C then proves containment, including for endpoints on its boundary. This argument does not require c's time coordinate to be strictly increasing or invertible.

Flat proper speed is superadditive on the future cone. One elementary proof takes the Euclidean lifts `(speed(v),v_x)` and `(speed(u),u_x)`, whose norms are `v_t` and `u_t`, and uses the Euclidean triangle inequality and nonnegative square roots. Positive homogeneity therefore gives `speed(g')>=k*speed(c')` almost everywhere.

Let `D_C` be the finite Euclidean diameter of C. Uniformly over c and its parameter,

    |g(t)-c(t)| <= |p'-p| + |delta| + 2*eta*D_C =: epsilon.

Indeed, subtract c in the displayed formula for g, use `0<=theta<=1`, and bound both `|c(t)-p|` and `|A|` by `D_C`. Uniform continuity of a fixed continuous positive weight w on compact C supplies a modulus `omega_w(epsilon)` tending to zero. Since every c has flat length at most two, positivity of w and the speed inequality imply

    L_w(g) >= k*L_w(c) - 2*omega_w(epsilon).

Take the supremum over the original c; the inserted zero causes no problem because the right-side error is nonnegative and the target supremum is nonnegative. This proves

    tau_w(p',q') >= (1-eta)*tau_w(p,q) - 2*omega_w(epsilon).

For a convergent sequence of timelike endpoint pairs, apply the estimate in both directions. Their timelike margins stay bounded below near a timelike limit, while eta and epsilon tend to zero; the uniform bound `tau_w<=2*hi` controls the factor `1-eta`. This proves continuity at every timelike pair directly for the actual AC supremum.

At all other pairs, the flat time separation is zero and is continuous on all endpoint pairs, as seen from the formula

    tau0(p,q)=sqrt(max(T-|A_x|,0)*max(T+|A_x|,0)).

The already accepted inequality `0<=tau_w<=hi*tau0` proves continuity there. Thus the direct route covers every pair in `C^2`, with no maximizing-curve or reparametrization-equivalence assumption. The subinterval causal monotonicity, future-cone speed superadditivity, explicit AC perturbation, uniform length comparison and joint endpoint continuity are now certified. The earlier compactness route is retained above as an alternative ordinary proof.

## The exact boundary quotient

Let W={(0,x): |x|=1}. For p in W and q=(t,y) in C, |y-p_x|>=1-|y|>=|t|. Neither ordered pair is timelike. All points of this waist circle therefore have identical zero incoming and outgoing time-separation profiles. Its zero volume does not remove the failure of point distinction.

No other distinct points share their profiles. Each interior point is in the closure of its nonempty chronological past and future within D. A future lateral boundary point, including the top tip, is in the closure of its nonempty past in D: shift its time slightly backwards. Its future in C is empty. Past boundary points have the reversed properties. Only W has neither kind of neighbor.

If two points have equal nonempty pasts in D, approach each by its interior predecessors. Each point then belongs to the other's closed future cone, so causal antisymmetry makes them equal. Equal nonempty futures give the same argument. Equality of profiles implies equality of these positive-profile sets. Thus W is the only nonsingleton distance-profile class.

Set X=C/W. A compatible quotient metric is induced by

    d_W(p,q)=min(|p-q|, dist(p,W)+dist(q,W)).

It allows free passage through W. Triangle inequalities follow by splitting paths according to whether they use W; distinct noncollapsed points have positive distance. The compact quotient topology agrees with this metric topology. Time separation descends continuously to X^2, has compact positive superlevel sets and distinguishes points. The pushed measure has full support because each nonempty relatively open set meets D in a nonempty open set and rho is bounded below. These are the required bounded Lorentzian metric-measure hypotheses.

D is intrinsically the subset of X having both nonempty positive past and positive future. The remaining lateral boundary is retained; only W is identified.

The exact chronological profile classification, explicit interior-neighbor criteria, lack of all closed-diamond chronological neighbors at W, and compactness of the actual causal diamonds are now [GCP certified](geometric-boundary-certification.md). The [actual weighted-curve supremum](geometric-proper-time-certification.md) now has GCP acceptance for integrability, sharp flat length and straight-segment attainment, two-sided weighted comparison, strict positivity/chronology equivalence and the exact numerical profile classes against all closed-diamond points. Its integrand equals the existing density metric proper speed. The [concatenation component](geometric-concatenation-certification.md) now certifies closure of the same AC class, exact length addition and the causal reverse triangle inequality. The [continuity component](geometric-endpoint-continuity-certification.md) now certifies joint and uniform endpoint continuity, including the boundary. The subsequent [quotient/support component](geometric-quotient-certification.md) certifies the compact metric profile image, exact quotient fibers/topology, continuous time-separation descent, point distinction, compact superlevels and full probability support. Its metric comes from the product of continuous-function spaces. The displayed path-metric formula above remains an alternative ordinary construction; the selected coupling-distortion loss now has accepted bounds, symmetry, triangle and zero-isomorphy on compact measured time spaces. The smooth gauge interpretation remains a separate obligation.

## Gauge and the geometric loss

Use the established coupling-distortion loss d_G on (X,tau_rho,mu_rho): infimize over couplings pi and positive epsilon such that

    (pi tensor pi){|tau_rho(p,p')-tau_sigma(q,q')|>epsilon} <= epsilon.

Time separation is the target geometry, not extra input to the estimator. The generic metric properties are prior work under the representation hypotheses just checked. The actual functional, nonnegativity, universal bound, symmetry, zero self-loss and conditional graph-transport bounds now have [GCP acceptance](geometric-sampling-loss-certification.md). The [triangle](geometric-triangle-certification.md) and [zero-isomorphy](geometric-zero-isomorphy-certification.md) properties are now also certified. Zero distortion is equivalent to a measure-preserving, time-preserving homeomorphism of the compact quotient spaces. The connection to the intended smooth open-spacetime equivalence still requires the gauge bridge below.

If F:D->D is a future-preserving smooth conformal bijection with F*eta=Omega^2 eta, determinants give |det DF|=Omega^3. Consequently

    F*g_sigma=g_rho  iff  rho=|det DF| (sigma composed with F).

Such an isometry preserves weighted curve lengths and volume. It extends to X: the supremum of the incoming/outgoing time-profile differences defines a continuous point-separating metric on compact X, so gives its topology. The same supremum can be taken over dense D. The isometry on D preserves this metric and extends to its compact completion, preserving time separation and measure. Hence d_G=0. This applies to the accepted conformal-flow pair and does not impose an O(2) coordinate gauge.

Conversely, zero distortion supplies a coupling with equal time separations almost everywhere. This attainment result and the resulting compact time homeomorphism are now certified. Coordinatewise measure transport under that homeomorphism gives equal original labeled and unlabeled finite iid chronological laws at every sample size, also now [certified](geometric-zero-isomorphy-certification.md). The journal weighted reconstruction theorem on the smooth flat base, with potentials log(rho) and log(sigma), gives a smooth base conformal bijection satisfying the Jacobian action above. On K3 this is the intended future-preserving smooth metric isometry. On B it identifies continuous conformal coefficients via a smooth base map. This converse retains its explicit external reconstruction dependency.

## Forward continuity

For delta=||rho-sigma||_infinity, the cube-root derivative bound yields

    ||w_rho-w_sigma||_infinity <= A delta,
    A=2^(2/3)/(3 V^(1/3)).

Every flat curve length is at most two. Supremizing over the same curves gives ||tau_rho-tau_sigma||_infinity<=2A delta. Here (2A)^3=32/(27V)<1, since V>2.

Let T be the total variation of mu_rho and mu_sigma, so T<=delta/2. Couple their common density min(rho,sigma) diagonally and their residual density differences by a normalized product. Diagonal probability is at least 1-T. In two independent copies both coordinates agree with probability at least (1-T)^2. On this event the time discrepancy is at most delta; the complement has probability at most 2T-T^2<=delta. Therefore

    d_G(rho,sigma) <= ||rho-sigma||_infinity.

The generic estimate `sup|tau_w-tau_v|<=2 sup|w-v|` is now GCP accepted for positive continuous bounded weights. The density-specific cube-root constant and diagonal/residual coupling argument still require their own formal proofs.

This is a forward continuity statement in the fixed normalized model. It is not an inverse bound from orders or a coordinate gauge selection.

## Finite labels and qualitative conditioning

For fixed n the iid labeled order law is invariant under vertex permutations. Point masses are constant on each finite isomorphism orbit, and each equals the orbit's unlabeled mass divided by its size. Summing absolute differences gives equality of labeled and unlabeled total variation. In particular equal unlabeled laws imply equal labeled laws. No infinite generic sequence is randomly reordered. The existing QuotientTV finite fiber lemma supplies the formal pattern. Its actual 2+1 iid instantiation and both law-equality directions are now [GCP certified](geometric-label-certification.md) for finite density measures, with explicit original-class corollaries. The continuous-class measure and geometric arguments still require their own formalization.

B is compact by uniform boundedness, a common Lipschitz constant and closed range/integral constraints. For every n, diagonal sample coupling gives

    TV(law_n(rho),law_n(sigma)) <= n TV(mu_rho,mu_sigma)
                                <= (n/2)||rho-sigma||_infinity.

The forward bound and triangle inequality make d_G jointly continuous on B^2. Fix epsilon>0. Pairs with d_G>=epsilon form a compact set. Each such pair has different laws at some finite size, by finite exchangeability and the journal weighted theorem. Law continuity gives an open neighborhood with a positive separation. A finite subcover supplies some finite N and gamma>0 such that

    d_G(rho,sigma)>=epsilon implies TV(law_N(rho),law_N(sigma))>=gamma.

For a nonempty separated set, take N to be the largest selected size. Labeled-law TV cannot decrease on adding points, by projection onto fewer sample coordinates; finite labeled/unlabeled equality transfers this fact to the observed laws. If the separated set is empty, N=2 and gamma=1 give a vacuous statement.

This avoids assuming smooth limits, but supplies **no explicit N(epsilon), gamma(epsilon) or computable optimization procedure**. It does not pass S043's quantitative gate.

A possible single-observation frequency route must also handle dependence. Uniform random labeling of a canonical representative, using an explicit independent seed, has exactly the original iid labeled order law by finite exchangeability. Disjoint k-point blocks then have iid law_k distributions, permitting coordinatewise Bernoulli bounds and a finite union bound for empirical frequencies. A deterministic data-dependent partition of a canonical order cannot simply be called iid. This is a randomized route, not a certified frequency theorem or implemented estimator.

Remaining to-do list: audit these ordinary geometric arguments and external proof dependencies; complete the smooth gauge/curve transport and density forward endpoints on GCP; audit/certify the restricted finite route or obtain a rigorous scoped obstruction; resolve S043's gate. The finite labeling bridge and exact quotient iid/order-law transport are accepted, but the random-label/disjoint-block observation construction is separate. No new publication or physical application is claimed complete.
