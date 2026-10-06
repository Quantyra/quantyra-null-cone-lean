# Explicit inverse rate from finite abstract orders

2026-10-06, E002/S005. Mathematical proof draft, not Lean verified or independently peer reviewed. This supplies the previously missing reconstruction hypothesis using elementary orientation witnesses. Novelty of the combination remains to be checked; realizer theory, concentration, and Lipschitz interpolation are established tools.

## Main statement

In the precise class K and notation of the planning specification, for every N >= 2,

`d_conf(rho,sigma) <= 100 (N^(-1/12) + Delta_N(rho,sigma))`.

These deliberately conservative constants give alpha=1/12 and beta=1. No optimality of this rate is asserted. The observable is the distribution of labeled partial orders, not latent coordinate rankings and not one noiseless empirical order law.

## Order-only reconstruction

For a labeled dimension-two poset P, enumerate pairs of total orders whose intersection is P, and choose the lexicographically first pair (L_1,L_2), using only event labels to break ties. Existence holds for every sampled poset because the latent coordinate orders are a realizer; the definition does not access them. Efficiency is irrelevant to the theoretical statement. For orders outside this class define the output arbitrarily.

Place vertex i at (rank_(L_1)(i)/n, rank_(L_2)(i)/n). Let A_n(P) be the empirical cumulative distribution of these points. A choice of another realizer will satisfy the same error guarantee below, up to one global axis swap.

## The orientation forcing rule

Each realizer induces an orientation Q of incomparable pairs by the first total order; the second total order reverses every such pair. Q is transitive: two successive Q comparisons hold in the first order and reverse in the second, so the endpoints are also incomparable and related by Q.

If xy and xz are incomparability edges while y,z are comparable in P, their orientations at x must agree. Otherwise Q has a directed path from y through x to z, or the reverse, forcing an incomparability edge between y and z. Therefore orientations propagate through these shared-vertex steps. This rule is applied to every realizer, including the true latent one.

## Grid occupancy forces the separated interior edges

Let r=1/m with m>=16. Assume the sample meets every open grid cell of side r and has no coordinate ties or points on grid lines. Set J=[4r,1-4r]^2. Choose sampled anchors

- A in (r,2r) times (1-2r,1-r);
- B in (1-2r,1-r) times (r,2r);
- W in (1-r,1) times (1-3r,1-2r).

These are distinct and AB and AW are incomparability edges. B precedes W.

Take any interior incomparable pair x,y with x_u<y_u and x_v>y_v and vertical gap x_v-y_v>=3r. The interval (y_v,x_v) contains a full open vertical grid interval. Grid occupancy supplies z in (0,r) times that interval. Then z precedes x and A, while z is incomparable with y. Also A is incomparable with y and y precedes W. Consequently the incomparability edges

`xy, zy, Ay, AW, AB`

form a forcing path: successive edges share y,y,A,A and their other endpoints are respectively comparable pairs (x,z), (z,A), (y,W), (W,B). The orientations of every edge on this path are fixed by the orientation of AB. Choose one global swap of the reconstructed total orders to make its AB orientation agree with the latent first coordinate. Every such separated interior edge then agrees with the latent ordering. Comparable pairs agree automatically. The only possible ranking disagreements for an interior vertex involve boundary vertices or interior vertices with vertical difference less than 3r.

The witnesses are sampled events whose existence follows from occupancy. The reconstruction algorithm itself never sees the grid, anchors, or latent coordinates; they are used solely to prove that ANY realizer has the claimed accuracy.

## Deterministic ranking and cumulative error

In addition to occupancy suppose the empirical cumulative distribution C_emp differs from C_rho by at most r at every grid vertex. Uniform marginals imply:

1. At arbitrary thresholds both empirical marginal distribution functions have error at most 2r, by monotonicity between grid vertices.
2. The full empirical cumulative distribution has error at most 3r, since C_rho changes by at most the sum of the two coordinate changes.
3. The fraction of vertices outside J is at most 20r: each of four marginal tails at the grid thresholds 4r and 1-4r is at most 5r. Overcounting intersections only increases this bound.
4. For any vertex x, the fraction of sample points with |v-v_x|<3r is at most 6r+4r=10r, using the arbitrary-threshold marginal error twice. Bounds remain valid at clipped thresholds.

After aligning the realizer globally as above, at most 30rn pair comparisons affecting the rank of an interior vertex can disagree. Its two reconstructed ranks divided by n therefore differ by at most 30r from the two latent empirical ranks. Each latent rank divided by n differs from its true coordinate by at most 2r. Every interior reconstructed point is thus within 32r of the corresponding true point in each coordinate. The boundary fraction is at most 20r.

For any anchored rectangle, ignoring boundary vertices changes its mass by at most 20r. Shifting both thresholds by 32r bounds the contribution of the interior coordinate error. Population mass changes by at most 64r because both marginals are uniform; replacing the true empirical distribution by C_rho costs at most 3r. Upper and lower bounds therefore yield

`sup |A_n(P)-C_rho| <= 87r`,

after the one global swap. Equivalently the unswapped order-only A_n is within 87r of C_rho or C_(rho transposed). This is precisely the previously specified H(n,87r).

## Uniform probability and polynomial rate

For n>=16^4=65536 choose m=floor(n^(1/4)). A grid cell has probability at least r^2/2 by rho>=1/2. The chance any of the m^2 cells is empty is at most

`m^2 exp(-n/(2m^2))`.

At each grid vertex the empirical rectangle indicator average is an average of independent Bernoulli variables. Hoeffding's inequality and a union bound give grid-vertex error failure probability at most

`2(m+1)^2 exp(-2n/m^2)`.

No independence between different rectangles or between pairs of sampled events is assumed. Grid lines and coordinate ties have probability zero.

Since n>=m^4, the sum of these failures is at most m^2 exp(-m^2/2)+2(m+1)^2 exp(-2m^2). Using exp(t)>=t^2/2 for t>0 bounds these terms by 8/m^2 and (m+1)^2/m^4 <=4/m^2, respectively. Their sum is at most 12/256<1/10. Thus the reconstruction success probability is at least 9/10, uniformly in K.

Also m>=n^(1/4)/2, so 87r<=174 n^(-1/4). The conditional separation argument in `quantitative-reduction.md` now applies WITHOUT an unproved hypothesis, giving

`d_conf <= (4096*174)^(1/3) n^(-1/12) + (5/4) TV(nu_n(rho),nu_n(sigma))`.

Because 4096*174=712704<100^3, this is bounded by the main statement with n=N. For 2<=N<65536 use d_conf<=1 and 100 N^(-1/12)>1. Hence the statement holds at every required N. All density and gauge bounds are those already fixed in S005.

## Identifiability and Lean target

Equal laws at all sizes imply Delta_N=0 for every N. Letting N increase in the displayed rate gives d_conf=0. Thus this quantitative argument also supplies identifiability for K without importing the infinite-kernel theorem. The earlier broader positive-continuous-density proof remains a separate draft.

Select the deterministic grid-witness rank reconstruction as the substantive Lean target. Its statement must quantify over finite labeled samples with distinct coordinates, grid occupancy, empirical marginal error, and arbitrary two-order realizers, and conclude that ONE global swap gives rank error <=30rn on J. Formalizing only the single shared-vertex rule would not verify the selected target. The probability and density-interpolation bridges should remain explicitly separate until compiled as well.

Remaining to-do list: adversarial audit of the complete rate; exact prior-work comparison for the forcing reconstruction and inverse theorem; freeze the finite Lean statement and compile it; update the planning disposition only after those checks.
