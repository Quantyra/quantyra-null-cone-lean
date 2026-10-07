# Order-only finite reconstruction: method and coverage

2026-10-07, E002/S019. Implementation: [CLI](../tools/finite_data.py), [combinatorics/calibration](../tools/finite_data_core.py), [LP and rational checker](../tools/finite_data_lp.py). This is ordinary mathematical and software verification, not a new Lean theorem. The original smooth class K, iid sampling and one global transpose remain fixed. Invalid orders are rejected; missing/noisy relations are not repaired implicitly.

## Constructive realizer and deterministic rank certificate

Represent the full strict directed order P by bit rows. Verify irreflexivity, absence of two-cycles and transitivity. Orient the incomparability graph Q by Golumbic's implication-class deletion: choose an edge, propagate the induced-P3 forcing class, remove its undirected edges and repeat on the remaining graph. Classes must be recomputed after deletions to prevent cyclic triangles. This is established graph theory, not an original algorithm; [the SAND 2026 paper's static-algorithm discussion](https://drops.dagstuhl.de/storage/00lipics/lipics-vol373-sand2026/html/LIPIcs.SAND.2026.7/LIPIcs.SAND.2026.7.html) states this procedure. See also [McConnell-Spinrad, Section 4](https://www.cs.colostate.edu/~rmm/linto.pdf). Return P union Q and P union reverse(Q), then independently verify two permutations and their exact intersection with P. No latent coordinates are supplied.

For the confidence certificate, use implication classes of the **original** incomparability graph, not the deleted-edge graphs. Pick its largest undirected class C and retain a rooted forcing tree: each new oriented edge follows from an earlier edge by sharing an endpoint while the other endpoints are comparable in P. Every transitive orientation must agree throughout C or reverse throughout C. Thus any two realizers have one global axis alignment on C; comparable pairs already agree. Let d_i count incomparable neighbors of i outside C. Both rank differences at i, after that one swap, are <=d_i by counting potentially disagreeing predecessor indicators. This is a direct finite consequence of established forcing, not a claim that forcing or all-realizer recovery is new.

For any integer j>=0 put b_j=#{i:d_i>j}/n. On the remaining points each normalized rank difference is <=j/n. The algorithm chooses j minimizing B(P)=min(1,min_j(b_j+2j/n)). A rooted forcing subset would suffice; choosing the largest class is a heuristic, not a proof that it minimizes this budget. The verifier checks the supplied forcing tree, covered edges, unresolved degrees and reported budget without running the realizer-construction algorithm. Exhaustive comparisons against every five-point realizer test the simultaneous global swap/rank claim.

## Uniform probabilistic certificate

This section records the original `grid` calibration, retained for old reports. New estimates default to the [separate DKW marginal/joint calibration](finite-data-confidence-sharpening.md), with radius B(P)+2epsilon_m+epsilon_j+2/q. The deterministic forcing and LP arguments apply to either certified radius.

Choose a deterministic q and epsilon from n and requested delta. On the (q+1)^2 fixed population-CDF grid vertices, Hoeffding and a union bound give

    Pr(max_vertex |C_n-C_rho| > epsilon) <= 2(q+1)^2 exp(-2n epsilon^2).

The axes need not be independent; Bernoulli indicators for one fixed rectangle are independent across sampled points. Uniform marginals and monotonicity extend this event to marginal error <=epsilon+1/q and joint CDF error <=epsilon+2/q at all thresholds. Inclusive ranks equal empirical marginal CDFs at each sampled coordinate, with ties and boundary points absent almost surely.

For the at-least-(1-b_j)n retained points, the selected normalized rank coordinates differ from latent coordinates, under the same global swap, by <=j/n+epsilon+1/q. The clipped orthant sandwich loses at most b_j mass and at most twice that coordinate shift in the population CDF. Adding the latent empirical joint error gives

    min_S ||A_P-C_(rho composed with S)||_infinity
        <= B(P)+3 epsilon+4/q.

This holds on the **same** grid event for every P, every j and every realizer, so data-dependent trimming adds no union penalty. The resulting a is clipped at one; a=1 is deterministic and has failure bound zero. The q choice uses only n and delta, not the observed order: minimize 3epsilon+4/q over a fixed list of meshes. Epsilon is rounded upward to multiples of 10^-6. No unverified floating logarithm determines coverage. The exact rational inequality

    exp(-t) <= (1+t/512)^(-512)

certifies the union bound. The reported probability is rounded upward on a rational grid that represents delta exactly. No occupied-grid assumption or the earlier constant 87 is needed. This data-dependent certificate can be nontrivial when the occupied-grid route is unavailable; uniform dominance over that route is not asserted. Its originality/significance remains unassessed beyond the known structural ingredients.

## LP bands and numerical certification

At a separate k-by-k estimation mesh, compute A_P corner counts exactly with integer ranks. Candidate cell averages have bounds [1/2,3/2], exact row/column sums k and cumulative corner masses within a of A_P. Neighboring cell averages differ by <=2/k: translate the cells by distance 1/k and integrate the density's 2-Lipschitz inequality. Hence true aligned cell averages are feasible on the same event. This is a relaxation, not a characterization of smooth K.

For each cell solve min b_ij and min -b_ij. HiGHS supplies multipliers, not trusted optimality. For minimization objective c, inequality matrix A x<=b, equality E x=d and multipliers y<=0,z arbitrary, set r=c-A^T y-E^T z. Every feasible x in [L,U] satisfies

    c dot x >= b dot y+d dot z + sum_j min(r_j L,r_j U).

The checker evaluates this weak-duality formula with exact fractions, including residuals from nonstationary/rounded multipliers. Positive inequality multipliers are replaced by zero before certification. Thus a solver tolerance or even a suboptimal dual does not invalidate the outer bounds. The verifier needs no SciPy installation or solver. Failed solves yield conservative full-range bands; numerical infeasibility is not reported as a proven empty class. Contradictory certified restrictions also trigger a full-range fallback.

At a point of a cell, average L1 distance to a uniform point in that cell is <=1/k: each coordinate's average absolute distance is <=1/(2k). Therefore the density differs from its cell average by <=2/k, improving the scope's earlier 2sqrt(2)/k bound. Expand cell-average limits by 2/k and clip to [1/2,3/2]. On the single event, **all** resulting point bands cover rho in **one** global orientation. Cell partitions are half-open with top/right edges included; the assertion extends to their closure by continuity. Histograms are coefficient estimates, not smooth metrics in K.

The point estimate minimizes LP L1 deviation from the flat histogram. Its rounded values are clipped to the density range; their exact maximum corner-constraint excess eta is measured. Four-corner inclusion-exclusion proves coefficient error <=min(1,8ak^2+4eta k^2+2/k). This certificate uses the actual rounded output, not an assumed feasible optimizer. The histogram is not asserted to satisfy marginal equalities exactly; its corner residual suffices for this error calculation, and the full rational values are retained. Fallback estimates use the trivial coefficient error one.

## Limits and verification

The Python algorithm is a dense reference implementation, not McConnell-Spinrad's linear-time implementation. Forcing propagation uses O(nm) work in the usual adjacency accounting; validation and permutation certificates add polynomial dense work. LP bounds require 2k^2 solves plus a central-point solve, with O(k^2) variables and O(k^2) constraints. Rational certificates and their validation can dominate runtime. The CLI caps n at 4096, k at 16 and JSON input at 64 MiB; those are resource limits, not a proven practical sample budget.

The [experiment report](finite-data-experiment-report.md) records actual coverage/error/width/runtime/memory and the new-paper decision. Conditional LP tests at prescribed radius are algebra tests, not empirical unconditional confidence claims. Proofs above establish uniform coverage in K; finite simulations assess implementation behavior in selected examples. The construction does not estimate Delta_N from overlapping suborders, certify a noisy-order model, establish an optimal rate or address curvature.

Remaining to-do list: none for method/experiment delivery; future sharpening/publication decisions follow the recorded gate.
