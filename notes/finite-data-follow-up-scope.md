# Finite-data follow-up scope

2026-10-07, E002/S017. Decision: prioritize a constructive confidence procedure from one sampled directed order in the existing two-dimensional class. This is a scoped next project, not a completed estimator paper. The existing inverse theorem compares *laws* and does not estimate Delta_N from one observed order.

## Observation and existing baseline

Observe only an n-point directed poset P. No latent coordinates, coordinate rankings or occupancy certificate are input. Work in the existing class K, with one global transpose ambiguity. Any enumeration of the input vertices is acceptable: the bound applies to every realizer, so a selector depending on that enumeration retains coverage. Do not assert a canonical selector under graph isomorphism without implementing one.

Validate the directed partial order, orient its incomparability graph transitively, and return the two orders P union Q and P union Q^d. Certify their intersection equals P. This replaces classical choice with an actual algorithm; it is not a new graph algorithm. [McConnell and Spinrad (1999)](https://www.cs.colostate.edu/~rmm/linto.pdf), abstract and Section 1, give linear-time modular decomposition/transitive orientation on adjacency-list input. [Kratsch et al.](https://www.cs.colostate.edu/~rmm/certIntvlPermut.pdf), Section 6 and Lemma 6.5 (printed 344), give certifying permutation recognition. Implementations must be checked: orienting a non-comparability graph can otherwise return a faulty orientation. A dense n-by-n order representation already costs O(n^2); do not promise subquadratic end-to-end runtime.

Build A_P, the empirical CDF of normalized inclusive ranks in that realizer. For m>=16, the existing theorem gives a=87/m and

    p_fail(n,m) <= m^2 exp(-n/(2m^2)) + 2(m+1)^2 exp(-2n/m^2).

Choose m deterministically from n and requested delta in (0,1), requiring this upper bound <=delta. On a single event of probability at least 1-delta, one global choice S in {identity, transpose} satisfies ||A_P-C_(rho composed with S)||_infinity<=a. Use the full square CDF, including boundary thresholds. If no valid useful m exists, output the full admissible range rather than an unsupported confidence claim. The logarithmic choice yields a=174 sqrt(8) sqrt(log n/n) for n>=65536, with its already-derived explicit failure bound. These constants will often make confidence intervals trivial.

An ideal confidence set consists of all admissible q whose CDF is within a of A_P in either orientation. Any two covered members, after alignment, have coefficient distance at most (4096a)^(1/3), clipped at one, by the existing boundary interpolation estimate. This is an immediate corollary, not a new main theorem. Smooth K is not compact: any optimization/attainment proof must use its bounded Lipschitz closure and prove the interpolation extension, or specify an approximate optimizer. Neither step is presently Lean formalized.

## Concrete computable target

Use a separate estimation mesh k and h=1/k; m above is a probability-proof mesh, not observed data. Let b_ij be candidate cell-average densities. Solve finite linear programs with bounds 1/2<=b_ij<=3/2, row/column sums k, and corner cumulative constraints

    |h^2 sum_(i<p,j<q) b_ij - A_P(ph,qh)| <= a,  0<=p,q<=k.

The true cell averages of rho composed with the good global S satisfy these constraints. Optional translated-cell Lipschitz inequalities can shrink the feasible set; any rounded constants must be outward bounds to preserve feasibility. They are unnecessary for the baseline proof. Empty feasibility indicates invalid input, numerical failure or an exceptional sample; never silently reduce a to repair it. Account for solver tolerances by enlarging the claimed a and checking returned constraints/certificates.

For any feasible b and true aligned cell averages c, each corner CDF differs by <=2a. Four-corner inclusion-exclusion implies |b_ij-c_ij|<=8a/h^2. For any point in that cell, Lipschitz regularity gives |rho(Sx)-c_ij|<=2 sqrt(2)h. Hence the histogram has simultaneous supremum error

    min(1, 8a/h^2 + 2 sqrt(2)h)

under one global S. This is an ordinary mathematical derivation, not a Lean export. A histogram need not belong to smooth K, so describe coefficient error explicitly rather than call it a smooth conformal metric. Half-open cells with top/right endpoints included define the output everywhere. Cellwise LP minima/maxima expanded by 2 sqrt(2)h give simultaneous pointwise bands, clipped to [1/2,3/2]. No pointwise switching between axes is allowed. Choosing k of order a^(-1/3) retains the existing (log n/n)^(1/6) rate; usefulness requires much sharper constants or data-dependent constraints with proved coverage.

## Execution and paper decision

1. Implement and certify the order-only realizer; compare against exhaustive tiny-order realizers and include adversarial invalid inputs. Separate graph algorithm cost, storage and LP cost.
2. Implement corner-CDF construction, LP feasibility and certified simultaneous bands. Derive rounding/tolerance effects before coverage claims.
3. Test flat and nonconstant copulas, including rho=1+c(2u-1)(2v-1), |c|<=1/2. Retain seeds, sample sizes, failure/coverage counts with binomial uncertainty, width, coefficient error after one best global transpose, runtime and memory. Latent data is for evaluation only.
4. Seek sharper uniform module/rank bounds, calibration or an information lower bound. Fully observed density-estimation lower bounds do not transfer as an asserted rate without a theorem for this uniform-marginal subclass and a justified data-processing argument.
5. New-paper go/no-go: require a substantive new theorem (sharper guaranteed rate, useful finite constants or justified limits) or a certified practical method with meaningful uncertainty and a defensible contribution beyond the baseline corollary. Simulation coverage alone does not prove uniform coverage.

Missing/noisy order edges, dependent sampling, higher dimensions, curvature and physical applications are deferred because each changes the model and proof obligations. Scope is complete; implementation and a new publication are not authorized by a claim that this plan is already a result. All future Lean development/acceptance runs must use the existing remote GCP protocol.

Remaining to-do list: implement and certify the realizer/LP procedure; establish useful bounds and evaluate the new-paper gate. These are future research tasks, not unfinished scoping.
