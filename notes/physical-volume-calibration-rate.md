# A joint finite rate for physical volume and detector calibration

2026-10-09, S046. This ordinary derivation resolves the selected candidate scale in the original geometric class, with the full marked-order observation and arbitrary independent estimator randomization. **It is not yet Lean-certified.** Primary-source comparisons, exact-source GCP acceptance and manuscript disposition remain required. The [frozen pilot](marked-volume-pilot-result.md) is unchanged; no new empirical-performance or novelty claim is made.

## Experiment and statement

Use the original class K: smooth densities on a neighborhood of the null square, values in [1/2,3/2], Euclidean Lipschitz constant at most 2, and both marginals uniform. Fix marked anchors (0,0) and (1/2,1/2) independently of the sample. Their interval is A=(0,1/2)^2, with physical normalized volume v=integral_A rho.

For known R in [1,2], the unknown measurable detector satisfies 1/R<=pi<=1. Observe the full strict directed order of n retained iid events and the two marked anchors, modulo sample-label permutations. The retained density is pi*rho / integral(pi*rho). Coordinates, detector values and rejected/generated counts are unavailable. The [S040 process argument](independent-thinning-process.md) provides the separate independent-detection interpretation.

For n>=1 define

    a_n=1/sqrt(n),  b_R=(R-1)/(R+1),  s(n,R)=min(1,a_n+b_R).

One observable estimator T satisfies, for every admissible model,

    Pr{|T-v| > 2 s(n,R)} <= 1/20.

Conversely, for every measurable estimator and arbitrary independent probability seed law, some admissible model satisfies

    Pr{|T-v| > s(n,R)/256} >= 1/4.

The constants are uniform in n and R, including R=1 and sequences approaching it. This determines the fixed-confidence minimax scale up to constants, not a sharp identified set or optimal interval length.

## Upper bound

Let theta be the retained probability of A and T=K/n its observed membership fraction. It is available from the full marked order and invariant under relabeling. The accepted finite concentration theorem gives

    Pr{|T-theta| > sqrt(2/n)} <= 2 exp(-4) <= 1/20.

The accepted retention transforms give

    theta/(R-(R-1)theta) <= v <= R theta/(1+(R-1)theta).

Each endpoint differs from theta by at most b_R. For R>1, cross-multiplication reduces the two required inequalities respectively to

    R(1-theta)^2+theta^2 >= 0,
    (1-theta)^2+R theta^2 >= 0.

All denominators are positive. At R=1 the transforms equal theta directly. Thus |theta-v|<=b_R. On the concentration event, error is at most sqrt(2)a_n+b_R<=2(a_n+b_R). Because T,v lie in [0,1], error is also at most one, yielding min(1,2(a_n+b_R))<=2s(n,R). This proves the upper statement. The existing exact-binomial report can be substantially tighter than this convenient bound.

## Geometric alternatives

Set f(t)=2t-1 and, for 0<=epsilon<=1/2,

    rho_epsilon(u,v)=1+epsilon f(u)f(v).

These polynomials are smooth. On the square their values lie in [1-epsilon,1+epsilon], and both marginals are one because integral_0^1 f=0. Expanding a difference of products gives, for p,q in the square,

    |rho_epsilon(p)-rho_epsilon(q)|
      <= 2 epsilon (|p_1-q_1|+|p_2-q_2|)
      <= 4 epsilon sqrt((p_1-q_1)^2+(p_2-q_2)^2)
      <= 2 sqrt((p_1-q_1)^2+(p_2-q_2)^2).

Every alternative therefore belongs to the unchanged K. Since integral_0^(1/2) f=-1/4, its target is exactly

    v_epsilon=1/4+epsilon/16.                         (1)

Positive conformal scaling leaves chronology unchanged. The anchors and residual coordinate transpose preserve this target.

## Sampling lower bound

For n>=1 take epsilon=1/(2sqrt(n)) and detector pi=1 in both the flat and alternative models. This is admissible for every allowed R. Compare the stronger experiment supplying all n coordinates. Relative to the flat product law, the likelihood is L=product_i rho_epsilon(X_i). Independence and integral_0^1 f^2=1/3 give

    E_0 L=1,
    E_0 L^2=(1+epsilon^2/9)^n,
    E_0 (L-1)^2=(1+1/(36n))^n-1.                    (2)

This divergence is at most 1/35 by a finite argument. For x=1/(36n), Bernoulli's inequality gives (1-x)^n>=1-nx=35/36, while

    (1+x)^n(1-x)^n=(1-x^2)^n<=1.

All factors are nonnegative, so (1+x)^n<=36/35. Cauchy-Schwarz bounds coordinate-law total variation by

    (1/2) E_0 |L-1| <= (1/2)sqrt(1/35) < 1/4.       (3)

The complete marked observation is a common measurable function of the sample: all pairwise chronology, all anchor flags and the finite sample-label quotient. Its total variation is no larger. Adding any common independent seed preserves this bound, as follows by integrating event sections against its probability law.

The target gap in (1) is a_n/32. Success events with radius a_n/128 are disjoint because twice that radius is strictly below the gap. For the two input laws and disjoint success events,

    P_0(E_0)+P_1(E_1) <= 1+TV(P_0,P_1) < 5/4.

Failure probabilities therefore sum to more than 3/4. Some model has strict error greater than a_n/128 with probability at least 3/8. This applies to the full marked-order experiment and arbitrary independent randomization; it does not discard potentially informative relations in deriving the lower bound.

## Detector lower bound

For R>1 take epsilon=b_R, which lies in (0,1/3]. Compare rho_0=1 with rho_epsilon and detectors

    pi_0=1-epsilon,  pi_epsilon=(1-epsilon)/rho_epsilon.

Both lie in [1/R,1]. The second's minimum is (1-epsilon)/(1+epsilon)=1/R and maximum is one; the first equals 2/(R+1)>=1/R. If Lean represents the density on the ambient plane, extend both detectors outside the square by the valid constant 1-epsilon. This leaves the supported experiment unchanged.

In both models the unnormalized retained density equals 1-epsilon pointwise on the square. The normalized retained coordinate laws are therefore identical flat laws. So are the full marked-order laws for every n, including any common independent seed. Equality of the generated-process experiments additionally uses S040's process construction.

The target gap is b_R/16. Success events of radius b_R/64 are disjoint under the common law, so one model has strict error exceeding b_R/64 with probability at least one half. At R=1 this pair has zero separation; the sampling argument remains available.

## Joint result and no-data case

If a_n>=b_R, then s(n,R)/256<=a_n/128 and the sampling pair applies. Otherwise b_R>a_n>0 and s(n,R)/256<=b_R/128<b_R/64, so the detector pair applies. Both alternatives respect the same n, R, geometric class and full observation. This proves the uniform lower statement, including when R depends on n.

For n=0, the constant estimate 1/4 has deterministic error at most 1/8 because v lies in [1/8,3/8]. The flat and epsilon=1/2 models with detector one have identical empty-sample marked observations and target gap 1/32. Their success events at radius 1/128 are disjoint, giving failure probability at least one half for some model under every independently randomized estimator. This is a separate no-data statement.

## Consequences and formal obligations

The crossover is n^(-1/2) comparable to (R-1)/(R+1). Fixed nonzero detector uncertainty prevents uniform error from vanishing, even when all causal relations are used. Keeping the sample-limited order requires detector uncertainty to decrease at order n^(-1/2) or faster. This is a statistical tradeoff, not a monetary optimum or physical sensor validation. The loose constants do not replace the tighter frozen confidence-report comparisons.

Formalization must cover actual K admissibility and target integrals; the iid likelihood and product divergence; data processing to the complete marked quotient; testing with arbitrary independent seeds; detector validity and exact law equality for every R; upper composition, joint case split and zero samples. Reusing the old unmarked lower theorem without these bridges is insufficient. S040 certification remains required for the physical process interpretation.

The planning source audit still records unresolved direct Aronow-Lee access and edition checks. Partial identification and bounded-selection estimation are established topics; the potential contribution here is the finite geometric, full-observation guarantee and its certification. No shortest-interval, exact-minimax-constant or improved empirical-performance claim is made.

Remaining to-do list: complete primary-proof comparisons; formalize and GCP-certify the substantive endpoints; validate the final finite formulas; decide manuscript placement and verify delivery. S046 remains incomplete.
