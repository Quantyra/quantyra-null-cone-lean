# Local-cell-mass coverage argument and checker contract

S031, 2026-10-08. Ordinary mathematical guarantee, subject to the specified checker; new Lean certification is not claimed. The [primary-source comparison](finite-data-feasibility-comparison.md) precedes implementation. Only B1 Bernstein and B2 exact binomial inversion are assessed. Before any pilot sample, fix k=8, delta=1/20 and delta_m=delta_cell=delta/2. No tuning on latent coverage or error is permitted.

## One orientation and retained counts

Reuse the checked original-incomparability-graph forcing tree and realizer intersection. Its soundness gives one axis orientation S under which the recovered ranks and true coordinate ranks differ by at most d_i, the number of unresolved incomparable neighbors at vertex i. The reason is deterministic: comparable pairs agree, the rooted forcing class has a common orientation in every realizer after S, and only unresolved neighbors can change a vertex's predecessor count. This holds for every enumerated realizer, including a data-dependent one. If the tree is empty, d_i counts all incomparable neighbors and either orientation suffices. A deletion-graph class cannot replace this original-graph witness.

Let r_i be the two recovered ranks divided by n. Sharp two-sided marginal DKW and a union over the two coordinates give an event E_m with failure <=4 exp(-2n e_m²). Uniform marginals imply that on this event each latent coordinate differs from its empirical normalized rank by <=e_m. Thus for every cutoff j, retained set I_j={i:d_i<=j}, and retained point,

    ||r_i-S z_i||_infinity <= s_j = j/n+e_m.

The SAME S works for every j and cell. No independence between S, I_j and the sample is assumed.

Partition [0,1] into (a,b], assigning zero to the first interval. For a fixed cell R with coordinate intervals (a,b], the inner test in each axis is r>a+s if a>0 and r<=b-s if b<1; there is no restriction at a=0 or b=1. The outer test is the conservative closed interval a-s<=r<=b+s, clipped implicitly to [0,1]. Their products define R^-s and R^+s. Empty inner intervals contribute zero; s>=1 is allowed. At sample ties/fixed internal boundaries the original continuous sampling law has probability zero; the strict inner lower endpoint also handles deterministic inequalities conservatively. The first interval contains zero by convention.

On E_m, every retained reconstructed point in R^-s_j has S z_i in R, and every retained point with S z_i in R has r_i in R^+s_j. Therefore, writing N_(S R) for the latent count,

    l_R = max_j #{i in I_j:r_i in R^-s_j}
      <= N_(S R)
      <= u_R = min_j [#{i in I_j:r_i in R^+s_j}+n-|I_j|].

Cap u_R at n. Cutoffs need only be zero and the distinct degrees: between degree changes the retained set is fixed while erosion shrinks and dilation grows. The leftmost cutoff dominates every later cutoff in that stretch. These optimizations are deterministic on ONE event; no cutoff union penalty is needed.

## B1: finite Bernstein calibration

For each fixed latent cell, X=N_R is Binomial(n,p_R) with p_R<=v=min(1,3/(2k²)). Use v as a variance upper bound. If Y is its centered single indicator, |Y|<=1 and E|Y|^m<=E Y²<=v for integer m>=2. Since m!>=2*3^(m-2), for 0<t<3 the exponential series gives

    log E exp(tY) <= v t²/[2(1-t/3)].

The same bound holds for -Y. Independence across points, Markov's inequality, and the choice t=e/(v+e/3)<3 yield

    Pr{|X/n-p_R|>e} <= 2 exp[-n e²/(2(v+e/3))].

For the k² fixed cells a union bound multiplies this by k². Choose a rational e_c with that union bound <=delta_cell and set

    mass_lower_R = max(0,l_R/n-e_c),
    mass_upper_R = min(1,u_R/n+e_c).

This proof uses **latent fixed-cell indicators**, not reconstructed coordinates or the trimmed sample as independent observations. Dependence among different cell counts is harmless for the union bound. If a useful rational calibration cannot be obtained, [0,1] mass restrictions remain deterministic.

Both exponential calibrations use exp(-t) <= (1+t/512)^(-512), an exact rational upper bound from exp(x)>=1+x. Searching rational tolerances on a 10^-6 grid is only a proposal step; the checker verifies the actual inequalities and budgets. It does not trust the search or floating logarithms. Parameter domain: integer n>=1, 1<=k<=16, 0<delta<1, within supported input limits.

## B2: exact binomial tails

Let alpha=delta_cell/(2k²). For an integer x define a lower endpoint L(x) in [0,1] such that L(0)=0 and, for x>0, Pr_(Bin(n,L(x))){X>=x}<=alpha. For the upper endpoint U(x), let U(n)=1 and otherwise require Pr_(Bin(n,U(x))){X<=x}<=alpha. Choose endpoints outward from the exact roots on the rational grid with denominator 2^20.

Binomial upper tails increase with p and lower tails decrease with p (couple each indicator by a common uniform variable). These facts prove L and U are nondecreasing in x. More directly, under a true p the event L(X)>p implies that X lies in an upper rejection tail of probability <=alpha; similarly U(X)<p lies in a lower rejection tail. Thus p belongs to [L(X),U(X)] except on a set of probability <=2alpha. A union over fixed cells gives failure <=delta_cell.

Use [L(l_R),U(u_R)] as the observed mass interval. Because l_R<=N_(S R)<=u_R, monotonicity transports the fixed-cell coverage event to these endpoints. The rational checker can alternatively validate the tail inequalities directly at l_R/u_R: an endpoint excluding the true p implies rejection at the actual latent count as well. Therefore a recomputed search is not a trusted component.

For p=a/b, the tail probabilities are finite sums of integers binom(n,t) a^t(b-a)^(n-t), divided by b^n. Integer recurrence and cross-multiplication with alpha make the check exact; zero/one endpoints and x=0,n are explicit. SciPy quantiles or floating probabilities are not certificates. Unlike an extra calibration search, selecting j costs no additional probability budget. B1 and B2 are evaluated as **separate** 95% procedures; taking an unallocated intersection of their outputs is not authorized.

## Selection, LP and full-square output

The k by k grid is closed under transpose. Its fixed-cell event includes R and S R regardless of the data-dependent choice of S. Intersecting E_m with the selected B1 or B2 event has failure <=delta. This controls every cutoff, cell and enumerated realizer at once. The allocation, grid and calibration variant are fixed before a run. No asymptotic realizer-probability rate is inferred from observed degrees.

Let z_R=k² integral_R rho(Sx) dx. The true cell averages lie in [1/2,3/2], each row and column sums to k, and neighboring averages differ by <=2/k, by translation of neighboring cells and the Euclidean Lipschitz bound. Add k² times the local mass lower/upper restrictions. This is a finite outer relaxation, not a claim that every feasible histogram is a smooth member of K.

For each signed coordinate objective, the existing rational weak-duality checker validates nonpositive inequality multipliers, unrestricted equality multipliers and exact residual correction on the known box. Thus numerical solver proposals cannot shrink the band unjustifiably. Solver failure, contradictory bounds, invalid input/certificate, timeout or memory rejection produce the documented full-range fallback with histogram 1 and deterministic radius 1/2; acceptance and fallback are counted separately. The study wrapper retains failures instead of dropping their samples.

Expand each certified average band by 2/k and clip to [1/2,3/2]. For any point x in the cell, the cell-average distance bound is <=2/k: in scaled coordinates, Jensen gives E||x-Y|| <= sqrt(E||x-Y||²)<=sqrt(2/3)<1, since the maximum mean squared distance is at a corner. Multiply by the Lipschitz constant 2 and cell side 1/k. Continuity extends the bound to each cell closure; the partition convention assigns its shared edges a unique reported value. The midpoint of these **point** bands is the output estimator and its certified global error is half their maximum width on the same coverage event. It need not satisfy the cell-average LP or belong to smooth K.

Consequently the proposed procedure has unconditional full-square simultaneous coverage >=1-delta over full K, under one global S. The finite observation space makes a deterministic checked report selector measurable. Label changes may alter the selected report but cannot invalidate this statement, since it holds for every valid realizer. A canonical labeling is unnecessary for the guarantee.

## Internal proof audit before pilot

All dependencies used above are either the already accepted forcing/LP foundations, the inspected marginal DKW inequality, or the elementary finite inequalities proved here. The new bracket, Bernstein/binomial composition and new report checker have an ordinary proof only. Tests must exercise boundaries, all-realizer alignment on small orders, false tail certificates and false LP/report claims. They are runtime regression evidence, not proof of the probability theorem.

The comparison to the old route is structural: old corner-CDF uncertainty is amplified by differencing and k²; local mass constraints use observed boundary strips and cell-specific binomial variation instead. They can be stronger intermediate restrictions without improving maximum point-band width. B1's variance upper bound and B2's exact inversion are the only two initial variants. Remaining empirical obligation: execute the gated pilot, retain every result and decide whether fresh confirmation is warranted. Remaining theoretical extensions, outside this study: a useful uniform realizer rate, a sharper proved pointwise conversion, or a matching order-specific lower bound.
