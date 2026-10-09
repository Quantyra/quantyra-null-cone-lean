# A degree-trimming lemma and an order-only fourth-root bound

S031 theoretical feasibility assessment, 2026-10-08. **Ordinary mathematical proof; not Lean certified and not an implemented/piloted estimator.** The frozen pilot continues to test only its original Bernstein/binomial LP candidates. The construction here identifies a distinct boundary-handling handoff for a separately scoped continuation; it does not replace that pilot or attribute this rate to its code.

The important difference is local: a count of discarded points divided by cell area can destroy a density rate. Observed predecessor/successor counts let us discard unreliable boundary points while knowing that **no true point in a selected interior cell was discarded**. This uses the already proved geometric rank theorem, rather than assuming that the pilot's observed unresolved degrees have a favorable distribution.

## Statement

For every integer n>=2 there is a measurable estimator from one directed-order isomorphism class, with output a bounded measurable histogram extended to the whole square, such that for every rho in the original K,

    Pr_rho{ min_(S in {id,transpose}) ||estimator-rho composed S||_infinity
             <= min(1/2, 650 (log(n)/n)^(1/4)) } >= 19/20.

One global S works everywhere. The output need not be smooth or have uniform marginals. The theorem is a statistical existence/explicit-construction statement, not a claim of practical computation at the very large n where these conservative constants become informative. It uses no stronger smoothness, independent coordinate ranks, multiple observed orders, or latent estimator input.

## 1. Fixed parameters and procedure

Put x_n=sqrt(n/(8 log n)) and m=floor(x_n). If m<65536, output the flat density 1. Otherwise define

    r=1/m, h=sqrt(r), H=8h, s=32r, k=floor(sqrt(m)),
    ell=(1-2H)/k.

If 270h>=1/2, also output 1. The remaining steps are only needed otherwise, but the proof below applies whenever m>=65536. Both choices are fixed from n before seeing data.

Choose any two-order realizer of the observed poset and normalize its inclusive ranks by n, obtaining r_i in [0,1]². Invalid inputs can return 1. Define the order-invariant retained set

    T={i: number of strict predecessors of i >6rn
             and number of strict successors of i >6rn}.

Partition the inner square [H,1-H]² into k² equal cells of side ell. In a cell R put

    b_R = #{i in T:r_i in R}/(n ell²).

The denominator is n, **not |T|**. Clip b_R to [1/2,3/2]. For an arbitrary point y in the full square, clamp each coordinate into [H,1-H] and use the cell value at that clamped point. Assign shared boundaries consistently (lower faces to the first cell, otherwise intervals open on the left and closed on the right). All continuity/error arguments below hold on cell closures, so the convention does not lose boundary coverage.

For an isomorphism class, choose a canonical labeled representative by finite lexicographic enumeration, then a fixed realizer of it. These operations use only the finite observation. The bound actually holds for every permitted realizer/enumeration, so it does not rely on the particular canonical choice. A function on this finite observation space is measurable. Existence of a realizer follows because every sampled order has dimension at most two.

## 2. The existing geometric event

Let E be the event that every open m-grid cell is occupied, the empirical anchored CDF differs from the population CDF by at most r at every grid vertex, and sample coordinates have no ties or fixed boundary hits. The last conditions have probability one under K. The accepted occupancy/concentration construction gives

    Pr(E complement) <= m² exp(-nr²/2)
                          +2(m+1)² exp(-2nr²).

On E, marginal empirical CDF errors at arbitrary thresholds are <=2r; the joint CDF error is <=3r. The fraction outside J=[4r,1-4r]² is <=20r, using the four marginal tails at the grid thresholds 4r and 1-4r. The accepted `finite_realizer_rank_rigidity` theorem then supplies one global S for which every point in J has rank error <=30rn in **both** rankings. Its true inclusive normalized rank is within 2r of its coordinate. Consequently

    ||r_i-S z_i||_infinity <=32r=s, for every z_i in J.

This is exactly the existing interior theorem, not an unproved all-vertex extension. Adding one to both predecessor ranks gives inclusive ranks without changing their difference. The source dependencies are [Bridges.lean](../QuantyraNullCone/Bridges.lean), [GridAccuracy.lean](../QuantyraNullCone/GridAccuracy.lean), the occupancy/concentration event in [GoodSamples.lean](../QuantyraNullCone/GoodSamples.lean) (from Sampling and Concentration), and [LogGridRate.lean](../QuantyraNullCone/LogGridRate.lean). Their existing GCP acceptance does not certify the new degree/filter/counting argument below.

## 3. Observable degree trimming removes the boundary penalty

If a sample point has u<4r or v<4r, its predecessor count is at most 5rn: all predecessors lie in the corresponding marginal lower tail, whose empirical mass at the grid threshold 4r is <=4r+r. If it has u>1-4r or v>1-4r, its successor count is at most 5rn by the analogous upper tail. Therefore, on E,

    i in T implies z_i in J.

The converse is not asserted for all of J. Instead, every point in the smaller square D=[7h,1-7h]² belongs to T. To see this, the lower density bound gives population southwest mass at least u v/2 and northeast mass at least (1-u)(1-v)/2. For a sample point in D both are at least 49r/2. Strict predecessor count divided by n is C_emp(u,v)-1/n, because the inclusive anchored CDF counts the point itself. Thus

    predecessors/n >=49r/2-3r-1/n >6r.

The strict successor fraction is exactly 1-F_emp,u(u)-F_emp,v(v)+C_emp(u,v); its population error is <=2r+2r+3r=7r. Hence

    successors/n >=49r/2-7r >6r.

Here 1/n<=r: m²<=n/(8 log n), log n>=1/2, and m>=1 imply n>=m. These comparisons include the self-count correction and require no independence among degrees or retained points. They establish

    {i:z_i in D} subset T subset {i:z_i in J}, on E.

Both squares and T are invariant under transpose. The same S from Section 2 therefore aligns all retained points and all forthcoming cell claims.

## 4. Fixed-cell concentration with no discarded-mass term

Since m>=65536, h<=1/256, k is between sqrt(m)/2 and sqrt(m), and

    (15/16)h <= ell <=2h,
    2s=64h² <=h/4 <ell,
    H-s >=(63/8)h >7h.

For each inner cell R let R^- shrink every side by s and R^+ expand every side by s. These rectangles are nonempty and contained in D (including their closures). They are deterministic functions of n, and the collection of 2k² rectangles is closed under transpose.

Every true point in R^- is retained, and its recovered point lies in R. Every recovered retained point in R has its aligned true point in R^+. Consequently, on E,

    N_(S R^-)/n <= #{i in T:r_i in R}/n <= N_(S R^+)/n.

Use strict inner lower endpoints and closed outer endpoints if needed for deterministic set inclusion. For latent counts these choices have identical masses and agree almost surely, since the finitely many boundaries are fixed null lines. Unlike the pilot's generic trimmed bracket, **there is no +b_T term**: the left inclusion uses the proved fact that all true points in the relevant cell are retained, and the right inclusion uses coordinate control of every retained point.

Each latent rectangle count is a sum of iid Bernoulli variables. Its population mass is at most

    (3/2)(ell+2s)² <=(3/2)(9h/4)²=(243/32)r <8r.

Apply the elementary B1 Bernstein inequality proved in [the local-mass note](finite-data-local-mass-feasibility.md), with variance upper bound v=8r and e=4r^(3/2). Because r<=1,

    n e²/[2(v+e/3)] >=(6/7)nr² >=(48/7)log n >=6 log n.

A union over both tails of the 2k² rectangles gives an event F on which every rectangle count differs from its population mass by <=e, with

    Pr(F complement) <=4k² n^(-6) <=4n^(-5).

The random S costs no further union: the fixed rectangle family already contains its transpose. There is no claim that reconstructed or retained points are iid, and no independence between E and F is used.

## 5. Density error, boundaries, constants

Write p_R for the true aligned mass in R. Since rho<=3/2, expanding a square of side ell by s changes its mass by at most

    (3/2)[(ell+2s)²-ell²]=6ell s+6s².

The contraction loss is no larger. On E intersect F the preceding count bracket therefore implies

    |b_R-p_R/ell²| <=6s/ell+6(s/ell)²+4h³/ell².

Using ell>=(15/16)h, s=32h² and h<=1/256 bounds the right side by

    [3072/15 + 6144/225 + 1024/225]h = (53248/225)h.

At a point in the cell closure, the true value differs from its average by <=2ell<=4h. One justification of the 2ell bound is Jensen applied to distance from a point to a uniform point in its square: the largest mean squared distance is (2/3)ell², attained at a corner; the Lipschitz constant is two. Clamping a point of the unit square into the inner square moves it by at most sqrt(2)H, producing an additional error <=16 sqrt(2)h<24h. Clipping the estimate to the known density range cannot increase its error. Thus over the **entire closed square**, under the same S,

    ||estimator-rho composed S||_infinity
        <=(59548/225)h <270h.

The logarithmic grid calculation gives

    Pr(E complement) <=1/(8n³)+1/n^15.

Indeed nr²>=8 log n, m²<=n/8, and 2(m+1)²<=8m²<=n. Combining this with F gives failure <=1/(8n³)+1/n^15+4/n^5<1/20 (already true at n>=4; the active branch has n>=4m²). This derives the finite confidence statement without hiding an asymptotic probability or a realizer-ambiguity hypothesis.

If the procedure selected the flat output, its error is deterministically <=1/2. Otherwise the bound is <=270h with probability >=19/20. For m>=65536, floor(x_n)>=x_n/2 implies

    270h <=270 sqrt(2) 8^(1/4) (log n/n)^(1/4)
          <650 (log n/n)^(1/4).

The final strict constant comparison follows from 32*270^4<650^4. If m<65536 then x_n<65536, so 650(log n/n)^(1/4)>650/(8^(1/4)*256)>1/2. Hence that fallback also satisfies the stated minimum bound. These facts prove Section 1's all-n>=2 result, including the adaptive flat/nonflat choice made solely from n.

Simultaneous bands can be formed by adding/subtracting the proved radius around the selected estimator and clipping to [1/2,3/2]. Their midpoint also has error at most that radius on the same event. These mathematical bands are not reports from the pilot's rational LP checker.

## 6. Optional law-separation consequence

Let R_n=min(1/2,650(log n/n)^(1/4)). For two densities in K, apply the **same** order-only estimator to their actual unlabeled n-point order laws. If their TV distance is less than 9/10, the two success sets overlap: transporting the first probability to the second law and intersecting leaves mass at least 9/10-TV>0. On an observation in that intersection, the quotient triangle inequality yields d_conf(rho,sigma)<=2R_n. If TV>=9/10, use d_conf<=1. Therefore

    d_conf(rho,sigma) <= min(1, 1300(log n/n)^(1/4)+(10/9)TV(pi_n^rho,pi_n^sigma)).

This is an ordinary corollary for the actual law experiment, not an estimate of TV from a single sample. It does not alter either published manuscript or an accepted Lean theorem.

## Feasibility disposition and handoff boundary

The substantive new obligation identified here is the degree-trimming/deep-cell inclusion lemma and its use to eliminate the global missing-mass term. The preceding sections supply its ordinary proof and finite constant/probability assembly. This is a stronger **theoretical** route than the old CDF-to-density one-sixth-power estimator corollary, even though its constants provide no practical success at the pilot sizes.

The [information-limit construction](finite-data-information-limit.md) gives a same-class n^(-1/4) obstruction for fixed confidence. Together these bounds match the polynomial exponent, leaving a logarithmic gap; they do not prove an exact minimax rate or an additional order-only information cost. The [primary-source comparison](finite-data-feasibility-comparison.md) establishes relevant rank/copula precedents, not priority of this composition. The bounded inspected sources do not already state this finite full-K order-only guarantee; broader originality remains provisional.

This changed boundary-handling construction requires its **own continuation scope** before implementation, numerical expansion, Lean certification or publication. S031 supplies the mathematical feasibility evidence and handoff; it runs no third calibration, higher mesh, larger sample or new estimator campaign. The old pilot cannot confirm this rate, and its failures cannot refute this theorem. Next review/certification must check the degree/self-count identities, fixed-rectangle inclusions, one-orientation measurability, constant/fallback assembly and optional TV corollary against the exact accepted foundations. Every Lean/Lake invocation remains remote GCP-only.
