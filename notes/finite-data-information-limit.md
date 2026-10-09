# A finite information limit inside the original class

S031, 2026-10-08. Ordinary self-contained mathematical argument; not Lean certified. This is a standard two-point lower-bound construction adapted to the exact K and quotient loss. It is **not** evidence of an extra cost of observing only order or a matching minimax rate.

## Model and alternatives

For integer n >= 1 put h = min(1/2, n^(-1/4)), f(t) = t exp(-t²), and

    a_h(x) = f((x-1/2)/h),
    rho_0(u,v) = 1,
    rho_1(u,v) = 1 + 2h a_h(u) a_h(v).

Both are smooth on all of R². Oddness about 1/2 makes the integral of a_h on [0,1] exactly zero, so every row and column integral of either density is one. In particular normalization is exact, not numerical.

The maximum of |f| is 1/sqrt(2e) < 1/2, attained at t = +/-1/sqrt(2). Its derivative (1-2t²) exp(-t²) has absolute value at most one: for t² <= 1/2 this is immediate; on the complement its maximum is 2 exp(-3/2) < 1. Hence |rho_1-1| <= h/2 <= 1/4 and each first partial derivative of rho_1 has magnitude at most one. The Euclidean gradient norm is at most sqrt(2) < 2, so the mean-value integral along a segment proves the required Euclidean Lipschitz bound. Both alternatives lie in the **full original K**; no closure argument is needed.

Since h <= 1/2, the points 1/2 +/- h/sqrt(2) lie in the square. Therefore

    ||rho_1-rho_0||_infinity = h/e.

Both densities are invariant under coordinate transpose. Their distance modulo G={id,transpose} is thus also h/e, not zero. Let r=h/6. Because e<3, their quotient separation is strictly greater than 2r. The familiar e<3 bound follows from its series: the terms from 1/2! onward sum to less than sum_(j>=1) 2^(-j)=1.

## Divergence and the actual observation

Let Q_i be the one-point coordinate distribution with density rho_i. Against Q_0, which is uniform,

    chi²(Q_1,Q_0) = integral (rho_1-1)²
      = 4h² (integral_0^1 a_h(x)² dx)²
      <= 4h^4 (integral_R t² exp(-2t²) dt)²
      = (pi/8) h^4.

The Gaussian integral in this display is sqrt(pi)/(4 sqrt(2)), obtained by differentiating integral exp(-b t²) dt = sqrt(pi/b) at b=2 (or by integration by parts). The truncated integral is bounded by the whole-line integral because its integrand is nonnegative.

For the n-fold coordinate experiment, multiplying likelihood ratios and using independence gives the exact identity

    1 + chi²(Q_1^n,Q_0^n) = (1 + chi²(Q_1,Q_0))^n
      <= exp(n pi h^4/8).

Cauchy–Schwarz applied to TV = (1/2) integral |dQ_1^n/dQ_0^n-1| dQ_0^n yields

    TV(Q_1^n,Q_0^n) <= (1/2) sqrt(exp(n pi h^4/8)-1).

Define T on the coordinate sample by all predicates u_i<u_j and v_i<v_j, followed by quotienting the finite directed graph by vertex relabeling. This is a measurable map into a finite set: each labeled event is a finite intersection of Borel inequalities, and each isomorphism class is a finite union. The actual observation laws in the study are pi_n^rho_i = T_* Q_i^n. Pulling back any order event proves TV cannot increase. Consequently the same displayed upper bound applies to their TV. No independent-suborder approximation is used. The same argument even applies to estimators given the labeled order, which is a more informative experiment.

Here n h^4 <= 1 and pi<4, so n pi h^4/8 < 1/2. Also exp(1/2)<2. Thus this TV upper bound is strictly less than 1/2. Constants are deliberately conservative.

## Testing reduction, including endpoints

For a bounded measurable estimator output b, write d_i(b)=min_(S in G)||b-rho_i composed S||_infinity. Sup norm is invariant under transpose, and composition within G proves the quotient triangle inequality. Therefore d_0(b)<=r and d_1(b)<=r cannot both hold. Measurability is an explicit estimator requirement; histograms and finite-order deterministic reports satisfy it. Arbitrary measurable randomized estimators are covered by adjoining their independent random seed, which does not increase TV.

Test hypothesis zero when d_0(b)<=r, and hypothesis one otherwise. Under zero, its error event is exactly {d_0(b)>r}. Under one, its error event is a subset of {d_1(b)>r}. For any test with zero-decision event A,

    Q_0(A complement) + Q_1(A)
      = 1 - (Q_0(A)-Q_1(A)) >= 1-TV(Q_0,Q_1).

Apply this to the two **order** laws and then take the maximum of the estimation risks. For every estimator,

    max_i Pr_(rho_i){loss(b,rho_i)>h/6}
      >= (1 - (1/2)sqrt(exp(n pi h^4/8)-1))/2 > 1/4.

The strict-error version avoids confusion between a confidence guarantee at <=r and a lower bound stated only at >=r. It also implies the weak-error version requested in the specification. Taking an infimum over estimators preserves the explicit non-strict lower bound, which is greater than 1/4. Since these two alternatives belong to K, the supremum over K is at least this large. For n>=16 the forbidden uniform 95% radius is n^(-1/4)/6. Equivalently no method can give uniform error probability <=1/20 at that radius.

If simultaneous bands have maximum width <=2r on **every** output, their midpoint is an estimator with loss <=r on the coverage event, contradicting this bound. If width is random, the valid consequence is instead

    max_i [Pr_i{coverage fails} + Pr_i{maximum width>2r}] >= the bound above.

This does not forbid occasional narrow accepted reports and says nothing about coverage conditional on acceptance. It is not an expected-risk statement; an expected-risk consequence follows separately by multiplying the probability lower bound by r.

## Interpretation and unresolved extensions

The lower bound scales as n^(-1/4) for n>=16, but does not establish the logarithmic factor appropriate to a sharp uniform estimation rate. A multi-alternative packing argument would be needed to examine that question. Matching it to an upper bound would also require uniform probability control of order/realizer ambiguity. Neither is supplied here.

At n=3072, r is about 0.0224. This is far below the study's practical radius 0.45. Consequently this result cannot explain vacuous bands at the pilot size or prove that the practical target is impossible. It remains valid even with full coordinate observations: this is a **generic transferred information limit**, not an order-specific obstruction and not sufficient by itself to justify a third paper under the frozen decision rule.
