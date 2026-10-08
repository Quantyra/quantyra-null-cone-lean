# Higher-dimensional feasibility: a gauge obstruction

2026-10-07, E002/S018. Decision: park a quantitative 2+1 Lorentzian extension until a valid gauge and a finite stability lemma are available. The naive density inverse modulo spatial rotations/reflections is false. Adding coordinate linear orders instead would give a product-order problem, not ordinary higher-dimensional Lorentzian chronology.

## Proposed model and failed target

Let D={ (t,x,y): |t|+sqrt(x^2+y^2)<1 }, eta=-dt^2+dx^2+dy^2 and V=2pi/3. Use normalized flat volume mu_0=dt dx dy/V. Let K_3 contain densities smooth on a neighborhood of the closed diamond with 1/2<=rho<=3/2, Euclidean Lipschitz constant <=2 and integral rho dmu_0=1. Set g_rho=V^(-2/3)rho^(2/3)eta, whose volume is rho dmu_0. Strict directed chronology is delta t>sqrt(delta x^2+delta y^2). Observe actual iid unlabeled finite-order laws, without identifying an order with its dual.

A tempting target is a vanishing finite inverse bound for

    d_rot(rho,sigma)=inf_(R in O(2)) ||rho-sigma composed with (t,R)||_infinity,

using Delta_N from those laws. The following example rules out any bound whose remainder tends to zero with N when Delta_N=0.

## Explicit smooth counterexample

For |a|<1 define r^2=x^2+y^2 and

    D_a=(1+at)^2-a^2 r^2,
    F_a(t,x,y)=(((t+a)(1+at)-a r^2)/D_a,
                (1-a^2)x/D_a, (1-a^2)y/D_a),
    Omega_a=(1-a^2)/D_a.

In radial null variables u=t+r and v=t-r, F_a sends each to f_a(z)=(z+a)/(1+az). Its derivative is positive, it fixes z=+-1, and its inverse is f_-a. Thus F_a preserves the diamond and time orientation. D_a>=(1-|a|)^2 on its closure, so the Cartesian formula is smooth on a neighborhood, including r=0; F_-a is its inverse. Radial null derivatives and the angular term both scale by Omega_a^2, giving F_a^*eta=Omega_a^2 eta. Consequently it preserves strict chronology in both directions and its positive Jacobian is Omega_a^3. These are analytic identities; finite checks below support the algebra, not the universal proof.

Take rho_0=1 and rho_a=Omega_-a^3. Change of variables gives rho_a mu_0=(F_a)_*mu_0 and its normalization. Coupling each iid point Z_i with F_a(Z_i) preserves every pair's chronological relation exactly. Therefore **all finite directed-order laws agree**, labeled as well as unlabeled.

For a=1/100 the density range is

    (99/101)^3 <= rho_a <= (101/99)^3,

which lies in [1/2,3/2]. Indeed, D_-a factors as (1-a(t+r))(1-a(t-r)), each factor in [1-a,1+a]. Further,

    ||gradient rho_a|| <= 6a (101/99)^3 (1+2a)/(1-a)^2 < 2.

This follows from gradient log rho_a=-3 gradient D_-a/D_-a and ||gradient D_-a||<=2a sqrt((1+a)^2+a^2)<=2a(1+2a). Convexity of the closed diamond makes the gradient bound a global Euclidean Lipschitz bound. Thus both densities are in K_3. The second density is radial, so spatial O(2) does not change it; at the future tip its value is (101/99)^3>1, also approached from the interior. Hence d_rot(1,rho_a)>0 although Delta_N=0 for every N.

This is a coordinate-gauge obstruction, not physical nonidentifiability: g_(rho_a)=F_-a^*g_1. The geometries are isometric. It is consistent with [Braun's qualitative reconstruction theorem](https://arxiv.org/abs/2507.01907), and it does not affect the published two-dimensional uniform-marginal gauge, which removes nonlinear independent null-coordinate reparametrizations.

## Repair obligations and stop decision

Either quotient by the full future-preserving conformal automorphism action (density transforms as J_F times sigma composed with F), or prove a normalization that selects representatives and characterize the residual group. A raw infimum of coefficient differences over this action need not be a symmetric metric: the action has nonconstant Jacobians and is noncompact. No metric, compactness argument or quantitative exponent is established merely by writing the quotient.

Then one needs a finite order-only anchor/coordinate reconstruction lemma with uniform probability, quantitative conditioning and a valid comparison norm. Neither a product-order k-realizer nor an infinite qualitative isometry theorem supplies it. The full Lorentzian route presently lacks this key finite lemma; promising an exponent would be speculative. A controlled gauge-normalized subfamily could reopen the question after its identifiability survives this flow and other conformal transformations.

The reproducible [rational algebra check](../checks/check_higher_dimensional_gauge.py) verifies inverse, Jacobian/conformal identities and chronological comparisons at explicit rational points, as well as exact conservative density/Lipschitz bounds. It is local Python, not Lean certification. The model, observable, proposed symmetries, error target and decisive counterexample complete the feasibility scope. Prioritize the [finite-data project](finite-data-follow-up-scope.md).

Remaining to-do list: none for feasibility. Reopening requires a justified gauge/metric and a credible finite reconstruction/stability lemma.

## Subsequent S025 certification

The [genuine 2+1 counterexample](higher-dimensional-certification.md) now has GCP root/type/axiom acceptance with actual volume/chronology, smooth map and derivative/Jacobian, density transport/class membership, all finite directed-order law equality, positive O(2) coordinate distance and the derived metric isometry. This supersedes the earlier Python-only verification status, while preserving the negative feasibility decision and its physical-claim boundary. The naive coordinate gauge remains invalid; no quantitative higher-dimensional inverse program is reopened.

Remaining to-do list: none for feasibility; S025 delivery closeout is recorded separately.
