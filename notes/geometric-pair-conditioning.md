# A restricted 2+1 route through pair probabilities

2026-10-10 continuation: the [complete ordinary pair audit](geometric-pair-audit.md) supersedes the selected constant and estimator route below. It proves the ordinary geometric factor `3/20`, selects an all-pairs U-statistic with a dependence-aware Bernstein bound, records relevant primary-proof comparisons and checks sufficient sample counts. The body below is preserved as the earlier calculation and randomized-matching alternative. New endpoints remain uncertified; S043 remains gated.

Subsequent progress: the general [density-to-geometric forward bound](geometric-density-forward-certification.md) now has 1,131-report GCP acceptance. The restricted family membership, pair-integral, inverse-conditioning and finite-observation/confidence arguments below retain their separate proof obligations.

S042 ordinary research, 2026-10-09 (Hawaii). **Not Lean certified; no S043 go decision.** This calculation tests a possible explicit finite route after the [full-class representation argument](geometric-diamond-representation.md). The original class and its nontrivial gauge remain part of S042. This one-parameter subclass does not replace full-class identifiability or supply its missing explicit inverse modulus.

## Controlled family and target

On the same genuine Lorentz diamond, let

    f(t)=t^2-1/10, rho_theta(t,x,y)=1+theta f(t), 0<=theta<=1/2.

Flat normalized time has density (3/2)(1-|t|)^2 on [-1,1], so its second moment is 1/10. The density is normalized and polynomial on a neighborhood. On the closed diamond it lies in [19/20,29/20] and its Euclidean gradient has norm at most one. Thus it belongs to the original smooth K3. Its chronological relation is the genuine spatial-norm light-cone inequality, not a three-axis product order.

Keep the geometric coupling-distortion loss d_G and its boundary quotient. The preceding ordinary forward estimate gives

    d_G(rho_theta,rho_phi) <= (9/10)|theta-phi|.

All latent coordinates and the parameterized family are model definitions; an estimator observes only one unlabeled directed order and, if used, an explicitly independent random seed. The geometric loss does not supply measured proper-time values or anchors. Total volume one is the same model scale convention.

## Exact ordered-pair calculation

Let q(theta)=P_theta(P precedes Q) for two independent samples. Write p=(t,x), r=|x|, b=1-t, and T^2=b^2-r^2. The future of p inside the diamond is the Alexandrov interval from p to the top tip. Its normalized flat volume is A(p)=T^3/8. This follows by a proper future Lorentz transformation to the rest interval: determinant has absolute value one, the rest interval has volume (pi/12)T^3, and the full diamond has volume 2pi/3. Null/degenerate intervals contribute zero.

For a uniform rest interval of total duration T, direct radial integration gives centered time variance T^2/40 and each centered spatial-coordinate variance 3T^2/80. Cross moments vanish by symmetry. Under the same Lorentz transformation the centered contravariant second-moment tensor is

    E[z^mu z^nu] = (3T^2/80) eta^{mu nu} + (Delta^mu Delta^nu)/16,

where Delta is the future displacement between the interval tips. Consequently the conditional second time moment for a flat draw Q in the future interval is

    E_0[Q_t^2 | p precedes Q] = (1+t)^2/4 + (2b^2+3r^2)/80.

Set M(t,r)=E_0[f(Q_t) | p precedes Q]=(7+18t+11t^2)/40+3r^2/80. These intermediate moments use the flat conditional law, before multiplication by both sampling densities. Since densities are exactly affine in theta, the ordered-pair integral is exactly quadratic:

    q(theta)= integral_C A(p)[1+theta(f(t)+M(t,r))+theta^2 f(t)M(t,r)] dmu0(p).

There is no omitted curvature or small-parameter remainder. In cylindrical coordinates dmu0 after angular integration is 3r dr dt, with 0<=r<=R=1-|t|. Let h=b^2-R^2=max(-4t,0). The required radial integrals are

    J0= integral_0^R r(b^2-r^2)^(3/2)dr = (b^5-h^(5/2))/5,
    J2= integral_0^R r^3(b^2-r^2)^(3/2)dr
       = b^2 J0 - (b^7-h^(7/2))/7.

For I_k(a)=integral_{-1}^1 a(t)[(1-t)^k-(-4t)_+^(k/2)]dt, time reversal and evenness of f give

    q0=(3/40) I_5(1),
    q1=(3/20) I_5(f),
    q2=(3/8)[I_5(f(17+30t+25t^2))/400 - (3/560)I_7(f)].

These integrals reduce to rational monomial integrals on [0,1]. Evaluation gives

    q(theta)=4/35 + (36/1925)theta - (151/375375)theta^2.

The comparable-pair probability is p(theta)=2q(theta): strict chronology is asymmetric and swapping the two iid draws interchanges the two directed events. On [0,1/2],

    p'(theta) >= 13738/375375 =: c > 0.

Hence |theta-phi|<=|p(theta)-p(phi)|/c. The unlabeled two-point order has just the chain and antichain outcomes on this model, so its total variation is exactly |p(theta)-p(phi)|. Therefore the ordinary geometric bound is

    d_G(rho_theta,rho_phi) <= (675675/27476) TV(law_2(theta),law_2(phi)).

This is an explicit finite conditioning inequality on the stated subclass. In particular geometric separation at least epsilon forces two-point law separation at least (27476/675675)epsilon. Different parameters also have different isomorphism-invariant pair laws, so cannot be related by a volume-preserving future metric isometry. This does not assume a globally valid coordinate gauge for K3.

## Finite confidence route

For n>=2, take an arbitrary representative of the observed unlabeled order and uniformly permute its n vertices with an independent seed. Use the first 2m vertices, m=floor(n/2), as disjoint pairs. Exchangeability makes the resulting random labeled order have the original iid labeled law: within each orbit the permutation group acts transitively with equal stabilizer sizes. Thus the m pair indicators are iid Bernoulli(p(theta)) **unconditionally**. Conditioning on the observed order does not make them independent, and an arbitrary deterministic canonical partition does not justify this step.

Clip K/m into [p(0),p(1/2)] and invert the strictly increasing quadratic. The resulting theta_hat is order-only with explicit independent randomization. For any 0<alpha<1, the standard two-sided Bernoulli Hoeffding bound and the inverse Lipschitz estimate yield

    P{d_G(rho_theta_hat,rho_theta) >
      min(9/20, (675675/27476)*sqrt(log(2/alpha)/(2m)))} <= alpha.

The constant midpoint estimator theta_hat=1/4 has deterministic geometric radius 9/40. Choose it whenever that radius is smaller than the displayed concentration radius; this selection depends only on n and alpha and gives their minimum. Empty and one-point data use the midpoint. Exact binomial inversion offers a potentially sharper report through the same monotone parameter map; a verified implementation and coverage transport remain future work.

The concentration constants are conservative. At alpha=1/20, this displayed Hoeffding guarantee needs n=55,772 for radius 0.2, n=223,082 for radius 0.1 and n=892,326 for radius 0.05. It first improves on the deterministic midpoint bound at about n=44,066. These are calculations from the sufficient bound, not necessary sample sizes or empirical performance. An explicit finite theorem is not yet a claim of useful computation, improved performance, or a resolved general geometric inverse problem. Counting every comparable pair instead would use overlapping pairs, requiring a separate dependence bound. Dense observation construction can dominate any linear-time matching statistic and must be included in a later cost protocol.

## Prior work, arithmetic checks and remaining proof work

Order-invariant relation/chain counts and their geometric interpretation are established work. [Roy, Sinha and Surya, arXiv:1212.0631](https://arxiv.org/pdf/1212.0631), sections 2, 5 and 6, give the flat chain formula, curvature corrections and overlapping-chain fluctuation analysis. Their flat two-chain coefficient specializes to 4/35 in three spacetime dimensions. [Reid, gr-qc/0207103](https://arxiv.org/pdf/gr-qc/0207103), section III, describes dimension estimators using order counts and tests in conformally flat spacetimes. These sources are currently screened, not a completed priority comparison for the exact family above. A fixed known dimension and a restricted conformal parameter do not amount to a new general dimension estimator. No broad originality claim follows.

[Exact rational arithmetic checker](../tools/check_lorentz_pair_moments.py) verifies the reduced moments and coefficients. Its optional deterministic quadrature checks the pre-radial-reduction moment integral to about 2e-14 agreement. [Retained checks](../evidence/geometric-gauge/ordinary-pair-moments/checks.json) record the source hash. Neither computation proves the geometric moment reductions or supplies rigorous floating-point enclosures. No random data or benchmark outcomes were generated. The initial standalone quadrature diagnostic is also retained; no stochastic feasibility protocol has been bypassed.

Remaining to-do list: audit the ordinary geometric integrals and prior proofs; certify original-class membership, actual pair-law identity and the geometric forward bound; prove the random-label/disjoint-pair confidence bridge on the actual observation; finish the full-class representation obligations; resolve the S042 gate before selecting an S043 experiment. No manuscript or physical applicability claim is advanced.
