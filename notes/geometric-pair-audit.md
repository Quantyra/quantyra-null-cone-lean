# Restricted geometric confidence: ordinary proof and investment audit

S042, 2026-10-10. **Ordinary mathematical derivation, not Lean certification.**
This completes the pre-formalization audit requested by the research efficiency
protocol. Retain the original time-quadratic family, improve its geometric
constant, and use the deterministic count of all comparable pairs with a
dependence-aware bound. Certify this complete theorem as the next milestone.
S042 remains at three of five criteria; S043 has not passed its gate.

The accepted baseline is the [general interior-isometry
audit](geometric-interior-isometry-certification.md): 1,165 exact GCP reports.
The smooth reconstruction converse remains external. The present restricted
result neither supplies a full-class explicit inverse modulus nor changes the
original class, its nontrivial gauge pair, or any published manuscript.

## Statement and model

Use the genuine 2+1 diamond `D={|t|+sqrt(x^2+y^2)<1}`, its closure `C`, flat
volume `V=2*pi/3`, and normalized flat probability `mu0=Lebesgue|D/V`. Set

    f(t)=t^2-1/10,
    rho_theta=1+theta*f,  0<=theta<=1/2,
    g_theta=(rho_theta/V)^(2/3)*eta,  eta=diag(-1,1,1).

The observation is one unlabeled strict directed chronological order from `n`
iid draws with law `mu_theta=rho_theta*mu0`. It contains neither coordinates
nor time measurements. Let `d_G` be the accepted coupling-distortion loss of
the weighted-time profile quotients. All units and volume normalization are
the original model conventions.

Write

    q(theta)=4/35+(36/1925)*theta-(151/375375)*theta^2,
    p(theta)=2*q(theta),
    c=13738/375375,
    pmax=p(1/2)=185489/750750,
    v=pmax*(1-pmax)=104849697629/563625562500,
    L=3/20.

The ordinary theorem is:

1. Every `rho_theta` belongs to the original smooth density class.
2. `q(theta)` is the actual ordered-pair probability and `p'(theta)>=c>0`.
3. `d_G(rho_theta,rho_phi)<=L*|theta-phi|`.
4. For `n>=2`, put `m=floor(n/2)`, `s=log(2/alpha)`, `0<alpha<1`, and

       b=s/(3*m)+sqrt((s/(3*m))^2+2*v*s/m).

   There is a deterministic order-only estimator with

       P_theta{d_G(rho_hat,rho_theta) > min(3/80,(225225/54952)*b)} <= alpha

   uniformly over this family. For `n=0,1`, the midpoint estimator has
   deterministic radius `3/80`.

Here and below an upper bound is sufficient, not asserted sharp. Sections
below give the complete ordinary argument; the arithmetic checker does not
replace its geometric, measure-theoretic or probabilistic steps.

## Family and actual pair integral

Integrating spatial disks gives time marginal `(3/2)*(1-|t|)^2` on `[-1,1]`.
Its moments are `E[t^2]=1/10`, `E[t^4]=1/35`. Consequently `E[f]=0` and
`E[f^2]=13/700`. The density is polynomial, lies in `[19/20,29/20]`, and
has Euclidean gradient norm at most one on the convex closed diamond. It is
normalized and meets the original `[1/2,3/2]`, Lipschitz-at-most-two bounds.

For `P=(t,z)`, put `r=|z|`, `d=1-t`, and `T^2=d^2-r^2`. The future of `P`
inside `D` is its interval to the top tip. For an interior point, `T>0`.
A centered rest interval of duration `T` has volume `pi*T^3/12` and centered
moments

    E[u0^2]=T^2/40,
    E[u1^2]=E[u2^2]=3*T^2/80,
    E[ui*uj]=0 for i!=j.

These follow by integrating disks of radius `T/2-|u0|`; the spatial-coordinate
second moment of a uniform radius-`R` disk is `R^2/4`. To justify transport,
write the future displacement as `Delta=(d,zeta)`, `T^2=d^2-|zeta|^2`, and use

    B(u0,u)=(d*u0/T+(zeta dot u)/T,
             u+zeta*(u0/T+(zeta dot u)/(T*(d+T)))).

Direct multiplication gives `B^T*eta*B=eta`, `B(T,0)=Delta`, positive time
orientation, and `|det B|=1`. Translating by the midpoint maps the rest
interval onto the required interval, preserving Lebesgue measure. The
centered covariance is therefore

    (3*T^2/80)*eta^(mu,nu)+Delta^mu*Delta^nu/16.

This proves both the normalized future volume `A(P)=T^3/8` and the conditional
future shape moment

    M(P)=E[f(Q_t) | Q in the flat future interval]
        =(7+18*t+11*t^2)/40+3*r^2/80.

Boundary/degenerate intervals have zero flat volume and do not alter these
integrals. Integrate the product of the two sampling densities:

    q(theta)=integral A(P)*(1+theta*f(P))*(1+theta*M(P)) dmu0(P).

A short way to evaluate this exactly is the light-cone substitution

    a=(1-t-r)/2, b=(1-t+r)/2,
    0<=a<=b<=1, t=1-a-b, r=b-a,
    dmu0=6*(b-a) da db, A=(a*b)^(3/2).

The spatial angle has already been integrated. For nonnegative integer `i,j`
and `h>=0`, two elementary power integrals give

    integral 6*(b-a)*(a*b)^h*a^i*b^j da db
      =6/((i+h+1)*(i+h+2)*(i+j+2*h+3)).

Apply this at `h=3/2` to `1`, `f+M`, and `f*M`. Their integrals are exactly
`4/35`, `36/1925`, and `-151/375375`. This independent reduction agrees with
the preserved radial/cap checker. Exchangeability and disjointness of the
two strict orientations give comparability probability `p=2q`. The minimum
of its decreasing positive derivative is `p'(1/2)=c`.

## Sharper geometric comparison

Let `Delta=|theta-phi|` and `w_theta=(rho_theta/V)^(1/3)`. The mean value
bound in density is

    |w_theta(t)-w_phi(t)| <= k*Delta*|f(t)|,
    k=1/(3*V^(1/3)*(19/20)^(2/3)) <= 27/100.

The last inequality follows from `pi>157/50` by cubing positive quantities:
`27*(2*(157/50)/3)*(19/20)^2*(27/100)^3>1`.

Along every admissible future absolutely continuous curve, flat proper speed
is at most its nonnegative time derivative. The primitive of the continuous
function `|f|` is C1 with bounded derivative on the time interval. The AC
chain rule and fundamental theorem thus imply

    |length_theta(curve)-length_phi(curve)|
      <= k*Delta*integral_(t_start)^(t_end) |u^2-1/10| du
      <= k*Delta*(7/15+4/(15*sqrt(10)))
      <= (27/100)*(5/9)*Delta = L*Delta.

The curve class is common to all positive conformal densities. Taking both
supremum inequalities yields the same bound for actual time separations;
pairs with no admissible curve have zero separation for both densities.

For the common-density coupling, the unmatched probability satisfies

    2*(1-integral min(rho_theta,rho_phi) dmu0)
      = Delta*E|f| <= Delta*sqrt(13/700) < L*Delta.

Use Cauchy–Schwarz and `13/700<(3/20)^2`. Two independent coupling draws both
lie on the common diagonal except on a set of mass at most twice the
unmatched mass. On that diagonal, the time error is at most `L*Delta`.
Push the coupling to the accepted profile quotients. Its distortion
admissibility proves `d_G<=L*Delta`; equality of parameters uses the accepted
zero diagonal. This specializes the accepted common-coupling argument; the
new AC integral estimate and its sharp-family specialization remain to be
formalized. No optimizer or optimal constant is claimed.

The parameter midpoint `theta=1/4` now gives a deterministic no-data radius
`L/4=3/80`. Also, monotonicity yields the inverse bound

    d_G(rho_theta,rho_phi) <= (L/c)*|p(theta)-p(phi)|,
    L/c=225225/54952.

## Observable statistic and finite confidence

Let `R` count every strict chronological relation in the observed order,
including transitive relations. Hasse edges alone are insufficient. For
`n>=2`, define

    U=R/binom(n,2)=2*R/(n*(n-1)).

This is unchanged by relabeling, hence defines a function of the original
unlabeled observation. Its symmetric pair kernel is the indicator `h` of
comparability. The expectation is exactly `p(theta)` at fixed `n`.

For each permutation `pi`, form the average `B_pi` of `h` on the `m` disjoint
pairs `(pi(1),pi(2)),...,(pi(2m-1),pi(2m))`. A uniformly averaged permutation
places every unordered pair in those positions with probability
`m/binom(n,2)`. Therefore, pointwise in the observations,

    U = (1/n!)*sum_pi B_pi.

For each fixed permutation its disjoint pairs are iid Bernoulli with mean
`p(theta)`. Jensen's inequality and exchangeability imply, for every real
`lambda`,

    E exp(lambda*m*(U-p)) <= E exp(lambda*m*(B_identity-p)).

The permutations are a proof device, with no random seed or permutation
enumeration in the estimator. Overlapping observed pairs are not independent.
This is the classical permutation argument for U-statistics, credited below.

For a centered Bernoulli variable `Z`, `|Z|<=1` and
`E|Z|^k<=E Z^2<=v` for all integers `k>=2`. Since `k!>=2*3^(k-2)`, expansion
of the exponential and `1+x<=exp(x)` give, for `|lambda|<3`,

    log E exp(lambda*Z) <= v*lambda^2/(2*(1-|lambda|/3)).

The uniform variance bound follows because `p` increases from `8/35` to
`pmax<1/2`, where `p*(1-p)` is increasing. Multiply the disjoint-pair MGFs,
use the preceding Jensen bound, and apply exponential Markov with
`lambda=r/(v+r/3)`. Applying the argument to both signs gives

    P{|U-p|>=r} <= 2*exp(-m*r^2/(2*(v+r/3)))  for r>0.

Solving for the positive root gives `b` in the theorem. Clip `U` to
`[p(0),p(1/2)]` and invert the continuous strictly increasing polynomial.
Clipping cannot enlarge distance to `p(theta)`, so the inverse estimator has
`|theta_hat-theta|<=|U-p(theta)|/c`. It is measurable and order-only. Select
this estimator if `(L/c)*b<3/80`; otherwise select the midpoint. That selection
uses only `n,alpha`, so its confidence radius is the stated minimum.

The all-pairs count does **not** have a binomial law. Exact binomial intervals
cannot be substituted into this proof. The earlier independently randomized
matching estimator remains a valid ordinary alternative, with separate
law/coverage obligations; it is not the selected formalization route.

## Quantitative check and decision

For `alpha=1/20`, use the rigorous rational bound `log(40)<369/100`. The
checker proves this from the first 21 positive exponential-series terms.
For error target `epsilon`, put `delta=c*epsilon/L`. Sufficient even sample
sizes are obtained by rounding up

    Hoeffding: m >= (369/100)/(2*delta^2),
    Bernstein: m >= 2*(v+delta/3)*(369/100)/delta^2,
    n=2*m.

| Geometric radius | Earlier L=9/10, Hoeffding | New L=3/20, Hoeffding | New L=3/20, Bernstein |
| --- | ---: | ---: | ---: |
| 0.025 | 3,570,386 | 99,178 | 74,606 |
| 0.010 | 22,314,906 | 619,860 | 463,260 |
| 0.005 | 89,259,622 | 2,479,434 | 1,849,002 |

These are sufficient guarantees, not necessary sample sizes or performance
measurements. The sixfold geometric improvement reduces the unrounded
Hoeffding requirement by 36 for a fixed absolute error. Relative to each
bound's own midpoint radius, that improvement cancels: the rational
Hoeffding crossover is 44,080 observations in both cases. Bernstein reduces
the new crossover to 33,338. The historical approximately 44,066 used
floating evaluation of `log(40)`, not this conservative rational upper bound.
Old targets 0.05, 0.1 and 0.2 are already met by the new midpoint without data.

Counting all pairs removes auxiliary estimator randomization, but this bound
still uses effective sample size `floor(n/2)`. No extra statistical gain from
all overlapping pairs is claimed beyond the established MGF argument.
Scanning an explicit dense order is quadratic; observation construction and
storage must count in any future feasibility protocol. These bounds do not
establish practical computational usefulness.

A bounded alternative-family check considered
`f=a*(t^2-1/10)+b*(r^2-3/10)`. The admissible choice `(a,b)=(2/3,-4/3)` gives
pair slope at least `16/165`, larger than `c`. However, a proved coarse
geometric factor is `11/20`: its absolute time-envelope integral is `23/18`,
the weight derivative is at most `3/7`, and `E[f^2]=41/315`. Its resulting
inverse factor `363/64` exceeds the retained family's `225225/54952`.
This is a comparison of sufficient bounds, not a global optimality or
impossibility result. A larger pair slope alone is insufficient reason to
change the family. Retain the current family and stop broadening this search
before the end-to-end theorem is accepted.

## Primary-source comparison and custody

| Source inspected | Relevant proof comparison and limit |
| --- | --- |
| Roy, Sinha and Surya, [arXiv 1212.0631v1](https://arxiv.org/pdf/1212.0631v1), 22 pages; [journal record](https://doi.org/10.1103/PhysRevD.87.044046) | Read the relevant flat-chain derivation, section 5 dimension context, section 6 overlapping-chain fluctuations, and Appendix moment calculations (PDF pages 4–8, 13–22). Their flat two-chain coefficient agrees with `q(0)=4/35`. Rest-interval moments agree with the independently integrated values above. Their Poisson/asymptotic fluctuation argument is not our fixed-n finite confidence theorem. The journal metadata was checked; its full text was not compared. |
| Reid, [gr-qc/0207103v2](https://arxiv.org/pdf/gr-qc/0207103v2), 26 pages, revised 2004-01-19; [journal record](https://doi.org/10.1103/PhysRevD.67.024034) | Read section III and relevant section IV sampling passages, PDF pages 6–9. Pair/chain counts and their dimension interpretation are established; equation (5) agrees with the flat coefficient. Its large-N `R/N^2` expression does not replace our exact normalization `R/binom(n,2)`. Curved sampling uses conformal volume. The earlier v1 was also retrieved; no complete version diff or full journal proof comparison is claimed. |
| Hoeffding, [Probability inequalities for sums of bounded random variables](https://www.cs.rpi.edu/academics/courses/spring06/random/hoefding.pdf), 1963 paper scan, 19 pages | Read printed pages 14–16 and 24–25, including section 5a's permutation/Jensen proof for U-statistics. Its effective block size is `floor(n/r)` for kernels of order `r`; here `r=2`. This directly validates the dependence-handling route. The Bernoulli Bernstein calculation above is given explicitly, rather than inferred from independent overlapping pairs. The concentration method is established, not a novelty claim. |

The inspected versions, PDF hashes, sizes and retrieval times are recorded in
[source custody](../evidence/geometric-gauge/ordinary-pair-audit/sources.json).
The PDFs remain private outside Git. This is a bounded comparison of the
proofs used here, not an exhaustive priority/correction search. A restricted
conformal-parameter result in a known dimension does not establish a new
general dimension estimator or physical detector model.

## Verification and next milestone

[The exact checker](../tools/check_geometric_pair_bounds.py) uses only rational
arithmetic for the reduced moments, geometric constants, three quadratic
candidates and sufficient sample counts. It agrees with the distinct preserved
radial reduction and checks permutation edge frequencies for `n=2,...,8`.
[Its retained output](../evidence/geometric-gauge/ordinary-pair-audit/checks.json)
contains source hashes and explicitly excludes formal certification. No
random samples, benchmark, Lean command or new GCP run was used for this
audit. All earlier source/evidence bytes remain intact.

The hard formal obligations are actual spatial-volume/pair integration and
the AC weighted-time integral estimate. Start with those, reusing accepted
coordinate, curve and coupling results. Then connect the order-invariant
statistic, permutation/Jensen law, Bernstein inequality and monotone inverse
to one actual-observation confidence endpoint. Check family membership and
measurability within that same batch. Do not substitute a theorem that assumes
the pair law or conditional independence which the endpoint must establish.

Use targeted GCP development with verified task-owned incremental cache
reuse, immutable submitted sources/outcomes, and one complete type/axiom
acceptance at this theorem milestone. Cache reuse is still an implementation
task, not an accomplished speedup. The last accepted VM state is terminated.
Reassess the route if a hard formal step exposes a mathematical gap; do not
turn proof difficulty into an impossibility claim. After acceptance, make the
S043 go/park decision against its intended theorem and computational budget;
avoid recertifying the same theorem as a separate S043 deliverable.

Remaining to-do list: certify the complete restricted confidence theorem on
GCP, validate incremental cache reuse, and record the S043 go/park decision.
