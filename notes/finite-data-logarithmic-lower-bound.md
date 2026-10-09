# S036: a matching logarithmic lower bound

2026-10-09. Complete ordinary argument below; the full lower endpoint and fixed-confidence minimax radius have **exact-source GCP Lean acceptance**, run `space-log-lower-final-acceptance-20261009T171053Z-0c7e20`. The original density class K and global-transpose full-square loss of the published finite-data paper are unchanged. The construction uses centered translated Gaussian profiles. This replaces the plan's preferred compact-support candidate with the same packing strategy and simpler reuse of accepted Gaussian calculus. No stronger density assumptions or new observations enter the conclusion.

## Statement

Put a(n)=(log(n)/n)^(1/4). For each integer n>=2^64 and every estimator of one unlabeled strict directed order, including an arbitrary independent probability-space seed, assume its simultaneous success events are measurable. There is rho in the original K such that

    Pr_rho{ L(estimate,rho) > a(n)/8192 } >= 1/2.

The required probability 1/4 follows. Outputs need not lie in K or be bounded; success means that one global identity or transpose makes every pointwise error at most the radius. The proof also holds when the estimator sees the entire iid coordinate sample, provided the corresponding success events are measurable.

Together with the accepted uniform 95% upper radius `min(1/2,650 a(n))`, this implies, for n>=2^64,

    a(n)/8192 <= r_95(n) <= min(1/2,650 a(n)),

where r_95(n) is the infimum of all nonnegative radii achievable uniformly over K by an eligible estimator with failure probability at most 1/20. The infimum includes randomized estimators. This is rate optimality up to constants at fixed confidence, not an expected-risk theorem or a sharp leading constant.

## 1. A translated mean-zero profile

Let f(t)=t exp(-t^2). The accepted Gaussian development proves smoothness, |f|<=1/2, |f'|<=1 and

    integral_R f(t)^2 dt = sqrt(pi)/(4 sqrt(2)) <= 1.

For h>0 and any center c define

    g_(h,c)(x) = f((x-c)/h),
    mu_(h,c) = integral_0^1 g_(h,c)(x) dx,
    p_(h,c)(x) = g_(h,c)(x) - mu_(h,c).

The primitive `-(h/2) exp(-((x-c)/h)^2)` gives

    mu_(h,c) = (h/2) [exp(-(c/h)^2) - exp(-((1-c)/h)^2)].

Both exponentials lie in [0,1], hence |mu|<=h/2. Therefore p is smooth on all of R, integrates to zero on [0,1], obeys |p|<=1/2+h/2 and is Lipschitz with constant 1/h. For h<=1/16, |p|<=1 suffices below. Centering decreases the second moment:

    integral_0^1 p^2 = integral_0^1 g^2 - mu^2
                    <= integral_R g^2 <= h.

Every integral here is finite; continuity gives compact-interval integrability and Gaussian integrability handles the whole-line comparison.

Two pointwise estimates will supply separation. First, exp(-1/4)>=3/4 gives f(1/2)>=3/8. Second, if |t|>=4, then |f(t)|<=1/16. To see the latter, `exp(t^2/2)>=1+t^2/2` implies `exp(t^2)>=(1+t^2/2)^2>=t^4/4>=16|t|`. Multiply by exp(-t^2). This argument uses only elementary exponential inequalities already present in the accepted Gaussian proof.

## 2. A transpose-invariant packing inside K

Fix an integer m>=1 and put

    h=1/(16m),
    c_j=1/4+(j+1/2)/(2m),  j=0,...,m-1,
    rho_j(u,v)=1+(h/2) p_(h,c_j)(u) p_(h,c_j)(v).

Each rho_j is globally smooth and invariant under transpose. Every marginal is exactly one because the centered profile integrates to zero. The deviation from one is at most h/2<=1/32, hence the required [1/2,3/2] range holds. For any two points z,w, expanding the product difference and using |p|<=1 yields

    |rho_j(z)-rho_j(w)| <= (|z_1-w_1|+|z_2-w_2|)/2
                         <= 2 |z-w|_2.

Thus each rho_j belongs to the full original K, with room in the Lipschitz bound. No uniform bound on higher derivatives is used.

Let x_j=c_j+h/2. Then x_j is in [0,1], and |c_j-c_k|>=1/(2m)=8h for j!=k. At x_j,

    p_(h,c_j)(x_j) >=3/8-h/2 >=1/4,
    |(x_j-c_k)/h| >=8-1/2 >=4,
    |p_(h,c_k)(x_j)| <=1/16+h/2 <=3/32 <=1/8.

Consequently, at the diagonal witness z_j=(x_j,x_j),

    rho_j(z_j)-rho_k(z_j)
      >= (h/2) [(1/4)^2-(1/8)^2] =3h/128.

All alternatives are transpose-invariant; quotient separation is therefore no smaller than this pointwise difference. In particular, success sets at any radius r<=h/256 are pairwise disjoint: two simultaneous successes would imply a difference at z_j of at most 2r<=h/128, contradicting 3h/128. This also works for arbitrary outputs and avoids any bounded-output supremum convention.

## 3. Actual iid likelihood moments

Take the uniform coordinate law Q0 on the square. The one-point squared-density integral is

    integral rho_j^2 = 1 + (h^2/4) (integral_0^1 p_(h,c_j)^2)^2
                     <= 1+h^4/4.

Under the n-fold uniform reference, the likelihood L_j is the product of the n densities. Independence gives

    integral L_j =1,
    integral L_j^2 <= (1+h^4/4)^n <= exp(n h^4/4).

These are the true coordinate product measures. Adding a common independent random seed leaves the two likelihood moments unchanged. Observing only the directed-order isomorphism class is a measurable deterministic map. Pulling back each measurable success event through that map reduces the order-only statement to the coordinate experiment, without assuming independent overlapping suborders or observed ranks.

## 4. Many-alternative testing

On a common reference probability space Q, let L_1,...,L_m be nonnegative likelihoods with integral one and squared integral at most B. Let A_j be pairwise disjoint measurable success events, and q_j=Q(A_j). Cauchy-Schwarz on each event gives

    P_j(A_j) = integral_(A_j) L_j <= sqrt(B q_j).

Since sum q_j<=1, finite Cauchy-Schwarz gives

    (1/m) sum_j P_j(A_j) <= sqrt(B/m).

If B<=m/4, average success is at most 1/2, so some alternative has failure probability at least 1/2. Apply this on the coordinate-sample times seed space, with the success events from section 2. Their complements express strict error. No KL or Fano formalization is needed for this argument.

This is an elementary instance of established divergence-based many-hypothesis testing, not a new general statistical inequality. See Guntuboyina, *Lower bounds for the minimax risk using f-divergences, and applications* (2011), section I's packing reduction, Theorem II.1 and especially Example II.8, equation (15), with l=2: https://arxiv.org/html/1002.0042v2. Theorem II.1's proof and Examples II.5/II.8 were inspected; the primary-source retrieval/hash record is `evidence/finite-data/s036-literature.json`. The present proof is written out independently so that its probability and measurability obligations can be certified directly. The Lean proof uses the equivalent single function F=sum_j 1_(A_j)L_j: disjointness gives F^2=sum_j 1_(A_j)L_j^2, and Cauchy-Schwarz bounds integral F by sqrt(mB). Existing copula/rank comparisons remain in `finite-data-manuscript-literature-refresh.md`.

## 5. Explicit finite scale

For n>=2^64 let t=log n, x=(n/t)^(1/4) and m=ceil(x). Then t>=32, using log 2>=1/2. The elementary inequality

    exp(t/2) >= (1+t/4)^2 >= t,  t>=0,

implies t<=sqrt(n), hence x>=n^(1/8), log m>=t/8 and m>=exp(4)>=16. Also x>=1 and therefore m<=x+1<=2x. All floors/ceilings have positive arguments.

Since m>=x, n/m^4<=t. With h=1/(16m), the likelihood bound from section 3 satisfies

    log B = n h^4/4 = (n/m^4)/262144 <= t/16
          <= (log m)/2.

Thus B<=sqrt(m)<=m/4, because m>=16. Section 4 gives an alternative with strict-error probability at least 1/2 at every radius r<=h/256. Finally

    h/256 =1/(4096m) >=1/(8192x)=a(n)/8192.

Apply the argument directly at r=a(n)/8192; only measurability of those target-radius success events is required. There is no implicit assumption that success events at an auxiliary radius are measurable. This proves the statement.

## 6. Interpretation, proof obligations and custody

The coordinate lower bound and order-only upper bound place both fixed-confidence minimax radii at the same rate up to constants. They do not identify optimal constants, finite-sample experiment equivalence, practical sample requirements or an efficient implementation. The upper constant remains 650; the completed LP pilot remains uninformative.

Eight new `LogLower*.lean` modules cover centered profiles and their moments, original-K membership, finite packing and witness separation, randomized many-event inequality, actual sample/order transport, integer scale and complete lower endpoint, then the 95% radius consequence with the existing upper theorem. The final root acceptance has 3035 jobs, 508 exact-type/axiom audits (62 new), 143 captured source/check/config identities, zero warnings and standard axioms only. All final premises are discharged except the explicit sample-size condition, probability-seed assumptions and success-event measurability. See [campaign and failed-route record](logarithmic-lower-certification.md) and the final evidence index `evidence/gcp/s036-logarithmic-final.json`.

Published payload `ce5496dffcf8c2caa8bcf03adf4756c7282effe6`, accepted proofs `6752732882862bc848c7a96722a7660456d6da38`, and frozen pilot are preserved. All Lean/Lake development and acceptance must run on GCP. The manuscript revision is a separate working edition; no Zenodo write is part of this goal.

Remaining to-do list: none for S036 proof and certification. The [reviewed manuscript revision](../manuscript/finite-data/revisions/v0.2.0/README.md) and its exact formal map are delivered; Zenodo publication and practical-estimator research are separate follow-ups.
