# Reproducing auxiliary-constrained inference

S049, 2026-10-10. This is a secondary comparison, specified after the original pilot but before evaluating these comparator decisions. It specializes an existing method; it is not a new identification principle.

## Source and version

[Tudball et al., published article](https://pmc.ncbi.nlm.nih.gov/articles/PMC10183833/) supplies the relaxed-set optimizer and subsequent Wald adjustment in equations (8)-(9). The [Cambridge institutional PDF](https://api.repository.cam.ac.uk/server/api/core/bitstreams/f859839e-9961-4740-bb6b-2ba950150171/content) has 14 pages and SHA256 `64a67865d6aa425801f893815cb1e36f47b8c3c4e06dd8fa0d629d74a56a750c`. The published supplement was retrieved from the [Europe PMC supplementary archive](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC10183833/supplementaryFiles); its 11-page PDF has SHA256 `f974c3ff561fb023212132461ca48c30a90d3cfe19cb2ad8febfa19cb24bb516`. Its section 4.2 equation (4) agrees with preprint v4 Appendix C equation (23). Sources are retained outside Git, with identities recorded here.

The [author implementation](https://github.com/matt-tudball/selectioninterval/blob/e0003fa14c6ebb4a2c74106b666439c3bc5cfa73/R/selection_bound.R) implements logistic-weight regression, not this categorical problem. Its default single-constraint critical values correspond to `shared_default` below. We implement the published categorical mathematics explicitly; this is not a claim to have run their R package. The source theorem is asymptotic, not a uniform finite-sample certificate.

## Specialization and global optimization

Write observed proportions as `(x,y,z)` and inverse selection weights as `(a,b,c)` in `[1,R]^3`. Generated balance is `a*x=b*y`. All three target functions `f=(1,0,0)`, `(0,1,0)` and `(1/2,1/2,0)` represent the same population volume under balance. In the relaxed set they differ, so all three must be compared.

With constraint failure budget `alpha_c`, set `Z=normal.isf(alpha_c/2)` and `k=Z^2/(n+Z^2)`. The published relaxed constraint reduces to

```
(a*x-b*y)^2 <= k*(a*a*x+b*b*y).
```

For positive `x,y`, put `r=a/b`. This is equivalent to

```
abs(x*r-y)/sqrt(x*r*r+y) <= sqrt(k).
```

The signed left expression is strictly increasing on positive `r`: its derivative is `x*y*(r+1)/(x*r*r+y)^(3/2)`. Consequently the admissible positive ratios form an interval. The lower endpoint is zero when `y<=k`, otherwise

```
r_low = y*(y-k)/(x*y + sqrt(k*x*y*(x+y-k))).
```

The upper endpoint is infinity when `x<=k`, otherwise

```
r_high = (x*y + sqrt(k*x*y*(x+y-k)))/(x*(x-k)).
```

Intersect with `[1/R,R]`. Empty intersection is reported explicitly. The box allows `max(1,1/r)<=b<=min(R,R/r)`. At fixed ratio the objective

```
Q = sum(p_i*theta_i*f_i)/sum(p_i*theta_i)
```

increases with `b` and decreases with `c`, for all three target functions. Thus minimization uses the smallest `b` and `c=R`, while maximization uses the largest `b` and `c=1`. For the past target, both resulting objectives increase with `r`, so minimum and maximum use the lower and upper ratio endpoints. For the future target they decrease, so use the opposite endpoints. For the pooled target the minimizing and maximizing ratios both equal the projection of 1 onto the admissible ratio interval: below 1 the relevant weighted sum is monotone toward 1, and above 1 it is monotone away from 1. These arguments give global extrema, without a numerical optimizer.

At each optimizing weight vector compute

```
variance = sum(p_i*theta_i^2*(f_i-Q)^2) / sum(p_i*theta_i)^2
CI = [Q_min - normal.isf(alpha_q)*sqrt(variance_min/n),
      Q_max + normal.isf(alpha_q)*sqrt(variance_max/n)].
```

This optimizes `Q` first, as the source prescribes. It does not optimize a confidence endpoint over weights. Intersect with the known volume range `[1/8,3/8]`. Empty relaxed sets and zero-count guards return that full range; the flag-on-empty sensitivity is additionally reported. The latter is a model-incompatibility convention, not a successfully computed confidence interval.

## Allocation and regularity boundaries

The paper's Remark 2 requests relaxation failure `alpha1/2` and uses objective tails `alpha2/2`. With `alpha1=alpha2=.025` this yields `alpha_c=.0125, alpha_q=.0125`. Its author code instead uses `normal.isf(alpha/4)` for the two-sided constraint and each objective tail; this yields `alpha_c=.025, alpha_q=.0125`. A common constraint event may be counted once, followed by the two target-tail events. We include that stronger allocation, plus fixed `alpha_c=.01,.04` with `alpha_q=(.05-alpha_c)/2`. These are twelve separate methods; their unadjusted union is not a 95% procedure. All are fixed before comparator evaluation.

The finite-support ratio functions have positive denominators on the compact box and satisfy the usual smooth multinomial uniform laws. The population lower and upper optimizing weights are unique for positive category probabilities in the interior feasible model: balance fixes `a/b=y/x`, and the objective fixes the extreme available common scale and `c`. However, detector patterns on the boundary `y=R*x` or `x=R*y` can give empty relaxed sample sets with nonvanishing small probability. The supplementary sufficient constraint-qualification condition is not automatic there: the equality and two active box faces have dependent gradients. Accordingly, no blanket application of the source's argmin assumptions or finite validity is claimed. The explicit empty convention and diagnostics are retained. At `R=1`, the original exact pooled comparator supplies a stronger finite reference regardless of this asymptotic construction.

The natural finite reference still to examine is inversion of the joint multinomial law with the same bounded-selection and balance constraints. For a nominated volume band `[l,u]`, its feasible observed probability set is the simplex polygon

```
x <= R*y, y <= R*x,
l*z/[R*(1-2*l)] <= x,y <= R*u*z/(1-2*u).
```

This follows directly from the aggregate identified interval. It identifies a concrete next comparison; asymptotic-source reproduction alone cannot establish best-existing-method superiority.

Remaining to-do list: audit and evaluate this implementation, then resolve joint finite inference and physical calibration.
