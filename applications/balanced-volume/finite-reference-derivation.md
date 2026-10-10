# Exact calibration supplies a dominating finite reference

S049, 2026-10-10. The original candidate uses four separate tail bounds. Before attempting a costly joint likelihood-ratio calibration, check the stronger reference obtained by exact calibration of each conditional binomial rejection region. The argument below shows that the candidate cannot have a positive power advantage over that reference for any admitted distribution. It does not prove that either test is globally optimal.

## Provenance and scope

Exact calibration orders possible observations by a statistic and sums their null probabilities; [Resin, section 2, equation (1)](https://arxiv.org/pdf/2008.12682) states this standard simple-null construction. Maximizing over a composite null preserves validity. We derive the endpoint reduction needed here explicitly, rather than importing an unverified nuisance-optimization claim. The method is an explicit specialization of established exact-test construction. This is neither a call to Resin's simple-null R package nor a claim that his article contains this balanced-volume application. The new implementation below is ours. Its use as a stronger reference does not establish a new statistical principle.

## Conditional experiment

For either category A or B, write its count as K and its count together with C as M. Under the multinomial retained-event model,

```
K | M=m ~ Binomial(m,q),
q in [qlo,qhi] under the nominated volume band [l,u],
qlo = l/[l+R*(1-2*l)],
qhi = R*u/[R*u+1-2*u].
```

Both tests receive `beta=alpha/2`. Independence between their random subset sizes or their test decisions is not assumed. At m=0 the test is unresolved.

## A continuous nuisance interval reduces to two exact checks

For integers `-1<=a<b<=m+1`, reject when `K<=a` or `K>=b`. With a nonempty central acceptance region, its rejection probability is

```
g(q) = P_q(K<=a) + P_q(K>=b).
```

If either tail is empty, g is monotone, so its maximum over a closed q interval is at an endpoint. If both tails are nonempty and `b>=a+2`, differentiation of binomial tails gives

```
g'(q)/m = BinomialPMF(m-1,q,b-1) - BinomialPMF(m-1,q,a).
```

The ratio of the first positive term to the second is a positive constant times `(q/(1-q))^(b-a-1)`, which increases strictly on (0,1). Hence the derivative changes sign at most once, from negative to positive. The function has no interior maximum. If the acceptance region were empty, g would be identically one, which cannot pass beta<1. Therefore

```
sup_{q in [qlo,qhi]} g(q) = max(g(qlo),g(qhi)).
```

This is a proof over the whole nuisance interval. It does not approximate it by a grid.

## Construction and finite validity

For a fixed m, define the ordering score

```
U(k) = min(P_qlo(K<=k), P_qhi(K>=k)).
```

Begin with both tails individually at level beta. This gives the largest potentially useful rejection set in the family `{U<=t}` with t<=beta. Repeatedly delete the accepted-for-rejection boundary count with the larger U score, deleting both boundary counts on an exact tie, until both endpoint rejection probabilities are at most beta. This is a nested exact calibration of a two-sided interval-null test, retaining both directions of error.

The original candidate's region for this pair uses `U<=beta/2`. It is feasible: under every q in the null interval each of its two tail probabilities is at most beta/2. Consequently calibration must stop before deleting any count in that original region. With rational qlo, qhi and beta, all comparisons, endpoint sizes and ties can be checked by integer arithmetic. No floating quantile is needed to establish size or inclusion.

For every m and every admitted q, the reference conditional rejection probability is at most beta. Averaging over M proves the same unconditional bound for each pair. A union bound over A:C and B:C gives false flags at most `2*beta=alpha` for the complete multinomial observation. The two tests can be dependent.

Moreover, for every possible count triple,

```
candidate_reject => finite_reference_reject.
```

Thus the reference's correct-flag probability is at least the candidate's under every alternative law, at the same sample size, observations, detector bound and uniform false-flag budget. This is sufficient to refute a positive-power-improvement claim for the frozen candidate over this stronger reference. It does not refute its earlier gains against the three specific marginal tests or the asymptotic Tudball variants. It also does not identify a uniformly most powerful test.

## Exact implementation and independent audit

For q=s/d, maintain the integer CDF numerators `F_m(k)=d^m*P_q(K<=k)`. The Bernoulli-step recursion is

```
F_m(k) = (d-s)*F_(m-1)(k) + s*F_(m-1)(k-1),
F_m(-1)=0, F_m(m)=d^m.
```

The implementation computes critical bounds from these integer arrays. It verifies endpoint size by cross-multiplication with beta's denominator and verifies that both original candidate tails are contained. The independent audit instead constructs integer probability masses from binomial coefficients and sums them. It checks every table row with a different recurrence.

Power calculations remain floating-point multinomial sums with an explicit omitted-mass bound. Their numerical status is separate from the exact-integer size and nesting checks. Neither is described as Lean certification. Full joint likelihood-ratio inference could improve further; it is unnecessary to establish this particular negative candidate gate.

Remaining to-do list: execute and audit the frozen comparison, then ground the next candidate in physical observations, independent calibration and a useful decision.
