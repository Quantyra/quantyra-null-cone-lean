# Physical volume and bounded selection weights

2026-10-09 (Hawaii), S046. The binary bounded-selection formulas used by our physical-volume report already appear explicitly on page 237 of [Aronow and Lee, Biometrika 100(1), 2013, 235–240](https://doi.org/10.1093/biomet/ass064). The purchased journal article and its Proposition 1 proof have been inspected. Its separate supplement, containing the proofs of Lemma 1 and Propositions 2–3, remains unread pending access. This is a partial direct source comparison; it does not close S046.

## Source and proof scope

All six article pages were read, including sections 2–3 and the complete Proposition 1 appendix on pages 239–240. The appendix converts a normalized weighted mean into a linear objective over normalized feasible weights, finds an endpoint-weight optimizer, sorts the weights with the outcomes, and identifies the threshold where the objective stops increasing. These are bounds on the possible Hájek estimator values for the observed sample.

The article separately states population-bound sharpness and convergence under its replicated finite-population sampling framework. Proposition 3 also imposes a strict threshold condition. Their supporting proofs are in the supplement. Those asymptotic results are not imported into our conditional retained-iid experiment. In particular, the article's sample sensitivity interval is not by itself a finite 95% confidence interval for the physical target.

The user-supplied PDF has SHA256 `a6bcd1a2e9e0e5c43d7b90d7227b6456e4d97629b6b19a71612b822535ebd507`. The PDF, extracted text, page image and receipt are retained privately outside this repository. No purchased article bytes are redistributed here.

## Algebraic correspondence

Write the observed binary marked membership responses as y_i, with k ones among n>0 events, and set p=k/n. With weights w_i in [1,R], let A be their sum over ones and B their sum over zeros. Then

    k <= A <= R*k,     n-k <= B <= R*(n-k).

The weighted mean A/(A+B) increases with A and decreases with B. Its minimum and maximum are therefore

    L_R(p) = k / (k + R*(n-k)) = p / (R-(R-1)*p),
    U_R(p) = R*k / (R*k+n-k)   = R*p / (1+(R-1)*p).

The same formulas include k=0 and k=n. They match the article's binary formulas with gamma=R=beta/alpha. This elementary specialization does not require importing the supplement's asymptotic theorems.

For the actual retained-event probability theta, the existing physical identification argument gives L_R(theta)<=v<=U_R(theta). Both transforms are increasing on [0,1]: for x<=y their increments are respectively

    R*(y-x) / ((R-(R-1)*x)*(R-(R-1)*y)),
    R*(y-x) / ((1+(R-1)*x)*(1+(R-1)*y)).

Thus a finite binomial confidence interval [l,u] for theta gives the physical report [L_R(l),U_R(u)]. These are exactly the expressions in `retention_interval` in [the existing implementation](../tools/marked_volume.py). The S046 benchmark already applies this transformation to the same outward-grid Clopper–Pearson certificate and intersects it with the same known target range [1/8,3/8]. Giving an additional comparator those identical endpoints would duplicate its report for every input, not merely on the tested grid.

The uncalibrated plug-in interval [L_R(k/n),U_R(k/n)] cannot replace a comparator required to have finite 95% coverage. For example, take the admitted flat geometry, uniform detector R=1 and n=1. The target is v=1/4, whereas that interval is the observed singleton {0} or {1}, so its coverage is zero. Intersecting with the geometric range does not repair it. This is a direct calculation, not a new experiment or an assertion that Aronow and Lee claimed finite confidence coverage.

## Consequences and remaining review

The binary selection transform is established prior work and must receive explicit attribution. Its generic weight sharpness does not establish sharpness within our smooth geometric class K given the full marked order. Our accepted result supplies admissible geometric alternatives, the uniform joint sampling/calibration rate, an obstruction for all eligible independently randomized full-order estimators, and exact-source GCP certification. These distinguish the proved mathematical content from the established formulas without asserting exhaustive novelty.

The inspected article supplies no distinct finite-coverage benchmark beyond the existing calibrated binary construction. Keep the current exact-binomial report as the practical method, consistent with the [frozen comparison](physical-volume-finite-validation.md). Final comparator closure still requires the requested supplement review; freeze any scientifically necessary amendment before numerical execution. No experiment, accepted proof, manuscript or original pilot was changed for this comparison, and no Lean invocation was made.

Remaining to-do list: inspect the Aronow–Lee supplement; finalize comparator applicability and any required amendment; decide S046 manuscript placement and continue/stop disposition. S039 and S042–S044 remain selected.
