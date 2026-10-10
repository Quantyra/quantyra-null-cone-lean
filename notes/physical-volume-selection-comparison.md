# Physical volume and bounded selection weights

2026-10-09 (Hawaii), S046. The binary bounded-selection formulas used by our physical-volume report already appear explicitly on page 237 of [Aronow and Lee, Biometrika 100(1), 2013, 235–240](https://doi.org/10.1093/biomet/ass064). The purchased journal article and its two-page supplement are now fully inspected, including all four proofs. The existing calibrated benchmark incorporates the binary construction; this source requires no additional numerical comparator.

## Source and proof scope

All six article pages were read, including sections 2–3 and the complete Proposition 1 appendix on pages 239–240. The appendix converts a normalized weighted mean into a linear objective over normalized feasible weights, finds an endpoint-weight optimizer, sorts the weights with the outcomes, and identifies the threshold where the objective stops increasing. These are bounds on the possible Hájek estimator values for the observed sample.

The supplement's Lemma 1 proof shows that the selected threshold optimizer does not split a group of equal outcomes, treating constant outcomes separately. Its Proposition 2 proof establishes the sorted weight pattern for distinct outcome groups: an inverted pair can be improved because at least one of the two displayed inequalities (B1)–(B2) holds. Proposition 3 groups equal responses, applies the strong law under independent population replication, and uses strict threshold inequalities to make an optimal weight pattern eventually stable. The lower arguments are given by symmetry. Equal lower/upper weight bounds require no strict improvement argument and are handled directly in our binary formulas.

These are population sharpness and convergence results under that sampling framework, not a finite confidence calibration. Their proofs do not supply a finite 95% interval, a uniform n/R minimax theorem, or geometric alternatives for full marked orders. The strong law is used as a standard result; it was not separately re-proved for this source audit. The article's asymptotic framework is not imported into our conditional retained-iid experiment.

The user-supplied PDF has SHA256 `a6bcd1a2e9e0e5c43d7b90d7227b6456e4d97629b6b19a71612b822535ebd507`. The PDF, extracted text, page image and receipt are retained privately outside this repository. No purchased article bytes are redistributed here.

The subsequently supplied `ass064_Supplementary_Data.zip` contains only `Bka-12-198_supplement.pdf`, two pages. ZIP SHA256: `4ebf395b7f880b544fe626b79a95e6c5c0cffa8b01c77028b6429cc7394502ba`; PDF SHA256: `9c3b23c711ab82a5ebbeda74ae4f51b0b1d56af148647608da990ae20dfb0ef1`. Both pages were read and visually inspected. They and their receipt are also retained privately. The earlier article-only review is preserved in Git history.

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

## Comparator decision

The binary selection transform is established prior work and must receive explicit attribution. Its generic weight sharpness does not establish sharpness within our smooth geometric class K given the full marked order. Our accepted result supplies admissible geometric alternatives, the uniform joint sampling/calibration rate, an obstruction for all eligible independently randomized full-order estimators, and exact-source GCP certification. These distinguish the proved mathematical content from the established formulas without asserting exhaustive novelty.

The full article and supplement supply no distinct finite-coverage benchmark beyond the existing calibrated binary construction. Keep the current exact-binomial report as the practical method, consistent with the [frozen comparison](physical-volume-finite-validation.md). The broader planning audit records the reviewed Imbens–Manski, Stoye and Tudball proof chains and their edition/assumption limits. Within that comparison set and the frozen observation/coverage requirements, the comparator review is complete; no protocol amendment or new execution is necessary. This is not an exhaustive ranking of all statistical methods or a claim of shortest possible intervals.

No experiment, accepted proof, manuscript or original pilot was changed for this comparison, and no Lean invocation was made. The [manuscript decision](physical-volume-manuscript-decision.md) completes the S046 disposition.

Remaining to-do list: none for this source/comparator comparison. S039 and S042–S044 remain selected; S047 is queued separately.
