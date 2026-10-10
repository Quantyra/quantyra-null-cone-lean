# Observable balance and finite inconsistency tests

## Model and balance

Keep original K, uniform coordinate marginals, a=(0,0), b=(1/2,1/2), known R, and the full marked order of n iid retained events. Define A={a precedes X precedes b}, B={b precedes X}, C=the remaining sampled events. Null boundaries have zero mass. A and B are observable from the existing anchor flags; no extra anchor, coordinate or detector value is supplied. Write v=mu(A).

Inclusion-exclusion gives

    mu(B) = 1 - mu{u<=1/2} - mu{w<=1/2} + mu(A) = v.

Hence the three generated category masses are (v,v,1-2v), even without pointwise reflection symmetry. The retained category probabilities x,y,z need not be balanced. This is a population marginal identity, not a symmetry assumed for the unknown detector.

## Aggregate identified bounds

Let inverse average selection weights t_A,t_B,t_C lie in [1,R]. Then physical masses are proportional to (t_A x,t_B y,t_C z). Equal physical masses impose t_A x=t_B y=h, which is feasible exactly when max(x,y)<=R min(x,y) for positive x,y. Consequently

    v in [max(x,y)/(2 max(x,y)+R z),
          R min(x,y)/(2 R min(x,y)+z)].                 (1)

To prove sharpness for the aggregate three-category model, h ranges over [max(x,y),R min(x,y)] and t_C over [1,R]. The function h/(2h+t_C z) increases in h and decreases in t_C, giving both attainable endpoints. Intersect with [1/8,3/8] for original K. This does not prove every aggregate endpoint is attainable by a smooth Lipschitz density in K; (1) remains a valid outer bound for K.

The ordinary pooled bound applies Aronow-Lee selection bounds to A union B, whose mass is 2v. Write L_R(q)=q/[R-(R-1)q], U_R(q)=Rq/[1+(R-1)q]. It gives [L_R(x+y)/2,U_R(x+y)/2]. Equation (1) contains additional information when x != y. At R=1, x=y=v, pooling has count variance v(1-2v)/(2n), versus v(1-v)/n for the old A-only report. Neither population weighting with known moments nor pooling binomial counts is a new statistical principle.

For example, v=1/4, R=2 and category detector probabilities (1/2,1,1) give (x,y,z)=(1/7,2/7,4/7). Equation (1) is [1/6,1/4]; the pooled bound is [3/22,3/10]. A nominated band [9/32,11/32] is disjoint from the balanced bound but overlaps the pooled bound. This is a model-level reason to test finite decision power; it is not an empirical performance result or physical validation.

## Finite conditional tests

Let (K_A,K_B,K_C) have the retained multinomial law. Conditional on M_A=K_A+K_C, K_A is Binomial(M_A,q_A), where q_A=x/(x+z). Likewise K_B conditional on M_B=K_B+K_C is Binomial(M_B,q_B). This conditioning is legitimate iid category sampling; it does not assume an adaptively stopped count is conditionally binomial. The two conditional tests need not be independent.

The generated conditional category probability for both comparisons is h(v)=v/(1-v). Bounded selection yields

    L_R(h(v)) <= q_A,q_B <= U_R(h(v)).

To test H0: v in [l,u], reject for an unusually small K_A or K_B at q=L_R(h(l)), or an unusually large count at q=U_R(h(u)). Use alpha/4 per tail. The binomial lower tail decreases in q and the upper tail increases in q. Under H0 each tail probability is a conservative p-value, conditional on its subset size, hence also unconditionally. A union bound over the four tails proves uniform false rejection <=alpha. At subset size zero, both p-values equal one. An empty intersection is not assigned an extra unbudgeted alarm.

Comparators use the same observation and the same 5% false-flag budget: (i) the old A-only exact binomial two-tail test with transformed endpoint null probabilities; (ii) the pooled A+B exact binomial test with target 2v; (iii) a balanced one-category-at-a-time report, using K_A/n and K_B/n, alpha/4 in each tail. Comparator (iii) already uses the geometric equality and is stronger than comparing only with the old implementation. The candidate uses conditional A:C and B:C odds to exploit the known mass of C. Two-sided confidence-interval choices do not replace these direct one-sided exact decision tests; each component tail is the standard monotone binomial test at its allocated size.

Candidate finite guarantees follow ordinary binomial conditioning and union bounds. The pilot evaluates power numerically; it does not certify every floating tail computation or replace GCP formal verification. Known population constraints with bounded inverse weights are covered by [Tudball et al., Biometrika 110 (2023), 485-498](https://doi.org/10.1093/biomet/asac042), extending Aronow-Lee sensitivity analysis. Their auxiliary-constrained framework is a mandatory stronger comparison; no new general identification method or final superiority is claimed before that comparison.

## Physical boundary

Exact balance depends on known population marginal medians. If their probabilities are F_1,F_2 instead, mu(B)-mu(A)=1-F_1-F_2. Uncertain or sample-selected anchors require a separate calibration treatment. Observed detector balance does not establish generated balance. Real photon captures additionally require a validated point process, independent/controlled selection and bounded relative efficiencies before any physical volume interpretation.

Remaining to-do list: validate the finite implementation and power screen, complete the auxiliary-constraint source comparison, and validate physical assumptions for a surviving decision benefit.
