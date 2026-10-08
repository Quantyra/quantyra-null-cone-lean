# Sharp uniform DKW proof route: work in progress

S024, 2026-10-07. This is a technical implementation route, not a Lean certificate. The required marginal bound is the sharp two-sided `2 exp(-2 n epsilon^2)`; the current split-DKW calibration must retain its constants.

A [primary-source library assessment](../evidence/dkw-formal-library-assessment.json) found no matching export in the searched libraries. StatLean's [DKWUniform source at the inspected commit](https://github.com/StatLean/Stat-Lean/blob/86b3823f77fc2b0f5a9923f85b588a4f8a65f94c/StatLean/HypothesisTesting/ForMathlib/DKWUniform.lean) explicitly proves the weaker `4 exp(-d^2/16)`; its one-sided order-statistic source uses an n-fold union. Neither supports the existing calibration. No external code or dependency was imported.

The probability route uses the reverse empirical-CDF likelihood martingale in [Reeve's proof](https://arxiv.org/html/2403.16651). We only need uniform margins, so finite uniform bin spaces can replace an arbitrary-distribution conditional-law construction before a dense-grid limit.

## Analytic barrier to formalize

For 0<e<1, find p in [(1-e)/2,1/2] with p<1-e solving

`log(1+e/p)+log(1+e/(1-p-e))-e/(p*(1-p))=0`.

For e<1/2, bracket the root between (1-e)/2 and 1/2. For e>=1/2, use upper endpoint `1-e-(1-e)/2*exp(-4/(1-e))`. Logarithmic bounds for `log((1+z)/(1-z))` give the required signs. Let lambda=e/(1-p-e)>0 and

`F(t)=(t+e)*log(1+lambda/t)-log(1+lambda)`.

The intended barrier is F(t)>=2e^2 for 0<t<=1-e. At t=p, F equals Bernoulli relative entropy and its derivative vanishes. Its second derivative has numerator `lambda*(t*(2e-lambda)+e*lambda)`, with one change from positive to negative at `c=e*lambda/(lambda-2e)`. The root bounds imply p<=c. Convexity up to c gives F>=F(p); concavity afterward bounds F below by the lesser endpoint value. Bernoulli Pinsker gives F(p)>=2e^2. At the other endpoint,

`F(1-e)=log(1+e^2/((1-e)*(1-p)))>=log((1+e^2)/(1-e^2))>=2e^2`.

Each analytic step still needs a universal Lean proof. The [nine numerical diagnostics](../evidence/dkw-barrier-design-check.json) are supporting falsification checks only. They do not certify the barrier.

## Finite probability construction

On independent uniform bins 1..q, let C_k count observations in bins <=k and reveal the state `max(bin_i,k)` as k decreases from q to 1. Its sigma-algebras form an increasing discrete filtration. Use

`M(k)=(1+lambda)^(-n)*(1+lambda*q/k)^C_k`.

Within a revealed parent atom at k+1, an unrevealed bin is uniform on 1..k+1, so its conditional factor average is `1+lambda*q/(k+1)`. Prove the product conditional identity from finite sums, adaptedness/integrability, starting value one, and the martingale property. Mathlib's proved Doob maximal inequality then controls the grid supremum; the analytic barrier converts a CDF deviation >e to M>exp(2ne^2).

Quantize actual uniform points with the ceiling bin map and prove its iid law and grid-count identity; zero endpoints are null. Dyadic grids are nested and dense, so continuity of probability gives the real-threshold one-sided bound. Reflection x->1-x and a union bound give sharp two-sided DKW. Finally transport each actual-K sample-coordinate vector to the uniform product law; dependence between the two coordinates of a sampled point is permitted. Both marginal events and the existing joint-grid Hoeffding event combine by a union bound.

Remaining to-do list: analytic barrier, finite martingale/Doob construction, quantization/dense-grid/reflection, actual-K transport, then complete split-DKW coverage and the other S024/S025 obligations.
