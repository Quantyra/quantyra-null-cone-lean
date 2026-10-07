# A limitation of the current finite calibration

2026-10-07, S019. This concerns the implemented grid/union-bound certificate, not an information-theoretic impossibility or an optimal sample lower bound.

Before observing data, the flat estimate has coefficient error <=1/2 throughout K. Its CDF has error <=1/8: put f=rho-1. Uniform marginals make the integral of f on each row/column zero; the integral over a lower rectangle is, up to sign, its integral over each of the other three complementary rectangles. Since |f|<=1/2,

    |C_rho(u,v)-uv| <= (1/2) min(uv,u(1-v),(1-u)v,(1-u)(1-v)) <=1/8.

No tightness for that CDF bound is asserted in the Lipschitz class. This baseline must be compared with a finite estimator; beating the unrelated upper bound one is not enough to establish useful inference.

For delta=1/20 and n<=4096, the current certificate a=B+3epsilon+4/q cannot be <=1/8 while its grid Hoeffding union bound is <=delta, even with B=0. If q<=32, 4/q already exhausts the target. For the four remaining ranges, assuming the target bounds epsilon gives these lower bounds on the proposed failure expression:

| q | Maximum allowed 2n epsilon^2 | Minimum prefactor 2(q+1)^2 |
| --- | --- | --- |
| 33-64 | 32/9 | 2(34)^2 |
| 65-128 | 8 | 2(66)^2 |
| 129-256 | 98/9 | 2(130)^2 |
| >=257 | 128/9 | 2(258)^2 |

Each product prefactor times exp(-t) exceeds 1/20. The [exact rational check](../checks/check_finite_data_calibration_limit.py) uses exp(-t)>=(1-t/512)^512 to certify all four comparisons. The implemented rational *upper* bound on exp(-t) cannot circumvent a lower bound on the actual union expression. The argument allows every integer q, hence covers the implementation's finite mesh selection too.

Consequences: the new forcing certificate gives inspectable order-only rank ambiguity, and improves the original occupied-grid reconstruction route, but its present confidence constants do not certify CDF accuracy beyond the no-data prior at 95% confidence within the CLI range. This does not imply the data are uninformative, that every LP band must be trivial, or that a sharper empirical-process calibration cannot work. A separate one-dimensional marginal concentration bound, tighter joint-CDF calibration, structural constraints or direct confidence-set analysis are credible sharpening questions; they need their own theorem/source and implementation audit. Changing to a parametric toy family would not solve the original full-K task.

The [experiment report](finite-data-experiment-report.md) separately assesses actual bands and errors in selected densities. The new-paper gate is evaluated on those results and this limitation, without manufacturing a practical-sample or novelty claim.

Remaining to-do list: none for this justified limitation; useful full-K density guarantees remain future research.
