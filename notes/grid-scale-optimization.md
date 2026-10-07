# Logarithmic grid scale and improved inverse rate

2026-10-06, Quantyra Space E002/S014. This derivation uses the existing deterministic finite theorem and the probability/CDF/interpolation arguments in `finite-order-rate.md`. It improves the prose inverse estimate; it is not a claim that the full probability-to-density argument has already been formalized in Lean. Review and verification evidence is recorded separately below.

## Statement

For the same class K, directed sampled-order observable and axis-exchange quotient as the original theorem, every integer N>=2 satisfies

`d_conf(rho,sigma) <= 130 ((log N / N)^(1/6) + Delta_N(rho,sigma))`.

Here log is the natural logarithm. The original `100(N^(-1/12)+Delta_N)` bound remains valid. The new estimate improves the asymptotic N term; neither estimate is asserted optimal or a practical sampling prescription. No observable, hypothesis or metric has changed.

## Integer grid and cutoff

For an integer n>=65536, write `x=sqrt(n/(8 log n))` and choose `m=floor(x)`, `r=1/m`. The function `t/log t` is increasing for t>e: its derivative is `(log t-1)/(log t)^2`. At t=65536, `log t=16 log 2<16`, so `t/(8 log t)>512>16^2`. Hence x>16 and m>=16 throughout the large-n branch. Also `log n>=1`.

Since x>=2, the floor inequality gives `m>=x-1>=x/2`. Therefore

`m^2 <= n/(8 log n)` and `r <= 2 sqrt(8 log n/n)`.

The witnesses and the `30rn` finite-rank theorem require only m>=16 and the same deterministic occupancy/marginal/boundary premises. Their proof does not depend on choosing the previous fourth-root grid.

## Uniform success probability

The original failure bound for grid occupancy and vertex-CDF accuracy is

`p_fail <= m^2 exp(-n/(2m^2)) + 2(m+1)^2 exp(-2n/m^2)`.

The grid-size inequality implies `n/(2m^2)>=4 log n` and `2n/m^2>=16 log n`. Thus the occupancy term is at most

`[n/(8 log n)] n^(-4) = 1/(8 n^3 log n)`.

Because m>=1, `(m+1)^2<=4m^2`; the vertex term is at most

`8m^2 n^(-16) <= n^(-15)/log n`.

Consequently

`p_fail <= 1/(8 n^3 log n) + n^(-15)/log n <= 1/(8 n^3)+n^(-15)`.

For n>=65536, this is below 1/10. In fact the final expression is already below 1/10 at n=2 and decreases thereafter. Density positivity, uniform marginals, iid rectangle concentration, and the null coordinate-tie/grid-line events are exactly the inputs of the original proof. No independence between cells, rectangles or overlapping suborders is introduced.

## Cumulative and coefficient constants

On the successful event the established clipped-rectangle argument gives one common orientation with cumulative error at most 87r. The floor estimate therefore gives

`a_n = 174 sqrt(8) sqrt(log n/n)`

as a uniform error bound with probability at least 9/10. The existing order-only map and two-orbit TV separation imply

`d_conf <= (4096 a_n)^(1/3) + (5/4) TV(nu_n(rho),nu_n(sigma))`.

Substitution yields coefficient

`C_*=(4096*174*sqrt(8))^(1/3)`

in front of `(log n/n)^(1/6)`. To verify `C_*<130` without numerical approximation, square the positive quantities in the cubed comparison:

`8*712704^2 = 4063575932928 < 130^6 = 4826809000000`.

Since `5/4<130` and `TV(nu_N)<=Delta_N`, the claimed bound follows for N>=65536. CDF-minimizing orientation need not minimize the coefficient norm: the coefficient quotient is no greater than the error in the chosen orientation.

## Small sample branch

For every integer 2<=N<65536, the density bounds give `d_conf<=1`. The integral formula for log gives `log 2>=1/2`, and so

`log N/N >= 1/(2*65536) = 1/131072 > (1/8)^6`.

Therefore `130(log N/N)^(1/6)>130/8>1`. The claimed inequality holds trivially in this branch, with no grid construction or probability assertion at small N. This establishes the statement for all required integers.

## Audit obligations and evidence

The mathematical audit must check the monotonicity/cutoff, floor direction, both exponential exponents, `(m+1)^2` factor, exact integer constant comparison, positive real powers, fixed orientation, and small-N fallback before the manuscript is revised. `checks/check_grid_scale.py` probes the cutoff, integer floor transitions and widely separated sample sizes using high-precision arithmetic. Such finite checks support the universal inequalities proved above; they do not replace them.

2026-10-06 author-directed Codex audit: rechecked all the listed obligations against the complete derivation, including the exact squared constant and the unchanged one-map/orbit argument. No blocking error found. This is informal mathematical auditing under Quantyra's open-source workflow, not specialist certification. `python checks/check_grid_scale.py` passed 612 sample sizes and 173 integer grid transitions at 100-digit decimal precision, with derived coefficient approximately 126.323668677941. The revised version 0.2.0 manuscript compiled locally with Tectonic 0.17.0, without unresolved references or overfull boxes, and all eight rendered pages were visually inspected. PDF SHA256: `c8395d0cb0c55da8257cdd3ffe85c8d1b66c11e1a74e39d7ca6de645c52db463`.

Remaining to-do list: verify the focused delivery commit and hosted checks. The full inverse theorem's formalization continues separately under S013.
