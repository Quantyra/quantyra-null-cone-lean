# S043 frozen numerical design

The [machine-readable protocol](geometric-pair-numerical-protocol.json)
specifies the complete evaluation before any study samples are drawn.
This is a bounded validation of the accepted S042 restricted 2+1 result.
It does not commission another Lean campaign or alter the accepted theorem.

## Observable and executable certificate

The estimator receives only sample size and the count of all strict order
relations, including transitive relations. A comparable unordered pair
contributes exactly one directed relation. Streaming all pairs therefore
constructs the sufficient statistic without storing a dense relation matrix.
The complete relation-test/count time is measured; hypothetical dense storage
is reported separately. Nothing measures the cost of acquiring causal order
from a physical experiment.

The accepted constants are `p(0)=8/35`, `p(1/2)=185489/750750`,
`v=104849697629/563625562500`, `L=3/20`, `c=13738/375375` and
`K=L/c=225225/54952`. The accepted Bernstein argument uses `m=floor(n/2)`;
overlapping pairs are not treated as independent trials. For confidence .95,
the executable uses rational `s=369/100 > log(40)`, certified by the first
21 positive exponential-series terms. Its rational upper root `b` satisfies
`m*b^2 >= 2*s*(v+b/3)`. This directly makes the accepted tail at most .05.

Forty-eight monotone bisections bracket the clipped inverse by `[lo,hi]`.
The returned midpoint differs from the ideal inverse by at most
`epsilon=(hi-lo)/2`. The geometric forward inequality adds `L*epsilon`
to `K*b`; the selected estimator uses the inverse if this conservative
radius is at most `3/80`, and otherwise returns the no-data midpoint.
This is a slightly conservative executable implementation of the accepted
inequalities, not a claim that its rational approximation is definitionally
equal to Lean's real-valued inverse. The inequality checker independently
checks the bracket, polynomial tail condition and rounding allowance; it
does not accept reports by comparing them with regenerated reports.

The probability argument remains valid if the numerical branch depends on
the bracket width: the midpoint never exceeds its deterministic radius,
and every inverse-branch failure implies failure of the same fixed Bernstein
event. The bracket rounding allowance is pointwise. No extra union bound or
independence of the selected branch is assumed.

## Sampler and finite arithmetic

For flat volume on the open diamond, `|t|` has CDF `1-(1-|t|)^3`,
the sign is symmetric, and each spatial slice is a uniform disk. The inverse
CDF and disk area map in the protocol generate that law in real arithmetic.
Rejection with envelope `1+9*theta/10` gives density
`1+theta*(t^2-1/10)`: its flat mean is one. The continuous diagnostic moment
is `E[t^2]=1/10+13*theta/700`, using `E_flat[t^4]=1/35`.

Actual samples are floating-point approximations rounded to the grid
`2^-24`. Rounded points outside the open diamond are rejected and counted.
The saved arrays therefore have a finite-grid law, not the exact continuous
iid law. Empirical validation cannot replace the theorem or certify this
discrete law. All integer coordinates are bounded by `2^24`; differences
are bounded by `2^25`, so the three-square chronology predicate fits safely
in signed int64. Exact-null pairs are excluded without a tolerance. Scalar
unbounded-integer fixtures and a separately implemented time-sorted counter
check the tiled computation. Every saved seed is replayed in the audit.

Record the generator, seed, call shapes, versions, source hashes and stored
coordinates. NumPy only promises stream reproducibility under specified
conditions; this study does not promise identical arrays across builds or
machines. See the [official compatibility policy](https://numpy.org/doc/stable/reference/random/compatibility.html).

## Interpretation and limits

There are 544 repeated small cases in 17 strata and six large cost cases.
The small cases necessarily select the midpoint under the conservative
certificate. Their inverse estimates are point-accuracy diagnostics; the
policy's deterministic guarantee is not empirical evidence of sharpness.
Report parameter errors and `L*absolute_parameter_error` as a certified
upper bound on geometric distance. Do not label that upper bound the actual
quotient geometric distance. At 32 repetitions, exact binomial coverage
intervals are broad. The six one-repetition cost cases cannot assess
Monte Carlo coverage. They test whether the informative certificate can
be evaluated within the fixed resource budget.

The raw-inverse point gate and large-sample cost gate are separate, with
thresholds fixed in the protocol. Neither establishes a practical physical
application, superiority of the selected policy or a full-class modulus.
The 3+1 decision must list the additional geometry and identifiability
obligations and explain the expected benefit before expanding formalization.

Windows Job Objects enforce one process and a hard committed-memory ceiling;
the 10-ms RSS/time watchdog rejects overshoot rather than claiming an
instantaneous RSS cap. A failed worker stops later work; there are no
evaluation retries or adaptive sample-size changes. Audit is separately
bounded. Source and data are retained even if a gate fails.

Remaining to-do list: execute the frozen protocol, audit retained results,
and decide whether the evidence warrants 3+1 investment.
