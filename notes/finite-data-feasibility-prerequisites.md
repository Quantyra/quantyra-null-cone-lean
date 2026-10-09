# S031 pilot prerequisite audit

2026-10-08, before pilot sampling. The v1 study and JSON protocol remain immutable. This audit fixes the implementation details allowed within those two variants, not a changed target or confidence budget.

## Mathematical gate

The [comparison](finite-data-feasibility-comparison.md), [local coverage argument](finite-data-local-mass-feasibility.md), and [same-class information limit](finite-data-information-limit.md) are written before estimator sampling. Both Bernstein and exact-binomial variants have an ordinary finite coverage argument and exact checker contract. Neither is represented as Lean certified. Benchmark K membership is verified as follows.

All five formulas are polynomials, hence smooth on a neighborhood of the square. The factors 2u-1, 2v-1 and 6v²-6v+1 integrate to zero on [0,1], so both marginals are exactly one. For FGM, |c|<=1/2 gives range [1/2,3/2] and Euclidean gradient norm <=2 sqrt(2)|c|<=sqrt(2)<2. For the asymmetric family, |2u-1|<=1, -1/2<=6v²-6v+1<=1 and |12v-6|<=6. At |c|=1/4 the range is [3/4,5/4] and gradient norm is at most sqrt((1/2)²+(3/2)²)=sqrt(5/2)<2. The flat case is immediate. Positivity, normalization and the original Euclidean bound thus hold, without importing a stronger uniform derivative condition.

The independent evaluator uses exact rational polynomial integrals and extrema: endpoint u, endpoint v, and the asymmetric v=1/2 critical point when inside the cell. Products of the one-variable factors attain extrema at these combinations. Supremum on a half-open cell equals the extremum on its closure by continuity, so these computations cover the whole square, including one-sided boundary values. One identity/transpose must validate all point/average/error claims at once. Finite-precision rejection sampling is an experimental approximation to iid sampling, not a proof of the theorem; repeated coordinate ties are retained as failure.

## Frozen choices

- Both separate candidates use k=8 and delta_m=delta_cell=1/40, without intersecting their unallocated events.
- Bernstein searches an outward 10^-6 tolerance grid using a rational exponential upper bound with 512 subdivisions; exact binomial endpoints use denominator 2^20.
- Every permitted degree cutoff is assessed on the one simultaneous event. The checker validates the actual endpoints, counts, forcing tree and LP duals rather than trusting numerical optimization.
- The histogram is the midpoint of pointwise bands. It is checked against half the maximum width. Baseline split-DKW retains its original output and error semantics.
- Pilot samples are the ten prespecified seeds; all three procedures receive the identical serialized order. No estimator receives coordinates, true ranks, the family or its coefficient. These are used only in generation/evaluation.
- No-data comparison is computed analytically. No oracle run or memory repeat is planned initially. The ten-case pilot determines whether the eighty fresh paired cases are warranted; no confirmation seed is generated during pilot work.

## Resource gate and provenance

The Windows runner attaches each numerical worker to a Job Object before numerical imports or data generation. It prohibits child processes, caps committed memory at 4 GiB, and polls the OS lifetime peak working set every 10 ms. Since children are prohibited, the root peak covers the allowed process tree. An RSS excess terminates/rejects the run; instantaneous overshoot is not described as a hard RSS reservation. A 600-second watchdog terminates the job. No accepted run may have peak RSS above 4 GiB. Worker import, I/O, evaluation and independent certificate reload/check are inside these conservative per-run limits. The sum ledger includes preparation and resource probes as well as estimator work. No new paid cloud resources are used.

Native job working-set limits were tried during setup but unavailable without an additional Windows privilege. They were replaced before sampling by measured peak-RSS rejection; that setup failure produced no research sample. The retained preflight runs test timeout, low-limit allocation failure and child denial; the final preflight also actively crosses a small RSS threshold and verifies rejection. These tests are safety checks at small limits, not performance trials. Microsoft documents the [job controls](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_basic_limit_information) and [OS working-set counters](https://learn.microsoft.com/en-us/windows/win32/api/psapi/ns-psapi-process_memory_counters); committed bytes and resident bytes are reported separately.

The runner writes its commit, source hashes, protocol hash, interpreter/DLL and numerical package RECORD hashes before the first sample. Shared input and forcing artifacts retain exact JSON and compressed hashes. Each report refers to those immutable artifacts to avoid duplicating large witnesses; loading checks all hashes and supported uncompressed sizes before verification. Every terminal failure gets its original log/resource record and deterministic range fallback. Nothing is dropped from the denominator.

Regression checks include exact binomial tail sums, finite rejection probabilities and endpoint monotonicity, exhaustive small-order realizer alignment, boundary/empty erosion cases, corrupted calibration/mass/bands/duals/histograms, and shared-artifact rejection. The pre-pilot code commit plus test/probe receipts are the internal implementation gate. Further formal certification remains a separately selected GCP-only task if the decision warrants it.
