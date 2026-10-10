# S043 restricted 2+1 validation and dimensional decision

2026-10-10. **The bounded study is complete: 550 cases, with every sample
replayed and every complete relation count independently reproduced.**
The informative-certificate computation gate passes. The prespecified
small-sample point-improvement gate fails at both withheld parameters.
Retain the 2+1 implementation as a reproducible research benchmark and park
new 3+1 formalization pending a distinct scientific use and stronger ordinary
quantitative argument. This is an investment decision, not an impossibility.

## Frozen scope and evidence

The [protocol](geometric-pair-numerical-protocol.json) and
[implementation derivation](geometric-pair-numerical-design.md) were pushed
before evaluation. Version 2 froze at
`1c307399c04b82c4108183a2db898a051edecd15`, matching remote main with a clean
worktree. The retained [freeze](../evidence/geometric-gauge/pair-numerical-v2/freeze.json)
records eight source hashes, snapshots, Python 3.13.7, NumPy 2.5.3, SciPy
1.18.1 and the Windows environment. The [independent summary and raw inventory](../evidence/geometric-gauge/pair-numerical-v2/audit/summary.json)
are authoritative for all strata and exact rational reports.

Version 1 failed in argument parsing before creating any case or sampling.
Its source, plan, stdout and terminal resource outcome are preserved. The
[pre-data amendment](geometric-pair-launch-amendment.json) corrects argument
forwarding and adds a subprocess test. It changes no seed, sample size,
threshold, resource ceiling or statistical rule. Version 2 had no evaluation
retry or tuning. Seven deterministic tests passed before its freeze.

The existing [S042 acceptance](geometric-pair-audit.md) supplies the complete
continuous-law theorem: 1,276 exact GCP reports, proof commit
`f4672c4ea5290e65759253e8052efae270702cbb`, endpoint
`time_pair_geometric_confidence3`. No Lean source changed and no Lean/Lake
execution occurred in this numerical study. The conservative rational
implementation uses the accepted inequalities plus the explicitly derived
inverse-rounding allowance. Python execution itself is not a Lean-verified
program. The smooth reconstruction converse remains external.

## Outcomes and interpretation

The repeated study used 32 cases per stratum: five primary parameters at
each of n=128, 512 and 2,048, plus two withheld parameters at n=2,048.
All **544/544** small cases selected the no-data midpoint. The raw inverse
is a separate diagnostic, with the following withheld parameter errors:

| Parameter | Midpoint/policy MAE | Raw inverse MAE | Required raw MAE | Gate |
| --- | ---: | ---: | ---: | --- |
| 1/6 | 0.083333 | 0.112129 | at most 0.075 | Fail |
| 1/3 | 0.083333 | 0.134247 | at most 0.075 | Fail |

This misses the frozen 10% improvement threshold at both withheld points.
It does not prove statistical impossibility or uniform inferiority at other
sample sizes. The policy protects the established worst-case radius while
the raw inverse is noisy at these small sizes. At the central parameter
1/4, the midpoint has zero error, so the inverse cannot uniformly improve
every parameter's point error.

All six separately designated large cost cases selected the inverse:

| n | Parameter | Policy parameter error | Geometric upper bound | Conservative radius | All-pairs seconds |
| ---: | --- | ---: | ---: | ---: | ---: |
| 33,338 | 0 | 0.020416 | 0.003062 | 0.037499535 | 12.015 |
| 33,338 | 1/4 | 0.021788 | 0.003268 | 0.037499535 | 11.992 |
| 33,338 | 1/2 | 0.013288 | 0.001993 | 0.037499535 | 11.970 |
| 74,606 | 0 | 0 | 0 | 0.024999891 | 60.136 |
| 74,606 | 1/4 | 0.044485 | 0.006673 | 0.024999891 | 60.974 |
| 74,606 | 1/2 | 0 | 0 | 0.024999891 | 66.122 |

The geometric column is `(3/20)*absolute_parameter_error`, an upper bound
on the original geometric distortion, not its computed exact value. The
endpoint zeros result from clipping on these particular samples. There is
one repetition per cost cell: no empirical-coverage or typical-error claim
follows. All three n=74,606 runs meet the frozen radius-at-most-0.025 and
resource requirements. This radius is about one third below the no-data
radius 0.0375. The n=33,338 crossover improvement is only about 0.000000465.

Every reported upper bound lies within its reported radius. In the small
strata this is uninformative: the policy radius is deterministically valid,
and the raw radii are at least 0.155, exceeding even the global geometric
upper bound 0.075 from the parameter range. Each 32/32 numerical event has
an exact 95% binomial interval approximately [0.8911,1]. That interval does
not establish a 95% continuous-law coverage guarantee; the theorem supplies
that guarantee under its original assumptions. Samples here approximate
the continuous law on a finite grid. Zero grid-boundary rejections occurred,
which does not eliminate the rounding difference between the laws.

## Cost, correctness and reproducibility

All 23 workers passed. Total supervised execution took **273.75 seconds**;
the largest worker took **67.31 seconds**, below its 120-second limit. Peak
worker RSS was **43,204,608 bytes (41.2 MiB)** and peak job commit was
32,456,704 bytes. The separately supervised audit took **109.84 seconds**,
with peak RSS 109,449,216 bytes, within its 900-second/512-MiB limits.
These are local numerical timings, not cloud build timings or acquisition
costs, and exclude authoring, Git transport and interpretation.

Each n=74,606 case counts all 2,782,990,315 unordered pairs. Streaming tiles
avoid a stored dense matrix; a hypothetical n-by-n one-bit matrix alone
would occupy 695,756,905 bytes. The measured count includes actual chronology
construction from simulation coordinates; only `(n,R)` reaches the estimator.
No physical procedure for obtaining those relations is supplied.

The audit reproduced every coordinate array from its seed, checked exact
integer domain/overflow guards, and independently recounted every complete
sample with a time-sorted future-row implementation. Unbounded Python-integer
scalar oracles cover all n=128 cases and 64-point subsets elsewhere. Rational
brackets, tail inequalities, rounding allowances, errors, resources and
planned-case completeness all pass. The raw inventory has **1,707 files,
12,357,948 bytes**, excluding the audit's own artifacts. Source snapshots,
coordinates, stdout, timings and exact reports are retained. The delivery
verifier checks raw staged Git bytes and proof/manuscript preservation.

## Separate 3+1 investment decision

**Park new 3+1 formalization.** Computation is feasible for this restricted
2+1 certificate, but useful small-sample performance and a physical
observation model remain unestablished. Adding a coordinate alone supplies
neither missing ingredient. The experiment does not show that 3+1 recovery
is impossible, nor does it invalidate the positive 2+1 theorem.

The relevant existing baseline is already dimensional. Roy, Sinha and Surya
derive the flat ordered-pair factor
`Gamma(d+1)*Gamma(d/2)/(4*Gamma(3d/2))` in equations (6) and (11), using the
future-interval integral and Appendix (75). At d=4 it equals 1/20; the
comparability probability is 1/10. These are established flat formulas,
not new results of this program. [Primary source, PDF pp. 4-5 and 19-20](https://arxiv.org/pdf/1212.0631v1).
The listed arXiv edition was checked on 2026-10-10 (v1 only); the previously
retained PDF hash and bounded source review remain in the
[source record](../evidence/geometric-gauge/ordinary-pair-audit/sources.json).
This is not an exhaustive priority or journal-edition comparison.

| Obligation before a 3+1 follow-up | What can be reused and what must change |
| --- | --- |
| Specific scientific question and observation law | Name an identifiable quantity and why dimension four matters to a simulation or measurement. Order samples alone still do not provide scale, dynamics or a detector model. |
| Genuine Lorentz geometry and loss | Use one time and three spatial coordinates. Extend proper-time curves, quotient/topology, volume/gauge transport and coupling distortion; the accepted geometry is currently specialized to dimension three. |
| Normalized admissible family | The same time-quadratic idea would center at `E_flat[t^2]=1/15`, obtained from `4*integral_0^1 t^2*(1-t)^3 dt`. Recheck all bounds and normalization; the conformal length weight becomes a fourth root. This is an ordinary candidate, not a new certified model. |
| Actual informative pair law | Recompute the weighted future-interval moments and prove a positive slope on the proposed parameter interval. The known flat value alone gives no conditioning constant for the perturbed family. |
| Finite geometric guarantee | Derive a dimension-four forward constant and a useful inverse/no-data comparison. Generic disjoint-pair, permutation and Bernstein arguments can be reused after the new model bridge is proved. Overlapping pairs still are not independent. |
| Quantitative investment gate | Show an ordinary complete argument whose constants answer the named question; freeze matched comparisons, sample/acquisition cost, precision and resource limits before experiments or formalization. |

No 3+1 proof campaign or new story is commissioned by this decision. Reopen
only with a target-specific benefit and a complete plausible quantitative
argument. The selected next research step is S047's bounded quantum
measurement source/model audit; its laboratory route does not require
3+1 reconstruction. The conditional causal-set field branch keeps its own
stability gate. S048 manuscript preparation remains proposed separately;
this delivery does not alter a published PDF or create a DOI.

Remaining to-do list: none for S043; next selected work is S047.
