# Marked volume application result

S044, 2026-10-09 (Hawaii). **Park this candidate's operational application route.** The frozen comparison passes its validity, resource and sampling checks, but fails both absolute decision utility and improvement over established inference. This is a scoped simulator result, not a general impossibility of physical applications.

## Evidence and decision

The [protocol](protocol.json) and [comparator screen](README.md) were pushed at `232ff80d2bbc71b72214d8d243337f2673e5ead5` before evaluation. The first attempt stopped before sampling on a source-custody assertion: a historical calibration file contained committed CRLF bytes. Its bytes were unchanged. [Failure](evidence/v1/attempt-1/failure.json) and [diagnosis](evidence/v1/attempt-1/source-identity-diagnosis.json) are retained. Execution commit `ce8c4e7b98853f873796e3a8dac7a23c768a8f87` repairs the check to exact byte equality; no scientific scenario, seed, method or threshold changed.

The successful [summary](evidence/v1/attempt-2/summary.json) covers 24 known and 108 withheld strata, each with 64 trials: 8,448 new coordinate/thinning samples. Every count was checked against coordinate membership. The [independent artifact audit](evidence/v1/attempt-2/artifact-audit.json) recomputes all 528 method/stratum metric rows using closed binomial combinations instead of the runner's recurrence, independently integrates the geometry, and reconstructs genuine Lorentz chronology for 132 saved coordinate witnesses. It also checks all trial-record groups and the frozen sources. It does not replay every sampler or prove floating-point sampling semantics.

| Check | Result |
| --- | --- |
| Valid-method exact coverage | All 396 rows meet 95%; minimum approximately 95.240900%. |
| Valid-method wrong decision probability | At most approximately 2.459484% over the two nominated volumes and all strata. Empty model alarms count as wrong in these admitted models. |
| Calibration and controls | All 1,348 integer-tail certificates, four zero-sample cases and five deliberately invalid controls pass. |
| Sampling diagnostic | All 132 aggregate-count checks pass their frozen family error budget of 1%. |
| Candidate/reference reports | Identical to the independently implemented Aronow–Lee transform of the same Clopper–Pearson certificate in every case. |
| Useful-width gate | Fails in 18 of the 27 withheld n=1024, R<=5/4 strata. |
| Correct decisive judgment gate | Fails in all 27 gate strata. |
| Incremental improvement gate | Fails in all 27 gate strata because reports coincide. |

The following ranges are rounded summaries across nine withheld strata per row at n=1024. Correct decisive probability is averaged over the two fixed nominations. The exact rational probabilities and outward expected-width enclosures are in [strata.json.gz](evidence/v1/attempt-2/strata.json.gz); width enclosures are at most 1e-10 wide.

| Assumed retention ratio R | Probability of nonempty width <=0.1 | Mean correct decisive probability | Expected interval width |
| --- | --- | --- | --- |
| 1 | Approximately 1 throughout | 0.01642–0.29214 | 0.05448–0.05597 |
| 9/8 | 0.02314–0.60729 | 0–0.01234 | 0.09931–0.10540 |
| 5/4 | 1.66e-11–0.06234 | 0–0.000199 | 0.11981–0.14414 |
| 2 (sensitivity, outside advance gate) | 1.57e-38–0.06604 | 0–9.60e-14 | 0.11832–0.24359 |

The gate required at least 0.8 for both utility probabilities. The nominations and tolerance were fixed before sampling; some targets are near or at tolerance boundaries. These outcomes concern this demanding validation decision and sample budget, not every conceivable use of the intervals. Ignoring bias is unsafe under the specified models: its minimum exact coverage is approximately 7.85e-18. That diagnostic is not treated as an eligible competitor.

## Comparator interpretation

The binary sensitivity formula is established prior work, as documented in the [full source comparison](../../notes/physical-volume-selection-comparison.md). The candidate is identical to an eligible established counterpart with the same observations and calibration. It therefore fails a necessary condition for a strict width/decision improvement over the best applicable alternative. This is sufficient for the negative stopping decision. It is not an exhaustive ranking or a positive benchmark against the strongest method.

The frozen source screen identifies sharper exact intervals, including Blaker's construction; their endpoints were not implemented in this experiment. The candidate's duplication of the CP counterpart already prevents the claimed incremental advantage. A future positive advance would require an explicit stronger-comparator evaluation and a fresh scoped protocol.

## Resources and reproducibility

The successful run used 300.629 seconds and 57,431,331 Python-traced peak bytes (54.77 MiB), below the frozen 1,800-second and 512-MiB ceilings. The six run artifacts plus independent audit occupy 6,511,356 bytes, below 32 MiB. Tracemalloc excludes untraced native/process memory. Audit time was 36.005 seconds. The preserved failed source-custody attempt used 135.067 seconds before sampling; total recorded failed/run/audit elapsed time is approximately 471.70 seconds. This excludes development and source review.

| Measured successful-run stage | Seconds |
| --- | ---: |
| Shared calibration verification | 28.400 |
| Exact model-law metrics | 177.885 |
| Coordinate/thinning samples | 5.420 |
| Full relation construction | 18.246 |
| Candidate reports | 32.068 |
| Reference reports | 1.671 |

The methods share the precomputed certificate bank; its historical generation is not a newly measured cost. Wrapper and validation differences prevent a runtime-superiority claim. The candidate has no demonstrated accuracy or resource advantage. All 8,040 pre-existing tracked files were unchanged at execution and audit. The frozen application README remains a historical protocol document; this result supplies its completed disposition.

To reproduce, use a clean checkout of execution commit `ce8c4e7b98853f873796e3a8dac7a23c768a8f87`, the recorded Python/NumPy environment in [freeze.json](evidence/v1/attempt-2/freeze.json), and a new output directory. The runner additionally checks matching local/remote main, so its original custody check requires that recorded repository state or an explicitly recorded reproduction amendment. Never overwrite an existing attempt. To inspect the retained run, read the JSON/gzip artifacts and audit receipt; the audit refuses to overwrite its receipt. A new audit should use a separate evidence copy and the exact execution sources.

## Conditional stages

The failed advance gate means no operational observation simulator, existing-data/measurement study or resource-management chain is commissioned under this candidate. Detector ranges remain sensitivity assumptions, without instrument validation. The 1+1 result supplies no unproved 2+1/3+1 bridge. No carrying-capacity score, deployment readiness or environmental benefit is upgraded; the clock-geodesy adjacency remains at its provisional 44/100 assessment.

No new substantive theorem endpoint was introduced and no Lean invocation occurred. Statistical and geometric guarantees reuse accepted S040/S041/S046 proofs. Frozen prior experiments, mathematical acceptance and the three published manuscript families are preserved. S047 may use this decision after its own model/source audit; no quantum conclusion follows from it. No new manuscript is initiated by S044.

Remaining to-do list: none for the S044 technical comparison. The planning roadmap retains S039 and S042–S043; S047 is queued separately and S048 manuscript preparation remains proposed.
