# Practical degree estimator: bounded no-go

S039, 2026-10-09 (Hawaii). **Park the literal degree estimator as a practical candidate in the existing dense implementation.** Every possible successful report for 2<=n<=4096 has the flat density, radius 1/2 and width one. The fresh paired pilot confirms that behavior at n=512, then stops at its preset worker limit on the first n=3072 case. This resolves the bounded feasibility question; it is not a completed 28-trial grid or a universal impossibility theorem.

## What was executed and checked

The [method/constant audit](degree-density-practical-audit.md), [protocol](degree-density-practical-protocol.json), implementation, runner and planned artifact checker were pushed before evaluation at `194c87d27d8ad4464f8a12e2da17df6f8194c9d0`. Six mechanical test groups pass, including all 4,095 supported sizes, 172,767 occupancy-feasible mesh choices, small realizable orders, relabeling, invalid/corrupt inputs, exact polynomial formulas and the retained baseline interface.

The [original attempt](../evidence/degree-practical/v1/attempt-1) remains a failed execution with its [timeout receipt](../evidence/degree-practical/v1/attempt-1/case-14/resource.json) and [terminal record](../evidence/degree-practical/v1/attempt-1/failure.json). Fourteen valid trials completed: two per admissible model at n=512. The first n=3072 worker exceeded 600 seconds. Thirteen subsequent valid trials and the separate misspecified-density sample were not started. The worker included both methods, report checking and planned relabeling work; no partial stage log exists, so the interrupted cost cannot be attributed to a particular method or stage.

A [separate stopped-study audit](../evidence/degree-practical/v1/stopped-audit-1/artifact-audit.json) was authored after the timeout and pushed at `91a10f6099bae8522f318b8465c6eebeb8975d7c`. It preserves the original attempt byte for byte and changes no scientific threshold or method. It independently reconstructs all 14 retained full relations from Lorentz coordinates, checks 896 exact polynomial cells, reloads 28 method certificates and two additional relabel certificates, recomputes every completed density metric, and verifies the exact resource stop. Its status explicitly denotes an audited stopped study, not a successful full-grid execution.

The failed worker had not saved coordinates or a coordinate hash. A separately labeled deterministic replay archives its prescribed input from the same frozen seed, without rerunning estimation. These are reconstructed prescribed inputs, not recovered original bytes or a new successful trial. No remaining pilot or confirmation seeds were sampled.

## Paired outcomes

All completed baseline reports have valid exact outer certificates, with no solver fallback. Both implemented methods equal the flat no-data point estimate and return full-width point bands in every completed trial. The exact full-square errors below hold under one global identity/transpose; the polynomial evaluator uses complete cell extrema, not a finite grid maximum.

| Admissible model, n=512 | Trials | Error of each point estimate | Maximum simultaneous width |
| --- | ---: | ---: | ---: |
| Flat | 2 | 0 | 1 |
| FGM, coefficient -1/2 | 2 | 1/2 | 1 |
| FGM, coefficient +1/2 | 2 | 1/2 | 1 |
| Asymmetric, coefficient -1/4 | 2 | 1/4 | 1 |
| Asymmetric, coefficient +1/4 | 2 | 1/4 | 1 |
| Boundary-localized polynomial | 2 | 1/8 | 1 |
| Oscillatory Legendre polynomial | 2 | 1/16 | 1 |

All completed joint density checks cover. Each stratum has only two trials: its outward exact 95% binomial interval is approximately [0.1581,1]. These observations do not empirically validate 95% coverage. The candidate's original-K coverage is deterministic from its known-range flat branch; the retained method keeps its existing mathematical guarantee. The coordinate histogram remains an evaluator-only diagnostic without a confidence claim.

There is no completed n=3072 comparison or sampled misspecification outcome. Hand-fixed invalid-order/report controls did run. Their success must not be confused with execution of the unstarted density-misspecification sample.

## Decision and resources

The prespecified practical gate requires width<=0.9, radius<=0.45 and point error at least 0.05 below both paired baselines in its nonflat target regime. The source/constant audit proves that no report produced by this literal implementation can meet the width or radius conditions anywhere in its supported range. Its point estimate also equals the flat baseline identically. Thus the stopping decision does not extrapolate the two-replicate observations to an unknown population improvement probability. The larger worker independently triggers the preset resource stop; its outcome remains a timeout.

No parameter-only revision is warranted by the retained proof expression: occupancy requires m<=sqrt(n), while its displayed shell term is at least 192/m>=3 at all supported n. A new rank argument, different estimator or stronger justified model could change that conclusion; this audit does not rule them out. Such a substantive revision was not established here, so no revised candidate or conditional confirmation is selected. The precomputed confirmation test and its fresh seeds remain unused.

Successful workers consumed 307.479 seconds in total; the interrupted worker consumed 600.395 seconds. Including preflight/custody and orchestration, the original run elapsed 919.004 seconds. The largest successful worker took 34.589 seconds with peak RSS 130,879,488 bytes. The timed-out worker peaked at 1,772,720,128 RSS bytes and 1,766,547,456 committed bytes, below the 4-GiB memory ceilings. It failed the 600-second time limit. The independent audit elapsed 109.106 seconds, including its separate 20.948-second input replay. These totals exclude development/source review. Complete per-stage records exist for successful trials; no method-speed superiority is asserted.

The Windows supervisor prohibits children, caps committed memory and rejects RSS/time overruns. The 0.395-second timing overshoot is recorded rather than described as an exact instantaneous cutoff. The aggregate pilot ceiling was not exhausted; its per-worker stop ended the attempt. Increasing that limit cannot make the literal candidate's uncertainty informative.

## Preservation and scope

The audit verifies all 16 frozen sources and all 8,055 pre-existing tracked files. Nested Git attributes retain the new raw evidence bytes, including CRLF logs. Prior pilots, accepted Lean sources and the three published manuscript families are preserved. No new substantive statistical endpoint was introduced, no Lean invocation occurred and no cloud instance was started for S039. The separate S042 ordinary geometry work remains uncertified.

The frozen method/protocol documents remain historical records of the pre-evaluation state. This result supplies the terminal decision. It does not initiate a manuscript, DOI or field application. The stopped grid and unavailable failed-worker stage attribution are limitations of the evidence, not silently completed tasks.

Remaining to-do list: none for S039's bounded practical-feasibility decision. Continue the selected S042 foundations and gated S043 study; S047 is queued separately and S048 manuscript preparation remains proposed.
