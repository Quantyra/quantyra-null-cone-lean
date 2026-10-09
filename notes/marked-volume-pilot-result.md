# Marked volume: the first calibrated pilot passes

2026-10-09, S040/S041. **Continue the calibrated functional method.** The frozen probability-grid pilot passes validity, width and resource gates. This is a controlled mathematical/simulation result, not a validated physical detector or a completed research story. The exact formal boundary is recorded in the companion formal map.

The [protocol](marked-volume-protocol.json), [ordinary proof](marked-volume-finite-data.md), implementation, benchmark and tests were committed before sampling in `a26809c`. [Freeze receipt](../evidence/marked-volume/pilot-1/freeze.json) binds those five source files and their environment; the run checks that they remain unchanged. [Summary](../evidence/marked-volume/pilot-1/summary.json), [all cells](../evidence/marked-volume/pilot-1/cells.json), [rational endpoint tables](../evidence/marked-volume/pilot-1/interval-tables.json), and [geometry counts](../evidence/marked-volume/pilot-1/geometry.json) retain the results. No seed, sample size or gate was changed after execution. A separate [artifact audit](../evidence/marked-volume/pilot-1/artifact-audit.json) verifies all 1,348 intervals without SciPy, rejects all 2,688 adjacent inward grid endpoints, and therefore bounds each endpoint's outward approximation error by 1/65,536. It also checks the exact pre-run Git blobs and recomputes geometry coverage from retained counts.

## Findings

There are 300 probability configurations and four paired methods, giving 1,200 report rows. Each cell has 2,000 Monte Carlo counts. Numerical summation over the complete binomial law accompanies every row; for n=0 and n=64 the coverage sums are also exact rational numbers. Of the 600 rational rows, 450 belong to the three valid methods and 150 to the deliberately misspecified diagnostic. All returned binomial endpoints pass exact integer tail checks; zero outward adjustments and zero fallbacks were needed.

The minimum complete-law coverage among the valid methods is approximately 0.951071. The minimum exact rational coverage among the valid small-n rows is approximately 0.966807. These grid checks are implementation evidence; universal coverage is supplied by the mathematical argument, with its Lean status explicitly delimited below. The bias-ignoring diagnostic reaches coverage about `1.20e-19` despite reporting an ordinary nominal 95% binomial interval. That interval estimates detected-event probability, not physical volume.

At n=1024, the worst expected interval width over the prespecified volume fractions and retention patterns is:

| Maximum retention ratio R | Exact-tail method | Conservative analytic method |
| --- | ---: | ---: |
| 1 | 0.06214 | 0.08839 |
| 1.1 | 0.10938 | 0.13539 |
| 1.25 | 0.17195 | 0.19746 |
| 1.5 | 0.25874 | 0.28320 |
| 2 | 0.38717 | 0.40939 |

Both methods use the same counts and the same asserted retention-ratio bound. The no-data width is one. The preselected useful-width threshold was 0.20 for R<=1.25. Every such cell passes and improves on the analytic comparator. The higher tested ratios fail that width threshold in some cells; more events cannot remove their entire uncertainty because the nuisance floor at detected probability one half is `(R-1)/(R+1)`. Do not describe R<=1.25 as a universal practical limit outside this grid and chosen width target.

The entire benchmark took 277.11 seconds against a 900-second ceiling. Python-traced peak allocations were 4,774,983 bytes against a 512 MiB ceiling. This is the named Python allocation metric, not a measurement of total native-library or operating-system peak memory. Flag processing is linear in retained count; the conservative report uses integer square roots and rational arithmetic. Exact tail table preparation has a higher cost and was included in the measured run.

## Actual geometry checks and uncertainty

Four 200-trial checks draw event coordinates in the null square, generate either flat volume density or `1+(2u-1)(2v-1)/4` by rejection, apply independent detection, and compute the two actual chronological anchor flags. Anchors are fixed at `(0,0)` and `(1/2,1/2)` before sampling. Every trial retains 1,024 events. The target volumes are exactly 1/4 and 17/64. Constant detection gives the appropriate physical volume law; compensating detection makes the retained law uniform in both models.

Observed report coverage was 0.935 and 0.955 for the two flat configurations, 0.965 for polynomial density with constant detection, and 1.0 for polynomial density with compensating detection and R=5/3. Preserve the 0.935 result: 200 trials do not determine coverage to percentage-point precision. For 187 successes in 200 independent checks, the same exact-tail interval gives approximately `[0.8914,0.9650]`; the complete-law coverage for that flat configuration is 0.952905. No selection or rerun was used to conceal the fluctuation. The compensated polynomial case had mean report width approximately 0.24188, exposing the calibration cost.

## Decision and remaining proof work

Five independent Python tests passed before the run: exhaustive small coin configurations versus the integer tail recurrence, exact small-law coverage, invalid/missing observation inputs, deliberately corrupted float quantile proposals, and analytic/composition boundary cases. SciPy only proposes quantiles; exact rational checks determine whether a proposed binomial endpoint is usable. The implementation's exact arithmetic is tested Python, not kernel-executed machine code.

The formal work proves generic iid indicator concentration, observable marked membership, relabeling invariance, retention-mass inequalities, normalized retained probability measure, and a full analytic physical-volume probability bound. It does not yet certify the binomial count-law identity and exact-tail inversion implementation, the iid thinning/Poisson-process construction, or the complete S038 confounding counterexample. Refer to the accepted source manifest and explicit theorem statements; the Python pilot does not fill those proof gaps.

The evidence justifies S044's separately frozen withheld-geometry study after these proof obligations close. It also identifies a useful future statistical question: the sharp cost of imperfect detector calibration for one physical functional. That is a candidate for S046, not an already selected or proved extension. S039's full-density feasibility and S042/S043's geometric questions remain independent obligations.

Remaining to-do list: close the exact-binomial and process/obstruction proof bridges in S040/S041; execute S039, S042/S043, S044 and one justified S046 extension. Published manuscript files remain unchanged.
