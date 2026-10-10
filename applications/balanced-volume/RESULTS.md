# A finite decision gain warrants the stronger comparison

2026-10-10, S049. **The balanced conditional test passes the local feasibility gate in three prespecified settings.** It does not yet establish superiority over auxiliary-constrained inference or validate a physical application. The broader goal remains active.

## Decision and evidence

A simulator claims that the marked interval has normalized volume 5/16 within tolerance 1/32. The tested alternative has actual volume 1/4. Each method either flags that claim as inconsistent or returns unresolved. The ordinary argument bounds the probability of flagging a correct claim by 5%, uniformly over the admitted iid retained-event model and detector bounds. All methods receive the same marked-order information, n and R. None is given the detector pattern.

The candidate uses both the past and future of the midpoint anchor, whose generated masses are equal by the original uniform-marginal assumption. It conditions each of those counts against the incomparable category. Three implemented exact-tail comparators use the old past-only count, the pooled past+future count, or both separate marginal counts with the same balance identity. The last comparator prevents attributing the entire improvement merely to adding the future count.

The table gives probabilities computed directly from the multinomial law after the frozen Monte Carlo screen passed. These are floating-point finite-law calculations, not experimental frequencies, exact rational certificates or Lean results.

| n | R | Lower-retention category | Candidate correct flag | Best implemented comparator | Gain |
| ---: | ---: | --- | ---: | ---: | ---: |
| 1,024 | 1.25 | Future | 81.88% | 56.11% (pooled) | 25.77 percentage points |
| 2,048 | 2 | Past | 95.63% | 73.61% (past-only) | 22.02 percentage points |
| 2,048 | 2 | Future | 95.63% | 62.48% (balanced marginal) | 33.16 percentage points |

This is a specific useful simulator-checking consequence at matched sample size and false-flag budget. It is **not uniform dominance**: the method can lose to pooling in other settings. Three of 48 biased alternative settings pass the local gate. All 256 decision rows, including non-passing settings and 192 null settings, are retained in `results.json`; no new runs or thresholds were selected after observing the pilot.

## Verification

Protocol/implementation were pushed at `5ea83e4` before any pilot sampling. The first unexecuted protocol at `788fae4` was amended before execution to add n=2,048, prompted by the ordinary variance calculation; no outcomes had been examined. The screen uses 128 strata and 4,096 trials per stratum, totaling 524,288 multinomial samples. Its family-adjusted paired lower bounds exceed a 10-point improvement against every implemented comparator in the three passing settings. The maximum observed null false-flag rate is 2.906%; this is a diagnostic, not the uniform error proof.

Independent checks compare the population formula to 64 linear-fractional optimizations, validate extraction of past/future flags and invariance on twelve actual order matrices, compare two numerical test implementations on 11,176 small-count cases, and replay all saved decisions. Direct law integration covers 1,041,824 count pairs over the three confirming settings. Omitted marginal probability is below 1.7e-14 per setting; probability sums agree with one within 2e-14. A 1e-10 numerical comparison allowance is reported, without claiming interval-arithmetic certification. The improvements are much larger than that allowance.

Run `python applications/balanced-volume/pilot.py` and then `python applications/balanced-volume/audit.py`. NumPy/SciPy versions and input/source hashes are saved. The pilot took about 4 seconds and the independent audit about 35 seconds in this environment; these are not comparative runtime claims. `counts.npz` is an immutable saved trial artifact for replay; use `allow_pickle=False`. No Lean/Lake was run.

## Stronger comparison and physical work still required

[Tudball et al.](https://doi.org/10.1093/biomet/asac042) already extend bounded-selection inference with population moment constraints. Our sharp aggregate bounds are a closed-form special case of that established weighting idea. Their paper's section 2 and Appendix C give asymptotic inference with relaxed sample constraints; a matched finite-sample implementation has not yet been evaluated here. Consequently, the table is a gain over **three named implemented methods**, not a completed best-existing-method claim.

Next compare the auxiliary-constrained approach with the same categories, balance restriction, detector bound and error target. Check its assumptions and both equivalent target representations (past mass and half the pooled mass), and distinguish asymptotic inference from a finite guarantee. A further exact joint multinomial comparison may be needed if it materially changes the strongest eligible benchmark. Do not certify or publish a superiority claim first.

Physical validation must then justify independent retained sampling, calibrated relative detection bounds and the midpoint marginal probabilities. If the two anchor marginal probabilities are F_1 and F_2, balance error is exactly 1-F_1-F_2; it cannot be ignored or inferred from observed balance. Existing photon-calibration summaries and newly located camera-data download listings do not establish this bridge, and a coordinate partial order constructed from an image is not physical Lorentz chronology.

Remaining to-do list: complete the strongest matched comparison; establish a surviving decision advantage; validate its observation, anchor and detector-calibration assumptions with adequate physical evidence. The active goal is incomplete.
