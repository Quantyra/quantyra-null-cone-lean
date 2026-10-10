# Exact calibration dominates the frozen candidate

2026-10-10, S049. **The frozen four-tail candidate cannot pass the positive-improvement gate against a stronger finite reference.** Exact calibration of the same conditional counts retains every candidate rejection and adds others at the same uniform 5% false-flag budget. The pointwise inclusion proof is independent of the pilot outcomes and suffices to decide this candidate's comparative gate.

The reference was constructed during this comparison by specializing standard exact rejection-region calibration. It is not misrepresented as a pre-existing published balanced-volume algorithm or a call to an external package. Its success establishes that the frozen candidate is suboptimal, not that balanced-volume inference has no practical value. Retain the improved finite procedure as a reusable baseline; the full user goal still requires a decision benefit over applicable existing methods and physical validation.

## Quantitative result

| Original positive setting | Frozen candidate | Calibrated finite reference | Reference improvement |
| --- | ---: | ---: | ---: |
| n=1,024, R=1.25, future retention reduced | 81.8779% | 88.4530% | 6.5751 points |
| n=2,048, R=2, past retention reduced | 95.6315% | 97.7044% | 2.0730 points |
| n=2,048, R=2, future retention reduced | 95.6315% | 97.7044% | 2.0730 points |

These are correct-flag probabilities computed from the multinomial law, with true volume 1/4 and nominated band [9/32,11/32]. They are not physical measurements. Previous gains against the three marginal comparators and the asymptotic auxiliary variants remain correct, but they do not establish superiority of the frozen candidate over this reference. The reference also has higher power than those implemented variants in these settings; that is an application-specific model calculation, not a new general statistical principle or a completed best-existing-method claim.

## Finite guarantee and verification

For each A:C or B:C conditional count, calibrate a two-tail rejection region over the whole null probability interval, with budget 1/40. Its rejection probability as a function of the binomial probability has no interior maximum; checking its two endpoints therefore covers the entire nuisance interval. Integer arithmetic certifies the endpoint probabilities and inclusion of the original 1/80-per-tail regions. Averaging over each random subset size and applying a union bound to the two conditional tests gives the full multinomial false-flag bound of 1/20. No independence between the two tests is assumed. [Complete ordinary derivation](finite-reference-derivation.md).

The protocol, derivation, implementation and audit were pushed at `77eba1ba30a2e283443a9d00b08a7d3bf03327b7` before creating the reference tables or evaluating their decisions. This is a declared secondary comparison after earlier candidate outcomes were known. All original inputs remain unchanged.

Two integer tables cover every conditional size from 0 to 1,024 at R=5/4 and from 0 to 2,048 at R=2. An independent fixed-size binomial-coefficient recurrence checks **6,148 endpoint size inequalities and 3,074 candidate-region inclusions**, separately from the Bernoulli-step CDF recursion used to construct the tables. The maximum endpoint sizes are approximately 0.0249987900 and 0.0249992822; the actual checks compare integers with 1/40, rather than rounded decimals. Another 8,775 exhaustive small-count cases check exchange invariance, zero subsets and nesting. The ordinary argument establishes validity and inclusion for all n, while the numerical audit certifies the stored finite tables. No Lean certification is claimed.

The preserved samples replay without any discrepancy from the original candidate decisions. Direct law integration covers 1,041,824 count pairs, agrees with the earlier independent candidate calculation and omits less than 1.7e-14 probability per setting. Power numbers are floating-point calculations with a reported 1e-10 allowance, not exact rational power certificates. All hashes, rows and results are retained in `finite-reference-results.json` and `finite-reference-audit.json`. Construction/evaluation took about 6.11 seconds and the independent audit about 11.37 seconds here; no comparative runtime advantage is claimed.

```text
python applications/balanced-volume/finite_reference.py
python applications/balanced-volume/finite_reference_audit.py --freeze-commit 77eba1ba30a2e283443a9d00b08a7d3bf03327b7
```

## Research decision

Park promotion or formalization of the frozen four-tail candidate as an incremental method. A full two-dimensional likelihood-ratio calibration is unnecessary to establish its negative improvement gate because pointwise dominance is already proved. Such joint calibration may further improve the reference; neither optimality nor a complete comparison for a future replacement method is claimed.

The next application should start with a physical decision and adequate calibration evidence, then compare against this finite reference and other applicable methods. The [physical-data screen](../detector-calibration/physical-data-screen.md) inspects a new cesium lifetime archive and an absolute-timing instrument dataset. Neither currently validates all assumptions. Further synthetic tuning alone does not close the user goal.

Remaining to-do list: select a physically grounded decision with adequate observation/calibration evidence, establish a surviving comparative benefit, then validate it. S049 and the full goal remain active.
