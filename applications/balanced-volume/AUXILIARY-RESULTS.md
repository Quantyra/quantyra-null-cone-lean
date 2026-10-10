# One setting survives the auxiliary-constrained comparison

2026-10-10, S049. **A 19.19 percentage-point model-based gain survives twelve fixed variants of the published auxiliary-constrained procedure.** The two other original positive settings retain 9.68-point gains and do not pass the ten-point gate. Joint finite multinomial inference and physical validation are still required; this is not a completed best-existing-method or physical-use claim.

## Matched comparison

The [frozen supplementary protocol](auxiliary-protocol.json), [ordinary specialization](auxiliary-derivation.md), executable and audit were pushed at `f26eb7418378a7c4be211d50e08f6496320359d9` before any auxiliary comparator decisions were evaluated. Original candidate outcomes were already known. This is a transparent secondary comparison on all 128 preserved strata and 256 decision rows, not a newly independent confirmatory experiment. No candidate, saved counts or original benchmark artifacts were changed.

[Tudball et al.](https://doi.org/10.1093/biomet/asac042) provide bounded weighting with population constraints. The final article, published supplement and author code were retrieved and compared. We implemented their categorical relaxed-constraint objective, then its Wald adjustment, using three equivalent population target representations and four prespecified error allocations. Each receives the same categories, sample size, detector bound and balance identity. None receives the actual detector pattern. The author R package itself implements logistic-weight regression, so these results are from an explicit mathematical specialization, not an R package call.

An empty relaxed set returns unresolved. A second sensitivity convention flags it. The table favors whichever auxiliary representation, allocation and convention gives the largest correct-flag probability; these are separate procedures, not an unadjusted union offered as a valid test. All twelve variants and both conventions are retained in `auxiliary-results.json`.

| Setting | Candidate | Strongest evaluated auxiliary variant | Gain | Secondary gate |
| --- | ---: | ---: | ---: | --- |
| n=1,024, R=1.25, future retention reduced | 81.8779% | 62.6883% | 19.1896 points | Pass |
| n=2,048, R=2, past retention reduced | 95.6315% | 85.9538% | 9.6777 points | Fail |
| n=2,048, R=2, future retention reduced | 95.6315% | 85.9538% | 9.6777 points | Fail |

These are floating-point probabilities calculated directly from the multinomial law, not physical measurements or Monte Carlo estimates. All three use true volume 1/4 and nominated band [9/32,11/32]. The best variant uses the pooled target and flags empty sets: `shared_01` for the first setting and `shared_default` for the other two. In the preserved pilot, the surviving setting has a family-adjusted lower gain of 11.049 percentage points over every auxiliary comparator/convention and still passes all original comparator gates. Only one of the 48 biased alternative settings passes this expanded screen.

## Verification and limits

- Independent scalar root inversion checks 176 feasible-ratio cases, including rare categories.
- A separate linear-fractional-to-linear-program formulation checks 582 global objective extrema, with maximum disagreement below 1.2e-15.
- Ninety supplementary SLSQP checks use the original quadratic constraint. Five report a line-search status failure despite objective discrepancies below 1.1e-10 and original-constraint residuals within 1e-9. Their full failure records are retained. The successful global LP checks supply the independent optimizer evidence; we do not label every SLSQP run successful.
- Zero-count handling, category exchange and R=1 limits pass. No original pilot sample activates the zero-count guard.
- Direct law integration covers 1,041,824 count pairs. Omitted marginal mass is below 1.7e-14 in each case; guarded endpoint mass is negligible and explicitly retained. A 1e-10 numerical allowance is reported. This is not interval arithmetic, exact rational certification or Lean acceptance.

The largest sampled null flag frequency across auxiliary variants/conventions is 4.8584%; the largest null empty-set frequency is 4.5410%. These finite-grid diagnostics do not establish uniform validity. The source procedure is asymptotic. Boundary detector patterns also need explicit treatment of empty feasible sets and optimizer regularity; we do not claim its theorem automatically certifies every benchmark condition. The candidate's finite ordinary false-flag proof remains separate. Thus the asymptotic comparison does not close the requirement for matched finite validity.

The original finite-law audit and these calculations independently agree on all three candidate probabilities. The full original input hashes, frozen new source hashes, environment, diagnostics and law calculations are in `auxiliary-results.json` and `auxiliary-audit.json`. The evaluation took about 8.75 seconds and the audit about 13.06 seconds in this environment. These are reproducibility observations, not a comparative runtime advantage.

Reproduce without regenerating the original pilot:

```text
python applications/balanced-volume/auxiliary.py
python applications/balanced-volume/auxiliary-audit.py --freeze-commit f26eb7418378a7c4be211d50e08f6496320359d9
```

## Next scientific decision

The ordinary specialization identifies the exact null polygon for joint multinomial inference. A finite comparison must use that same balance and detector information, with a verified treatment of the continuous nuisance parameters. A grid maximum or asymptotic chi-square cutoff is not a uniform finite guarantee. [Resin's exact multinomial work](https://arxiv.org/abs/2008.12682) covers simple nulls; it is a relevant computation source, not by itself a solution to this composite-null optimization.

Physical evidence still needs to support retained independent sampling, relative detector efficiency and the anchor marginal probabilities together. Observed balance does not validate generated balance; an image-coordinate order does not establish physical Lorentz chronology. No current physical dataset validates those assumptions for this procedure. The frozen manuscripts and prior GCP certificates remain unchanged.

Remaining to-do list: complete the joint finite comparison, then validate a surviving decision advantage's observation, anchor and detector-calibration assumptions with adequate physical evidence. S049 and the full user goal remain active.
