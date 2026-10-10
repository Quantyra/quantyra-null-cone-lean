# Finite checks of the volume/calibration rate

2026-10-09 (Hawaii), S046. **The frozen deterministic checks pass. Retain the transformed exact-binomial report for practical use.** The joint-rate theorem supplies a uniform accuracy scale and lower obstruction; its conservative upper constants yield no narrower interval in the tested report grid. The direct primary-proof comparison and final comparator-applicability review remain open before manuscript disposition.

## Prespecified comparison

The [protocol](physical-volume-finite-protocol.json) and [runner](../checks/validate_volume_rate_finite.py) were committed and pushed in `d59e567d64f2661d3970022a3ffee183fbdf9764` before numerical execution. The successful attempt used unchanged protocol and runner bytes at `2dc6f4f2994fdfed3c97870094cf8d771668eb61`. [Freeze and source identities](../evidence/volumerate/finite-v1/attempt-2/freeze.json).

The model remains the original K with fixed marked anchors, unknown global retention in [1/R,1], and retained sample size n. Every comparator receives the same membership count, n, R and known physical target range [1/8,3/8]. All reports are intersected with that range. Empty intersections are retained as empty sets, with zero width and no coverage. This geometric range is specific to the selected class and quarter-square target; the earlier pilot covered a different grid of physical volume fractions and is preserved separately.

The four methods are the existing outward-grid Clopper–Pearson interval followed by retention transformation, the existing transformed Hoeffding interval, the new theorem's count-fraction interval with radius `2*min(1,1/sqrt(n)+(R-1)/(R+1))`, and the fixed known-range report. At n=0 all return the known range. There are no generated samples, random seeds, Monte Carlo replications or numerical quadrature.

The formula grid uses n=q² for q=1,2,4,8,16,32,64. R includes eight fixed rational values in [1,2] and the prespecified points around the sampling/calibration crossover, including exact equality where admitted. Interval comparisons use n=0,1,4,16,64,256,1024: all counts through n=64 and seven specified counts at each larger size. Complete-law coverage and expected width are calculated only through n=64, for three admitted polynomial geometries and uniform, inside-low and inside-high piecewise constant detectors.

## Results and independent checks

- Independent coefficient integration checks eight polynomial densities: normalization, both uniform marginal polynomials, quarter-square target and second moment. Exact product arithmetic checks the finite divergence bound through n=4096. All 71 rate cells satisfy the frozen joint strict-gap inequalities, including R=1 and both sides of the crossover. [Formula results](../evidence/volumerate/finite-v1/attempt-2/formulas.json).
- All 104 distinct rational binomial reports pass integer tail certificates, with no fallback. The complete paired report grid contains 1,108 count/R cases. Joint-rate widths are greater in **732**, equal in **376**, and smaller in **zero** cases. These are reportwise comparisons on the specified grid, not a universal dominance proof. [Interval tables](../evidence/volumerate/finite-v1/attempt-2/intervals.json).
- All **1,656** exact finite-law coverage checks meet 19/20. The minimum is approximately **0.96288634**; its exact fraction is retained. Expected widths have outward rational display enclosures of width at most 10^-12. Empty-report probabilities are recorded exactly. [Coverage tables](../evidence/volumerate/finite-v1/attempt-2/coverage.json).
- All five negative controls are rejected: incorrect target and second-moment denominators, equality at a strict separation boundary, an unclamped ambient detector, and an invalid point binomial interval.
- The [separate artifact audit](../checks/audit_volume_rate_finite.py) verifies that every prespecified cell occurs once, rechecks committed source identities and the 104 certificates, recomputes coverage with integer tail sums, and verifies expected widths and empty probabilities using 261 distinct binomial PMF recurrences. It passes all 1,656 rows. [Audit receipt](../evidence/volumerate/finite-v1/attempt-2/artifact-audit.json).

For illustration, these are **realized widths** at the prespecified n=1024, k=256; they are not expected widths or full-law coverage calculations at that size. Displayed values are rounded.

| R | Transformed exact binomial | Transformed Hoeffding | Joint-rate interval | Known range |
| --- | ---: | ---: | ---: | ---: |
| 1 | 0.053970 | 0.088388 | 0.125000 | 0.250000 |
| 5/4 | 0.137225 | 0.170836 | 0.250000 | 0.250000 |
| 2 | 0.249039 | 0.250000 | 0.250000 | 0.250000 |

## Resources, custody and interpretation

The successful run took **199.33 seconds**, against the frozen 900-second ceiling. Peak Python-traced allocation was **59,031,222 bytes (56.30 MiB)**, against 512 MiB. This excludes untraced native/process allocations. The supplementary artifact audit took 3.15 seconds. Python 3.13.7, NumPy 2.5.3 and SciPy 1.18.1 were used. These resource records support reproducibility, not a comparative speedup claim. [Run summary](../evidence/volumerate/finite-v1/attempt-2/summary.json).

The [first attempt](../evidence/volumerate/finite-v1/attempt-1/failure.json) passed its formula and zero-sample checks, then stopped because SciPy was absent from the selected interpreter. Its partial tables, failure and source manifest were committed before retry. Installing the original pilot's NumPy/SciPy versions restored that environment. The retry changed no source, grid, method, threshold or scientific claim.

The run hashes verify preservation of all **8,024** pre-existing tracked files, including manuscripts, earlier acceptance evidence, the original pilot and the failed attempt. No pilot was rerun or overwritten. No new Lean invocation was made. The [797-report GCP certification](physical-volume-joint-certification.md) remains the authority for the universal mathematical theorem; these finite executions do not certify Python semantics or extend that theorem to a physical detector.

Decision: retain the exact-binomial implementation and the joint theorem for their demonstrated purposes. The tested upper-rate interval supplies no practical width advantage over the existing report. The lower theorem still establishes a calibration floor even for arbitrary independently randomized estimators using the entire marked order. The finite grid neither establishes optimal interval constants nor completes a comparison against all applicable prior work.

After the Aronow–Lee proof is inspected, resolve whether another comparator applies under the same observations and finite-coverage requirement. Freeze any required amendment before evaluating it. S044 retains its separate withheld-geometry and operational-model gates; these calculations do not validate an instrument or a resource-management benefit.

Remaining to-do list: S046 direct source comparison, final comparator-applicability check and any required frozen amendment, then manuscript disposition; S039 and S042-S044 remain selected.
