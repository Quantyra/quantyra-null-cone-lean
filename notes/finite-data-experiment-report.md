# Finite-data experiments and paper decision

2026-10-07, E002/S019. Evidence: [80-trial JSON](../evidence/finite-data/benchmark-20261007.json), [generator](../tools/benchmark_finite_data.py), [method/coverage proof](finite-data-certified-method.md), [calibration limitation](finite-data-calibration-limit.md). Decision: deliver the inspectable reference baseline; **do not promote it to a practical full-K density-estimation paper yet**.

## Model and execution

Five smooth densities in K: flat; `1+c(2u-1)(2v-1)` with c=+-1/2; and asymmetric `1+c(2u-1)(6v^2-6v+1)` with c=+-1/4. Both factors have zero integral, hence uniform marginals and unit volume. FGM gradient bound is 2sqrt(2)|c|<=sqrt(2); asymmetric bound is sqrt(40)|c|<=sqrt(40)/4<2. Density bounds lie in [1/2,3/2]. Asymmetric cases exercise the global transpose ambiguity.

Rejection sampling uses envelope 3/2 and Python's seeded pseudorandom generator. Sizes 128 and 512, eight trials per density/size, grid k=8, requested delta=1/20. All 80 distinct seeds and parameters are retained. Only the directed order enters estimation; latent coordinates evaluate output. CDF errors include empirical jump corners and upper one-sided limits; density/band extrema include polynomial critical points. Orientations are compared as whole functions, never point by point.

Ten separate memory repetitions reuse the first seed of each case; they are not additional independent trials. Earlier runs were intentionally superseded because profiling inflated runtime and 512-point runs exposed redundant incoming-edge scans. [Measurement redesign](../evidence/finite-data/profiling-run-replaced.json) and [propagation optimization](../evidence/finite-data/propagation-run-replaced.json) preserve terminal outcomes. The accepted run completed the full original scope after the tested optimization.

## Results

All 80 trials returned rationally checked outer certificates and covered cell averages, point bands, CDF and coefficient error in one common global orientation. This is selected-model software evidence, not proof of uniform coverage. Each case has 8/8 joint coverage, with a 95% Wilson interval approximately [0.676,1]; these samples cannot establish 95% coverage empirically. The ordinary proof supplies the theoretical guarantee.

| n | Density | Mean CDF error | Mean certified CDF radius | Mean cell/point width |
| ---: | --- | ---: | ---: | ---: |
| 128 | flat | 0.05773 | 0.73055 | 1 / 1 |
| 128 | FGM -1/2 | 0.05197 | 0.72665 | 1 / 1 |
| 128 | FGM +1/2 | 0.05932 | 0.72860 | 1 / 1 |
| 128 | asymmetric -1/4 | 0.05271 | 0.71883 | 1 / 1 |
| 128 | asymmetric +1/4 | 0.05190 | 0.72958 | 1 / 1 |
| 512 | flat | 0.02579 | 0.37827 | 1 / 1 |
| 512 | FGM -1/2 | 0.02709 | 0.38071 | 1 / 1 |
| 512 | FGM +1/2 | 0.02549 | 0.38046 | 1 / 1 |
| 512 | asymmetric -1/4 | 0.02608 | 0.37949 | 1 / 1 |
| 512 | asymmetric +1/4 | 0.02838 | 0.37827 | 1 / 1 |

All reported mean density-band widths remained one, the full admissible range. Coefficient errors were 0 for flat, 1/2 for these FGM extremes and 1/4 for asymmetric densities, matching the flat baseline's performance, with conservative reported bound one. These settings did not demonstrate useful density resolution. Full-range 100% coverage is not practical inference.

Normal estimation/certificate verification took 2.339-9.084 seconds, median 4.071 seconds, on this Windows Python 3.13.7 workstation. Sampling/order construction and validation timings are separate. Python-traced peaks in separate profiles were 5,259,105-24,346,438 bytes; tracked arrays are included, untracked native solver allocations/total RSS are not. These environment-specific measurements are not a sample/performance budget. NumPy 2.5.3 and SciPy 1.18.1 were isolated from Lean.

## Gate and next research

The forcing certificate removes an occupied-grid prerequisite and reports actual all-realizer ambiguity, but confidence constants remain conservative. A no-data flat estimate already guarantees CDF error <=1/8 and coefficient error <=1/2 in K. The [exact limitation](finite-data-calibration-limit.md) proves this grid certificate cannot beat that CDF prior at 95% confidence for any n<=4096, even with zero forcing ambiguity. This is not an information lower bound and does not exclude better estimators/calibrations.

The delivered outcome is a constructive, independently checked order-only realizer, forcing/rational confidence certificates, LP outer bands, reproducible tests and a justified limitation. A new-paper claim of useful full-K density inference fails the current gate. Reopening needs sharper empirical-process/marginal calibration, data-dependent confidence-set restrictions or a substantive rate/limit theorem, then nontrivial simultaneous bands and defensible priority assessment. Parametric toys, more simulations alone or Lean encoding of this conservative bound would not meet that gate. Future Lean commands remain remote GCP-only.

The literature-only manuscript revision and optional publication candidate remain separate; no finite-data claim is inserted into published DOI artifacts.

Remaining to-do list: none for implementation/evaluation delivery. Future research: sharpen full-K confidence before presenting a practical estimator paper.
