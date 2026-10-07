# Confidence-sharpening delivery and limits

2026-10-07, E002/S020. The [finite concentration derivation](finite-data-confidence-sharpening.md) and reference implementation are delivered. Code commit `305a6dfa59e1a9894cc0003a13b3f7873935f716` is pushed. [Python certificates](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37697912438) and [supplementary proof/manuscript checks](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37697912388) passed at that exact commit. Formal source/dependency/audit/workflow bytes remain equal to accepted GCP commit `b7d762acc9c10ca881f8366f545f3998b0528448`; no local Lean or new GCP run occurred.

## Acceptance evidence

| Requirement | Result |
| --- | --- |
| Primary theorem and finite proof | Reeve's finite univariate result; separate grid Hoeffding joint event; explicit allocation, clipped sandwich, all-realizer global swap, deterministic selection and outward rounding. No unsupported finite multivariate DKW constant used. |
| CLI and independent checker | `split-dkw` default, explicit legacy `grid` selection, old schema-1 reports still valid, standard-library verification and deterministic/full-range fallbacks preserved. |
| Regression checks | Fourteen tests including exhaustive combinatorics, rational weak duality, both methods, allocation/rounding, corrupted calibrations, immutable caching and extreme-budget fallback. Both retained CLI reports verify without SciPy. |
| Observed certificates | Six seeded diagnostics at n=512,3072 in flat, FGM +1/2 and asymmetric +1/4 densities from K. All reported CDF, cell, point and coefficient targets covered under one common orientation in each case. This small sample is not a coverage-rate estimate. |
| Beyond the no-data CDF threshold | All three n=3072 certificates fall below 1/8, including both nonconstant examples. Legacy calibration of each identical forcing certificate remains above that threshold. This is a radius comparison, not uniform dominance of estimators centered at different CDFs. |
| Density assessment and paper gate | At the examined k=8 grid, all mean cell/point widths remain one and histogram error certificates remain one. Practical full-K density-paper gate stays no-go. No optimality, priority or useful density recovery is claimed. |
| Integrity and reproduction | [Results](../evidence/finite-data/sharpening-20261007.json), [terminal receipt](../evidence/finite-data/sharpening-run-20261007.json), exact source hashes, dependencies and integer/rational radius checks retained. Published/working PDFs and literature-candidate ZIP are unchanged. |

## Actual comparison

| n | Density | Legacy radius | New radius | CDF diagnostic error |
| --- | --- | ---: | ---: | ---: |
| 512 | Flat | 0.376802 | 0.2698555 | 0.0206451 |
| 512 | FGM +1/2 | 0.38070825 | 0.27376175 | 0.0207519 |
| 512 | Asymmetric +1/4 | 0.376802 | 0.2698555 | 0.0276422 |
| 3072 | Flat | 0.1629395 | 0.11308625 | 0.0152613 |
| 3072 | FGM +1/2 | 0.1629395 | 0.11308625 | 0.0106189 |
| 3072 | Asymmetric +1/4 | 0.16359054 | 0.11373729 | 0.0101192 |

CDF errors minimize over the two global orientations; the joint diagnostic explicitly checks one orientation for every guarantee. The asymmetric example has two different orientation errors. The three n=3072 reductions are 30.47%-30.60%; n=512 reductions are 28.09%-28.38%. Normal estimation times were 4.32-157.66 seconds. No additional memory profiling was performed; earlier memory measurements describe the legacy runs only. Data construction uses latent samples, but estimation receives only their full directed order. Legacy comparisons recalibrate the identical forcing certificate; they do not rerun a second legacy LP.

Reproduce with a fresh output:

```text
python tools/compare_confidence_calibrations.py --output comparison.json --sizes 512 3072
```

The result file's canonical LF SHA256 is `137a75f748d007c2b8af40b90e18002c8cc55e92dac8f994c0238175f0f2bebf`. All five recorded source hashes match current code and canonical Git bytes. The prior 80-trial archive, its negative legacy-calibration proof and its source provenance remain untouched.

## Remaining decisions and next research

The literature-only 0.3.1 candidate remains unpublished while the author's selection is pending. No DOI draft or publication was written. The new calibration is separate from that manuscript and is not silently added to it.

Density-specific improvement would need another scoped study: confidence bounds for local rectangle masses, explicit rank-boundary strips and density-dependent variance, followed by exact certificate and resource tests. A CDF constant reduction alone is insufficient. A successful method must preserve full K and one global ambiguity, improve on the flat coefficient prior where justified, and report useful simultaneous density widths. Reassess the dense graph implementation before enlarging the sample cap. These are future research suggestions, not delivered results or authorized publication claims.

Remaining to-do list: none for the selected calibration implementation/evaluation. Publication choice remains pending; useful density confidence remains future research.
