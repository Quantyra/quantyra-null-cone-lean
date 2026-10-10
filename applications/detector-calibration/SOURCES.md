# Source and observation screen

Accessed 2026-10-10. Public primary sources; no email connector or author contact. Citations denote scope, not endorsement of our inference.

| Source | Role and boundary |
| --- | --- |
| Georgieva et al., [EPJ Quantum Technology 13, 82 (2026)](https://doi.org/10.1140/epjqt/s40507-026-00540-9) | Pulsed single-photon calibration comparator. SNSPD recovery is measured separately; SPAD reset parameters are fitted. Shared photodiode calibration uncertainty and recovery/electronics effects prevent treating all measurements as independent exact truth. |
| Ivanov et al., [data and scripts, version 1](https://doi.org/10.5281/zenodo.18662495) | Sixteen files, API metadata license CC BY 4.0. `vendor/18662495` preserves original bytes, with creator attribution and original MD5 plus our SHA256 manifest. Numerical columns contain measured count rate, efficiency and standard uncertainty; flux is reconstructed from these quantities. An autocorrelation histogram is not an ordered arrival record. |
| Lopez et al., [EPJ Quantum Technology 7, 14 (2020)](https://doi.org/10.1140/epjqt/s40507-020-00089-1) | Established pulsed dead-time correction for dead time between one and two pulse periods, with a small-dark-count approximation. Its zero-dark limit equals q=p/(1-p). Provides the special-case check, not a general soft-recovery formula. |
| Krause and Walenta, [arXiv:2507.10361v1 (2025)](https://arxiv.org/abs/2507.10361v1), section II.1 | Established age-dependent hazard, survival and inverse mean waiting time. Continuous Poisson illumination differs from Bernoulli pulses. Its general renewal principle supplies the strongest mathematical baseline after changing the illumination law explicitly. Our discrete calculation is an application of this principle, not a claimed new principle. |
| Koerner et al., [Photon Inhibition for Energy-Efficient Single-Photon Imaging (2024)](https://arxiv.org/abs/2409.18337) | Already studies resource reduction with adaptive inhibition and physical captures. Any future photon-budget candidate must compare the applicable established policies; resource savings cannot be presumed from adding a stopping rule. Not evaluated in this screen. |

## Dataset suitability

The calibration curves and recovery histogram can support a retrospective model consistency check. They cannot by themselves establish independent thinning, source independence, calibrated finite-sample coverage, temporal drift bounds or operational decision improvement. There are no ordered run-level timestamps/exposure records or full joint uncertainty budget among the deposited files. Preserve the distinction between missing data and a demonstrated violation.

In the SNSPD comparison, fit only eta_0 on the lower-flux half; fix the recovery parameters from the independently acquired histogram/configuration. Hold the higher-flux half out of that fit. This prevents local fitting leakage but does not undo publication-level selection or provide a second independent physical campaign. A common 0.5% reference-calibration error does not average away; include a sensitivity shift, and do not label residual scores p-values or certified confidence.

SPAD afterpulsing corrections and dead-time summaries are available, but their reset times were inferred from calibration responses. Reserve those devices for later model-development checks; they are not independent physical validation of fitted reset parameters. The present bounded screen uses SNSPD only.

Remaining to-do list: execute the frozen screen, assess the need for another accessible physical dataset, and design a distinct decision comparison without overstating these measurements.
