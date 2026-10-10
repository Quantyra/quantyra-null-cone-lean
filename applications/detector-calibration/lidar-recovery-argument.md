# Recovery dependence: argument before a range comparison

S049, 2026-10-10. This bounded development check resolves whether a specific
model extension is worth a ranging comparison. It does not claim a new
general estimator, a range improvement or physically certified coverage.

## The opening and the strong comparison

For a complete detection history, let `u(t)` be time since the last recorded
event and `phi(t)` laser phase. A useful candidate intensity is

`mu(t) = g(u(t)) [b + a f(phi(t)-tau)] + h(u(t))`.

Here `g` permits gradual sensitivity recovery and `h` permits an additional
age-dependent detection contribution. This is a proposed observation model;
neither function is calibrated by the present check. An off-pulse histogram
alone cannot distinguish these two mechanisms or unknown incident variation.

The hard-cutoff range likelihood sets `g(u)=1{u>=d}` and `h=0`. Its score at
the true range parameters has expectation

`E integral [mu_true(t)-mu_model(t)] grad log(mu_model(t)) dt`

on its positive-intensity region, by the counting-process compensator
identity. Hence a recovery error need not average away with more detections.
It causes range bias only if its projection onto the *nuisance-adjusted range
score* is nonzero. Detecting age dependence alone does not prove that projection
is consequential; amplitude/background adjustment may absorb it. This is the
hardest unresolved step for a useful range result.

A candidate recovery-aware implementation must be compared with fitted
hard-cutoff joint likelihood, robust one-step estimation, a flexible recovery
likelihood and a guarded likelihood using only mature recovery ages. Every
method receives the same calibration and event record. Guarding the likelihood
must retain all detections as history; deleting detections and pretending to
have observed another hardware policy is invalid. Generic recovery models and
likelihood methods are existing tools, not new Quantyra principles.

Before building those range fits, test the simpler consequence of a hard
cutoff: in fixed off-pulse phase strata, the intensity after the cutoff is
constant with event age. Allow each phase stratum its own rate, fit the best
cutoff, and let this null fit the evaluation data themselves. The alternative
is fitted exclusively on the earlier chronological half. A surviving
predictive difference justifies the next range comparison; it cannot replace it.

## Exposure and likelihood, including dependent events

For an age/phase cell `j,k`, accumulate the detection count `N_jk` and actual
time at risk `E_jk`. Intersect every interval after a recorded event with the
fixed analysis window, age bounds and periodic phase bounds. A final right
censor contributes exposure and no event. The first recorded event supplies
the initial state and is not itself scored. At the split, retain its preceding
event. Detections outside the scored region still reset age.

The continuous-time partial log likelihood is

`ell(lambda) = sum_jk [N_jk log(lambda_jk) - E_jk lambda_jk]`.

This follows by applying the usual intensity likelihood on a predictable
subset. It does **not** assume independent Poisson cell counts: the exposures
are random and depend on earlier events. The history dependence remains in
the likelihood. It assumes a complete history, the stated conditional
intensity and exact timestamps.

For the hard-cutoff model, all scored detections must have age at least `d`.
For fixed `d`, each phase rate is maximized at `N_k/E_k(d)`. Since exposure
decreases as `d` increases, the optimized log likelihood is nondecreasing
until `d` reaches the smallest scored gap. Thus the global supremum over the
declared cutoff interval occurs at that gap clipped to the interval. This
comparison includes a fitted nonintegral cutoff; a fixed 198 or 200 ns baseline
would be unnecessarily weak. A supremum at an observed endpoint is interpreted
as a limit if the intensity convention uses a strict inequality.

Train the alternative cell intensities using the fixed positive smoothing
rule `(N_jk+0.5)/(E_jk+0.5/0.015)`. On the later half define

`log e = ell(frozen_training_alternative) - sup_null ell`.

Under the exact continuous-time null, the numerator-to-true-null likelihood
ratio has conditional expectation at most one. The fitted-null denominator
is at least the true-null likelihood, so `E[e | training history] <= 1`.
Markov's inequality then bounds `P(e >= 100)` by 1%. This is a specialization
of existing split-likelihood inference, not a new universal inference theorem.
The comparison needs no independence between time halves, provided the
intensity model and predictable history are correct.

**Physical limitation:** digitally rounded timestamps are not exact event
times. The executable reports the continuous-time model score and two
prespecified rounding perturbations. These do not integrate or bound every
latent timestamp configuration. They therefore do not establish an exact
physical 1% test, an afterpulsing diagnosis or recovery calibration. Additional
dependence, changing illumination and electronic losses remain alternatives.

## Primary-source comparison

- [Jorgensen and Johnson (2026)](https://arxiv.org/html/2605.23210v1)
  supply exposure-aware sufficient statistics, efficient joint likelihood and
  robust one-step estimators in a periodic Bernoulli model with hard dead time.
  Their fixed-model efficiency result does not establish calibration of a
  different age-dependent intensity. The source implementation is pinned in
  the existing lidar manifest; do not claim their estimators are generally weak.
- [Kitichotkul et al. (2025), Appendix A](https://arxiv.org/html/2507.09386v1)
  derive continuous-time lidar likelihoods, including free-running acquisition.
  Using a counting-process likelihood is established methodology.
- [Wayne et al. (2017)](https://www.nist.gov/publications/simple-autocorrelation-method-thoroughly-characterizing-single-photon-detectors)
  characterize reset and afterpulse effects using correlation measurements.
  Recovery diagnostics are prior art; an age effect here is not a discovery of
  the phenomenon.
- [Georgieva et al. (2026)](https://doi.org/10.1140/epjqt/s40507-026-00540-9)
  explicitly model a noninstantaneous recovery function. A flexible or calibrated
  recovery model must be included before claiming an incremental range benefit.
- [Wasserman, Ramdas and Balakrishnan (2020)](https://doi.org/10.1073/pnas.1922664117)
  provide split-likelihood universal inference. The argument above spells out
  the conditional-intensity specialization and its additional physical limits.

Remaining to-do list: establish a consequential range-score effect and matched
decision improvement, validate pulse/recovery/reference assumptions, and confirm
the result on the reserved measurements.
