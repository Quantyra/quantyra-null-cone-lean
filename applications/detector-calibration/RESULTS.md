# First detector screen: no demonstrated decision advantage

2026-10-10; S049 remains active. Protocol and executable were pushed before execution at `59dd082`. This bounded screen is complete; the broader practical-use goal is not. Run `python applications/detector-calibration/screen.py`, followed by `python applications/detector-calibration/audit.py` from the repository root, with NumPy/SciPy. No Matplotlib or Lean invocation is needed. The adapter executes the inspected original numerical definitions without their plotting setup; the vendor source bytes are unchanged.

## Mathematical consistency

Thirty hard-dead-time cases and twenty-four soft-recovery cases agree with an independently constructed stationary Markov chain to at most 1.12e-16. The independently coded geometric calculation agrees with the deposited numerical code on six SNSPD probability checks to at most 4.45e-16. The source's 95% recovery convention is verified. Its 0.999 and the converged 0.999999999999 cutoffs select the same SNSPD prefix, so tail truncation does not explain this comparison.

The ordinary derivation gives a genuine model-level counterexample: two fully blind pulses and a true input click probability of 1/2 yield an output probability of 1/4. Geometric-age inversion instead returns 4/9. It makes the wrong point decision at the preselected threshold 19/40; the classical renewal inverse makes the right decision. This demonstrates the consequence of the approximation within the stated model. It is not an improvement over established renewal inference, and it is not a physical validation.

## Retrospective physical check

Eight original SNSPD calibration observations were used. Each method fitted one zero-flux efficiency on the lower-count four observations and predicted the upper-count four, fixing the recovery times to the independently acquired histogram/configuration. This is a local holdout from published data, not an independent replication. Relative flux RMSE uses the reconstructed reference flux; that reference has uncertainty and shares inputs with measured efficiency.

| Method | Withheld relative flux RMSE | Maximum absolute relative flux error |
| --- | ---: | ---: |
| Published geometric-age approximation | 0.4095% | 0.5158% |
| Established recovery/renewal calculation | 0.5884% | 1.1138% |
| Independent stationary-chain implementation | 0.5884% | 1.1138% |
| Hard dead-time renewal without partial recovery | 1.7745% | 2.0663% |

The proposed correction has **worse descriptive prediction error** than the published comparator in this small holdout. Its agreement with the strongest renewal baseline also leaves no distinct methodological advantage. Replacing the older model is not warranted by these data. This result does not refute the ordinary renewal argument; the measurements may depart from its idealizations and the calibration/recovery inputs have uncertainty.

Shifting the common reference flux by +/-0.5% preserves the ordering. This sensitivity is nearly absorbed by refitting eta_0; it does not validate the common calibration or account for all errors. No independence of reported error bars, p-value, certified coverage or statistically significant ranking is claimed. We did not retune the recovery parameters or split after observing this result.

## Disposition and next research gate

Retain the licensed data, exact model counterexample, original-code comparison and reproducible negative prediction result. Park the **renewal correction alone** as a candidate for new practical superiority; do not start a Lean campaign or revise the prepared manuscript on that basis.

The next candidate must change the decision procedure or information use, not rename renewal inference. Screen finite uncertainty for recovery calibration and the value of time-resolved observations before implementation. Mandatory prior-art checks include [Wayne, Bienfang and Polyakov's autocorrelation characterization](https://doi.org/10.1364/OE.25.020352), [Raupach et al.'s count-rate-dependent calibration](https://doi.org/10.1103/PhysRevA.105.042615), and the existing photon-inhibition policies listed in `SOURCES.md`. Only their abstracts/institutional descriptions were screened at this milestone; full-text/data comparisons remain pending. This is an ordered next investigation, not evidence that it will succeed.

For a candidate to proceed: specify an actual measurement decision and tolerable error/cost; derive the complete ordinary argument; compare against the best applicable established use of the same data; show a quantitative advantage. Then seek adequate physical records with ordered timestamps or a justified acquisition law, separate calibration and validation runs, and shared-error information. The current deposited summaries do not establish those assumptions.

Remaining to-do list: identify and demonstrate a distinct decision benefit, then validate the observation and calibration assumptions with adequate physical evidence. The active goal is not complete.
