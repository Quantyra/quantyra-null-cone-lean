# Physical evidence selection after the finite comparison

S049, 2026-10-10. The [finite balanced-volume comparison](../balanced-volume/FINITE-REFERENCE-RESULTS.md) parks promotion of the frozen four-tail candidate and retains a better exact reference. The next research decision needs an actual measurement task and physical calibration evidence. This screen adds two inspected primary-source leads; it neither changes the first negative detector experiment nor declares the goal complete.

## Cesium lifetime archive: useful physical data, insufficient observation record

[Pucher et al., Physical Review A 101, 042510 (2020)](https://doi.org/10.1103/PhysRevA.101.042510) measures an atomic excited-state lifetime from photon delays after periodically switching off an excitation laser. The [public archive](https://doi.org/10.5281/zenodo.3701333) includes detector histograms, experimental metadata, evaluation scripts and much larger raw-delay archives. We retrieved the full eight-page [author-hosted paper](https://www.adphys.eu/pdf/PRA2020.pdf) and inspected its experimental sequence, fitting method and systematic-error analysis. Paper SHA256: `e063c57ee992ab977613e96ba2afd0eee15a86051ef79ea18e69fd3c93dc6eb7`.

Downloaded and verified against the published MD5 values:

| Archive | Size | SHA256 |
| --- | ---: | --- |
| histograms.zip | 11,101,007 bytes | `4350154bc943bb7c58c7240455d4ff0429234d3f442c3fcb2a27c19cfe78326b` |
| scripts.zip | 5,219 bytes | `c5bbd58266262ea060e411c59499a9807f83520c6b90cb00719bbd5af3792f94` |
| figures.zip | 1,220 bytes | `df5983d7540d2057f272305a127abbe3df25460991d6117fbd7876e1d36efddc` |

The selected figure-3 metadata and two histograms are retained unchanged under [vendor/3701333](vendor/3701333/ATTRIBUTION.md), with full file hashes and license attribution. The API declares CC-BY-4.0 for the data. Author script headers instead specify CC-BY-SA-4.0; those scripts were only inspected, not copied or executed.

The figure-3 record specifies 1,899,069,473 excitation cycles of 50 microseconds, a 26.4-hour acquisition, and about 0.104 detected fluorescence photons per cycle. The stored fluorescence and reference histograms have 9,998 bins and respectively 197,711,476 and 129,240,344 counts. The declared photon totals exceed those histogram sums by 229 and 185 respectively. This small difference is recorded without assigning a cause or alleging a measurement error. The actual stored bin spacing is approximately 5.001 ns; analysis should use the supplied times rather than assume exactly 5 ns.

The archive description and inspected histogram script establish that each released raw datum is a **delay relative to the beginning of an excitation cycle**. The described format does not provide absolute timestamps or an explicit cycle identifier. The two detector streams are separate. Consequently a file of these delays cannot reconstruct all empty cycles, inter-event waiting times or the full detector history. A raw-file label alone does not make the observation adequate for independent sampling or recovery validation. We did not download the 1.47 GB, 9.35 GB and 21.71 GB raw-delay archives to discover a limitation already specified by their format.

The paper discusses a specified 22 ns detector dead time, background, fit-window effects, radiation trapping and observed drift. Its reference detector measures the excitation laser, not a known number of fluorescence photons reaching the measured detector. Neither that channel nor the inspected metadata supplies the relative category-efficiency bound and generated anchor balance required by the balanced-volume procedure. Aggregate histograms cannot independently verify temporal independence. The source's negligible-dead-time argument is an operating-model argument, not a calibration certificate for our assumptions.

**Disposition:** retain as a lawful physical-data source for a separately specified lifetime/measurement study; do not claim it validates our retained-event model. No lifetime fit, claimed correction to the authors' result or comparative improvement was performed in this screen.

## BrightEyes-TTM: better event history, a different calibration

[Rossetta et al., Nature Communications 13, 7406 (2022)](https://pmc.ncbi.nlm.nih.gov/articles/PMC9715684/) describes an open-source photon time-tagging instrument. We inspected its observation format, data-calibration section, instrument-characterization section and data availability. Its calibrated format retains absolute synchronization times, event indices, detector channels and relative photon times. This is a materially better candidate for temporal-history checks than a delay-only archive.

The [Zenodo record 4912656](https://doi.org/10.5281/zenodo.4912656), whose API metadata was retrieved, lists three CC-BY-4.0 raw datasets: fluorescence lifetime imaging (6,637,665,696 bytes), fluorescence spectroscopy (6,448,302,912 bytes) and fluorescence correlation spectroscopy (4,255,140,864 bytes). No multi-gigabyte raw file was downloaded in this screen.

The inspected calibration converts tapped-delay and cycle codes into times. It does **not by itself establish photon detection efficiency or generated category balance**. Correlation-spectroscopy and scanning data also cannot be silently treated as independent stationary retained samples. An absolute event history is necessary for some checks but insufficient for the whole model. The listed dataset description does not currently establish a separate, matched efficiency-calibration run.

**Disposition:** keep this lead for a concrete instrument-timing or photon-history task if its relevant calibration evidence is available. It is not yet selected as a validation experiment, and no biological, imaging-quality or spacetime-reconstruction benefit is claimed.

## Next selection gate

Choose a task for which the observable record, independently known or calibrated target, detector selection uncertainty and useful decision threshold are jointly available. Prefer an existing physical control or withheld calibration run. Specify the strongest applicable inference and decision cost before measuring performance. If a transfer changes the physical target from spacetime volume, state and justify that bridge explicitly. A constructed coordinate order or simulated thinning of physical measurements cannot substitute for detector calibration.

Remaining to-do list: identify adequate physical control/calibration data, specify the resulting decision and matched existing methods, then establish and validate a concrete benefit. The full user goal remains active; these two data screens do not complete it.
