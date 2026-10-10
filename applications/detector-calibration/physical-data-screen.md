# Physical evidence selection after the finite comparison

S049, 2026-10-10. The [finite balanced-volume comparison](../balanced-volume/FINITE-REFERENCE-RESULTS.md) parks promotion of the frozen four-tail candidate and retains a better exact reference. The next research decision needs an actual measurement task and physical calibration evidence. Three primary-source leads are inspected below. The newest beam-telescope screen confirms that misses are retained, but leaves reference independence unresolved. These screens preserve the first negative detector experiment and do not complete the goal.

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

## Beam telescope: misses retained, reference independence still open

[Beam Telescope Analysis (BTA)](https://github.com/SiLab-Bonn/beam_telescope_analysis/tree/9ab568b787a9c018207dff6a33b9ef2148153e1a) processes multiple detector planes observing particle-beam events. Its [EUTelescope example](https://github.com/SiLab-Bonn/beam_telescope_analysis/blob/9ab568b787a9c018207dff6a33b9ef2148153e1a/beam_telescope_analysis/examples/eutelescope.py) identifies DESY Run36 at approximately 5 GeV/c, six Mimosa26 planes spaced 150 mm apart, and copies named hit fixtures. The precise derivation of `Merged_small.h5`, used to generate the fitted regression fixture, still needs tracing. The example's run description is not by itself a complete provenance chain for that processed subset.

The [screen protocol](beam-reference-protocol.json) and [executable](beam_reference_screen.py) were pushed at `e0807380e352e6713a0b3007d8da9c91e8934df2` before reading event rows or hit/miss outcomes. Schemas, row counts, stored fit arguments and upstream source were already inspected. This is retrospective analysis of an existing regression fixture. It is not a new physical experiment or a blinded performance evaluation.

The downloaded `Tracks_result.h5` is 107,329,094 bytes; SHA256 `136d3cd99c06bb75f1a4ea0d2e9fbbe2261ce0bfac3b8229372d14429e8d0cfb` matches its upstream Git LFS identity. The [result](beam-reference-results.json) records ten pinned source-file identities, stored fit arguments and software versions. Source/data bytes stay in an external cache. The software has an MIT license; an independent physical-data redistribution license was not established, and no HDF5 fixture is vendored here.

For DUT3, selected from the upstream efficiency test before outcomes, the saved table contains **56,792 tracks across 9,937 events**, including **1,047 rows without a DUT3 hit**. Every row has hits on the other five planes. Of those events, **9,249 contain multiple saved tracks**. Requiring quality bits only on the other five planes and the upstream `track_chi2 < 15` cut retains 19,412 rows, including 313 without a DUT3 hit. A missing assigned hit is not automatically a known particle missed by the sensor: association, acceptance and reconstruction can contribute.

The fixed event-ID split is descriptive. Its earlier/later reference-quality subsets contain 9,845/9,567 rows and 177/136 absent DUT3 hits. Both halves have now been inspected; neither is available as an untouched validation set. No efficiency estimate, stability test, iid guarantee or comparative gain is inferred from these counts.

All six saved tables together contain 343,156 rows. All 108 comparisons of hit bits with finite x/y coordinates and positive cluster-hit counts agree. A separate streaming recount using absent coordinates, rather than hit bits, reproduced 24 DUT3 row, missing-hit, event and multiplicity counts. Frozen protocol/executable bytes match their Git snapshot. Result SHA256: `4de557bfc57966b3c4b7b9abc506ddd93d60446198d9af27dbf0d4f9f1013f4d`. These checks validate extraction, not detector calibration.

The [fitting source](https://github.com/SiLab-Bonn/beam_telescope_analysis/blob/9ab568b787a9c018207dff6a33b9ef2148153e1a/beam_telescope_analysis/track_analysis.py) confirms that the default final fit excludes the evaluated detector and does not require its hit. However, the preceding candidate finder defaults to using all planes for extrapolation. DUT3 can therefore influence downstream hit association before its exclusion from fitting. Default exclusion from the final fit does not establish an independent reference denominator. Multiple tracks per event also prevent treating table rows as automatically independent observations. Trigger selection, alignment reuse and matching uncertainty remain unvalidated.

The upstream efficiency regression test additionally selects hits on every plane before evaluation. That fixture selection is not a defensible comparator for absolute efficiency: correcting it would not demonstrate an advantage over properly configured established tag-and-probe analysis. The source already supports excluded-detector fits and Kalman tracking; neither is our contribution.

**Disposition:** retain this concrete reference-data lead. Before a calibration study, trace the fixture to original hits and construct or verify reference tracks without the evaluated detector influencing selection or association; account for event clustering and use a separate validation record. Any beam-efficiency or fluence decision would be an explicit transfer to a new physical target, not validation of spacetime reconstruction. No Lean/Lake invocation, new hardware, outreach or publication was performed.

Reproduce the structural screen with Python, NumPy, h5py and hdf5plugin:

```text
python applications/detector-calibration/beam_reference_screen.py --cache-dir PATH_OUTSIDE_REPOSITORY --fetch --output applications/detector-calibration/beam-reference-results.json
```

## Next selection gate

Choose a task for which the observable record, independently known or calibrated target, detector selection uncertainty and useful decision threshold are jointly available. Prefer an existing physical control or withheld calibration run. Specify the strongest applicable inference and decision cost before measuring performance. If a transfer changes the physical target from spacetime volume, state and justify that bridge explicitly. A constructed coordinate order or simulated thinning of physical measurements cannot substitute for detector calibration.

Remaining to-do list: resolve the beam reference's provenance and selection dependence, specify a physical decision and matched existing methods if the data qualify, then establish and validate a concrete benefit. The full user goal remains active; these three data screens do not complete it.
