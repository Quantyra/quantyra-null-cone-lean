# Physical evidence selection after the finite comparison

S049, 2026-10-10. The [finite balanced-volume comparison](../balanced-volume/FINITE-REFERENCE-RESULTS.md) parks promotion of the frozen four-tail candidate and retains a better exact reference. Three primary-source leads are inspected below. The newest beam milestone traces the small fixture to its parent record and replays an established association algorithm with the evaluated detector removed from per-event inputs. Physical calibration and a comparative decision benefit remain open. These screens preserve the first negative detector experiment and do not complete the goal.

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

## Beam telescope: reference associations reconstructed, physical calibration open

[Beam Telescope Analysis (BTA)](https://github.com/SiLab-Bonn/beam_telescope_analysis/tree/9ab568b787a9c018207dff6a33b9ef2148153e1a) processes multiple detector planes observing particle-beam events. Its [EUTelescope example](https://github.com/SiLab-Bonn/beam_telescope_analysis/blob/9ab568b787a9c018207dff6a33b9ef2148153e1a/beam_telescope_analysis/examples/eutelescope.py) identifies DESY Run36 at approximately 5 GeV/c, six Mimosa26 planes spaced 150 mm apart, and copies named hit fixtures. The subsequent check below traces `Merged_small.h5` exactly to the full merged fixture. The original raw-file conversion and trigger configuration are not independently reconstructed from the example's run description; its old EUTelescope example URL currently returns 404.

The [screen protocol](beam-reference-protocol.json) and [executable](beam_reference_screen.py) were pushed at `e0807380e352e6713a0b3007d8da9c91e8934df2` before reading event rows or hit/miss outcomes. Schemas, row counts, stored fit arguments and upstream source were already inspected. This is retrospective analysis of an existing regression fixture. It is not a new physical experiment or a blinded performance evaluation.

The downloaded `Tracks_result.h5` is 107,329,094 bytes; SHA256 `136d3cd99c06bb75f1a4ea0d2e9fbbe2261ce0bfac3b8229372d14429e8d0cfb` matches its upstream Git LFS identity. The [result](beam-reference-results.json) records ten pinned source-file identities, stored fit arguments and software versions. Source/data bytes stay in an external cache. The software has an MIT license; an independent physical-data redistribution license was not established, and no HDF5 fixture is vendored here.

For DUT3, selected from the upstream efficiency test before outcomes, the saved table contains **56,792 tracks across 9,937 events**, including **1,047 rows without a DUT3 hit**. Every row has hits on the other five planes. Of those events, **9,249 contain multiple saved tracks**. Requiring quality bits only on the other five planes and the upstream `track_chi2 < 15` cut retains 19,412 rows, including 313 without a DUT3 hit. A missing assigned hit is not automatically a known particle missed by the sensor: association, acceptance and reconstruction can contribute.

The fixed event-ID split is descriptive. Its earlier/later reference-quality subsets contain 9,845/9,567 rows and 177/136 absent DUT3 hits. Both halves have now been inspected; neither is available as an untouched validation set. No efficiency estimate, stability test, iid guarantee or comparative gain is inferred from these counts.

All six saved tables together contain 343,156 rows. All 108 comparisons of hit bits with finite x/y coordinates and positive cluster-hit counts agree. A separate streaming recount using absent coordinates, rather than hit bits, reproduced 24 DUT3 row, missing-hit, event and multiplicity counts. Frozen protocol/executable bytes match their Git snapshot. Result SHA256: `4de557bfc57966b3c4b7b9abc506ddd93d60446198d9af27dbf0d4f9f1013f4d`. These checks validate extraction, not detector calibration.

The [fitting source](https://github.com/SiLab-Bonn/beam_telescope_analysis/blob/9ab568b787a9c018207dff6a33b9ef2148153e1a/beam_telescope_analysis/track_analysis.py) confirms that the default final fit excludes the evaluated detector and does not require its hit. However, the preceding candidate finder defaults to using all planes for extrapolation. DUT3 can therefore influence downstream hit association before its exclusion from fitting. Default exclusion from the final fit does not establish an independent reference denominator. Multiple tracks per event also prevent treating table rows as automatically independent observations. Trigger selection, alignment reuse and matching uncertainty remain unvalidated.

The upstream efficiency regression test additionally selects hits on every plane before evaluation. That fixture selection is not a defensible comparator for absolute efficiency: correcting it would not demonstrate an advantage over properly configured established tag-and-probe analysis. The source already supports excluded-detector fits and Kalman tracking; neither is our contribution.

### Subsequent provenance and association check

The [rebuild protocol](beam-rebuild-protocol.json), [executable](beam_reference_rebuild.py) and [upstream MIT notice](beam-source-NOTICE.txt) were pushed at `4e6a72872877ca81d76b9490b0fbe1510bcfc1d9` before evaluating reconstructed associations. The provenance identity had already been inspected and is explicitly retrospective. The executable loads only named routines from hash-verified upstream source; it does not introduce a new tracker.

`Merged_small.h5` contains 99,478 rows in 10,000 events. Selecting those event IDs from `Merged_result.h5` gives the **identical dtype and identical record bytes**. The parent has 1,116,936 rows across 112,700 events, leaving **102,700 other event IDs**. Its SHA256 is `624c6c4bd617b9daf470475288bb6e0888209c3969774203088229eb13bd7c3e`; the small fixture's is `1b4f472b6b6727e56310453f57863ab365b78261edaa538c654b7c2f3c03c3a8`. The stored merge arguments identify six input clustered files. We have not evaluated DUT3 response or association outcomes on the other events. They are available for a separately specified retrospective validation; their separation in event ID does not itself establish statistical independence.

A metadata-only inspection of the named DUT0 clustered input also links its processing to the example's raw hit and mask files. That 44,255,791-byte fixture has SHA256 `55f64b7c4524d80180fbea0344c96236757ab0c8f6274f241753cc519b790809`; its `cluster_hits` arguments specify charge-unweighted clustering with three-pixel spatial distance and zero frame distance. This extends the recorded chain but does not independently replay clustering or establish original trigger/live-time calibration.

The six-plane replay matches **all 74 fields on all 99,478 candidate rows** in the saved upstream fixture. A new packed input then retains only event IDs and fields from planes 0, 1, 2, 4 and 5, removing rows without any reference hit. Neither DUT3 fields, its plane geometry nor the all-detector hit flag enter the reference finder. The published overall alignment remains fixed. The result is:

| Complete reference-cluster tuples | Count |
| --- | ---: |
| Original six-plane associations | 56,792 |
| Reference-only associations | 56,907 |
| Shared | 56,017 |
| Present only in original associations | 775 |
| Present only in reference-only associations | 890 |

Tuples comprise event ID and the five reference cluster IDs. There are no duplicate complete reference tuples. The counts reconcile exactly, including agreement of the original 56,792 count with the earlier fitted-table screen. This demonstrates that evaluated-detector input affects the associations in this fixture. It **does not establish which changed associations are physically correct** or imply an efficiency gain.

Replacing every DUT3 field and the incoming hit flags leaves the packed reference input identical. Adding detector-only rows also leaves it identical. Reconstructing in two pieces separated at an event boundary matches reconstruction of the whole subset in every field. These checks support per-event input separation conditional on the published geometry. That geometry was aligned using the development subset and DUT3, so statistical independence, alignment uncertainty and physical matching accuracy are still open. These outputs are candidate associations, not newly fitted trajectories or a detection-efficiency certificate.

[Machine-readable results](beam-rebuild-results.json), SHA256 `00df72d7c30240aaba17865972716a7e08275fc57b45055403fa52fc6b123686`, retain source identities, versions, original merge arguments and every check. The frozen protocol/executable bytes were verified against Git. No previous experiment or manuscript changed, and no Lean/Lake or GCP run was invoked.

This is established reference construction. [Corryvreckan's primary description](https://arxiv.org/abs/2011.12730), sections 3.3-3.4, explicitly separates reference tracking from DUT association and includes straight-line, multiplet and General Broken Line models. Those methods and BTA's Kalman option remain appropriate comparators. Replacing a detector-influenced association or an all-hit selection is not itself evidence of a new inference advantage.

An additional physical-control lead is the [EUDET performance archive](https://doi.org/10.5281/zenodo.59255): its metadata declares CC-BY-4.0, and its inspected README maps separate runs to beam energy, sensor threshold and 20/150 mm plane spacing. The [primary paper](https://doi.org/10.1140/epjti/s40485-016-0033-2) compares threshold-dependent efficiency with isolated upstream reference triplets. This is a separate experiment, not provenance for Run36. Only metadata and the README were inspected; no file from its 24.8 GB raw-data collection was downloaded.

**Disposition:** retain the replayed reference construction and the reserved event pool. Before consuming it, identify a physical decision for which the inference can add value beyond established tracking and exact-binomial qualification. Simple binary efficiency thresholds do not by themselves supply that advantage. A next ordinary feasibility question is whether a beam-profile decision using multiple observed categories can benefit from bounded spatial-selection inference. It must specify a physical target, demonstrate that the operational inputs are available without the validation reference, and compare with full multinomial nuisance tests before calibration/performance evaluation. Beam coordinates are not Lorentz chronology. Alignment, triggering, event clustering, acceptance and matching error remain calibration obligations.

Reproduce the structural screen with Python, NumPy, h5py and hdf5plugin; the association replay additionally uses Numba and PyYAML. Exact versions are recorded in each result:

```text
python applications/detector-calibration/beam_reference_screen.py --cache-dir PATH_OUTSIDE_REPOSITORY --fetch --output applications/detector-calibration/beam-reference-results.json
python applications/detector-calibration/beam_reference_rebuild.py --cache-dir PATH_OUTSIDE_REPOSITORY --fetch --output applications/detector-calibration/beam-rebuild-results.json
```

## Next selection gate

Choose a task for which the observable record, independently known or calibrated target, detector selection uncertainty and useful decision threshold are jointly available. Prefer an existing physical control or withheld calibration run. Specify the strongest applicable inference and decision cost before measuring performance. If a transfer changes the physical target from spacetime volume, state and justify that bridge explicitly. A constructed coordinate order or simulated thinning of physical measurements cannot substitute for detector calibration.

Remaining to-do list: establish a useful physical decision and ordinary comparative argument before further calibration work; validate alignment, trigger, matching and sampling assumptions on separate evidence; then demonstrate the benefit on reserved measurements. The full user goal remains active.
