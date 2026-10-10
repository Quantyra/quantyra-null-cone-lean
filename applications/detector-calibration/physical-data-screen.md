# Physical evidence selection after the finite comparison

S049, 2026-10-10. The [finite balanced-volume comparison](../balanced-volume/FINITE-REFERENCE-RESULTS.md) parks promotion of the frozen four-tail candidate and retains a better exact reference. The beam check below also parks the proposed all-cluster transfer. The latest source screen retrieves actual lidar timing records and a separate raw pulse calibration, verifies bounded development counts, and identifies a dead-time convention that is incompatible with those records as an exact cutoff. This supplies a better observation/calibration lead, not a validated detector model or comparative benefit. Physical validation and practical use remain unachieved.

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

### Operational beam-profile feasibility

The [new protocol](beam-profile-protocol.json), [ordinary derivation](beam-profile-bridge.md)
and [executable](beam_profile_model.py) were pushed at
`666b9511f62d0de5da8417f0717782a2e71727e3` before this evaluation. The existing
development subset and reference count were already known; the new raw-DUT3
cardinality comparison was not. This is a retrospective feasibility check,
not a new physical experiment or a held-out comparison.

For fixed spatial quadrants, the generated category law is
`(a,a+d,1-2a-d)`, where `d=1-F_X(x0)-F_Y(y0)`. The model admits relative
category-retention ratio at most `R`, balance error `|d|<=delta`, and an
observed-record contamination fraction at most `epsilon`. The derivation
gives an exact convex lift, a finite rational polygon for the whole continuous
null set, and sharp endpoints for both conditional category comparisons.
The linear-fractional transformation is established optimization, not a new
general statistical method. A conditional exact test would still require
the stipulated sampling and calibration assumptions.

All **96** exact-rational model cases agree with **1,926** independent
continuous linear-program checks, including conditional endpoints, support
values and minimum-contamination sensitivity. The largest numerical
disagreement is `6.67e-16` and feasibility residual is `4.45e-16` (rounded
up). These numerical checks support the ordinary proof; neither is Lean
certification. At zero balance error and contamination the bounds recover
the earlier pure-thinning formulas exactly.

The earlier alternative's observed law is `(5/19,4/19,10/19)`. A null model
at `a=9/32` with the same relative retention weights produces exactly that
law after mixing `20/171` contamination entirely into category C. This is
about **11.696%**. Under the iid model, the entire categorical sample laws
then agree for every sample size: any uniformly 5%-valid test of the enlarged
null must have detection probability at most 5% at that particular
alternative. This applies to full multinomial tests as well as conditional
ones. Transferring the earlier test unchanged would turn its 88.453% model
power into the same false-flag probability at this null witness.

The exact sensitivity calculation, independently checked by continuous LP,
gives:

| Allowed balance error delta | Minimum contamination making this law null |
| --- | ---: |
| 0 | `20/171` = 11.696% |
| 0.01 | `20/217` = 9.217% |
| 0.02 | `260/3971` = 6.547% |
| 0.03 | `140/3819` = 3.666% |
| 0.04 | `20/3667` = 0.545% |
| 0.05 | 0 |

The physical record check counts **67,113 DUT3 clusters** in the inspected
10,000-event subset, using finite x coordinates and positive cluster-hit
counts; these masks agree for every row. A separate streaming recount from
finite y coordinates gives the same total. There are **56,907 complete
reference tuples**, so every partial one-to-one pairing leaves at least
**10,206 clusters**, or `1134/7457 = 15.207%`, unpaired. This is an exact
cardinality bound for this record/cohort definition. Off-cohort genuine
particles can contribute; it is not a detector-noise estimate, a population
contamination confidence bound or evidence that the physical categorical
law equals the constructed witness. The finite bound and the model's 11.7%
overlap threshold must not be conflated into a physical impossibility proof.

**Disposition:** park the direct all-cluster/pure-thinning transfer to the
complete-reference cohort. Reference-based filtering is unavailable to the
proposed detector-only operational procedure. Any replacement must justify
an observable selection rule or a different target cohort, and bound its
selection, category error, balance and sampling uncertainty before a power
comparison. Counting clusters, reconstructing references and deriving a
robust envelope do not supply the goal's comparative benefit. The 102,700
reserved event outcomes remain uninspected.

[Machine-readable results](beam-profile-results.json) have SHA256
`7076625fdf5ba657518f730c5c144d7667817171808d88b5d3fc040774295c2a`.
All three frozen input files match their Git snapshot byte-for-byte. Data
and reference-result hashes match the earlier provenance record. Reproduce
with the versions recorded in the result (including SciPy):

```text
python applications/detector-calibration/beam_profile_model.py --cache-dir PATH_OUTSIDE_REPOSITORY --output applications/detector-calibration/beam-profile-results.json
```

No reserved response/association outcome, earlier manuscript or Lean source
was changed or evaluated by this check. No Lean/Lake or GCP run was invoked.

## High-flux lidar: timestamp history and calibration counts available

This continuation screens a ranging decision rather than a spatial beam-profile
decision. It does not treat photon times as a causal-order observation or
reopen the parked beam transfer.

### Applicable existing methods

- [Po et al. (CVPR 2022)](https://arxiv.org/html/2111.15047v2) already use
  adaptive gating and exposure. Their [released implementation](https://github.com/cmu-ci-lab/adaptive-gating-spad)
  resamples measured fixed-gate histograms. Such replay can support a model
  comparison but does not independently validate the counterfactual acquisition
  history of a new policy. No large file from that release was retrieved.
- [Rapp et al. (Optica 2021)](https://doi.org/10.1364/OPTICA.403190) already
  model detector/electronics dead times and provide histogram correction and
  flux inference. Their separate low-flux acquisition and pulse calibration
  motivate the selected record check. The public data are linked by
  [HighFluxSPL](https://github.com/Goyal-STIR-Group/HighFluxSPL/tree/1494365d05867fa6bff9b989dc4f0bd5817a0b4e).
- [Kitichotkul et al. (ICCV 2025)](https://arxiv.org/html/2507.09386v1)
  already provide efficient joint depth/signal/background likelihood inference.
  Merely replacing a stationary-histogram approximation with likelihood
  inference cannot be claimed as our new contribution. Its observation model
  and resource requirements must be matched in a future comparison.
- [Jorgensen and Johnson (2026), sections II, V-F and VI](https://arxiv.org/html/2605.23210v1)
  provide exposure-aware sufficient statistics, asymptotic information bounds
  and robust one-step inference. Their real-data benchmark uses acq14, with a
  full-acquisition likelihood fit as proxy truth. They explicitly identify
  residual model mismatch and describe optimized gating as ongoing work. These
  methods are required comparators; neither routine likelihood optimization,
  a one-step update nor a fitted full-record proxy establishes our goal.
- [Zhang et al. (2025)](https://arxiv.org/html/2509.20500v1) already accelerate
  Markov transition-matrix construction. A speed comparison must include that
  formulation if stationary-distribution computation is the proposed benefit.

This is a scoped source/implementation screen, not a completed originality
review or a numerical comparison of these methods. The [source manifest](lidar-source-manifest.json)
pins eight inspected files from HighFluxSPL at `1494365d05867fa6bff9b989dc4f0bd5817a0b4e`
and the 2026 implementation at `d63dc5d8e2395ff1104a81946b989c4345d0baab`.
No upstream executable was run. The former ranging script uses nominal
holdoff plus 2 ns; the latter data reader uses nominal holdoff. Their differing
conventions motivate the check, not an allegation that either publication
claims exact physical calibration from its nominal setting.

### Frozen adequacy check

[Protocol](lidar-record-protocol.json) and [executable](lidar_record_screen.py)
were pushed at `eae51464d528892c9c9e451be64cd52a7ab83553` before local
event-outcome analysis. Published results and archive metadata were already
known. This is retrospective analysis, not a blinded physical experiment.

Only three named ZIP members were retrieved using HTTP byte ranges from the
456,605,196-byte public archive. Member sizes and CRC32 agree with its central
directory; SHA256 identities below freeze the retrieved bytes. CRC is an
integrity check, not an independent physical-data authenticity certificate.
All raw data stay outside Git; software MIT licenses are not presumed to
license redistribution of the separate data archive.

| Member, under `2019_01_28/` | Bytes | SHA256 |
| --- | ---: | --- |
| `FGS_td048_2019_01_28_acq1.mat` | 19,558,228 | `74e8aa95c4b04f2face829e771aa77bafb6b712914b0bf147dedfcc047268098` |
| `FGS_td198_2019_01_28_acq14.mat` | 20,133,276 | `cd1b55c68272a830a3c69fdf78b2198036b49607b9e4ab304c2124db5683cc26` |
| `laser_calib_100.mat` | 3,168 | `69391ff9b96dce1d8fba65ab5c962d77c3e81a69eb063a0f23185b0991ceebf8` |

Both event files include laser frame numbers, within-frame detection times,
8 ps timestamp resolution, measured repetition period, optical density and
nominal holdoff. This allows reconstruction of absolute event times, including
empty periods between recorded detections. The files do not supply an explicit
acquisition-end timestamp: the last occupied frame does not determine a
possibly trailing empty acquisition interval.
The detector's initial recovery state at an analysis boundary also needs an
explicit convention or conditioning on a preceding recorded event.

Outcome analysis uses only frame IDs `[0,1,000,000)` in each file. Full lengths
and frame extents were inspected as authorized provenance metadata. The
development counts are **3,260 low-flux detections** and **396,502 high-flux
detections**. Original absolute-time order is increasing, without duplicates;
frame-difference and absolute-time gap calculations agree to `2.90e-8` ns.
A separate searchsorted prefix extraction reproduces both event counts and
all ten cutoff counts using absolute-time differences.

The high-flux nominal holdoff is 198 ns, exceeding the stated 80 ns timing
electronics dead time. Its minimum observed development gap is 198.2336 ns.
The prescribed four-bin rounding allowance is 0.032 ns:

| Proposed exact cutoff | High-flux gaps below cutoff minus allowance |
| --- | ---: |
| 198 ns | 0 |
| 198.5 ns | 141 |
| 199 ns | 2,085 |
| 200 ns | 13,232 |
| 201 ns | 27,477 |

Thus a literal 200 ns hard cutoff is incompatible with this record under
the specified rounding allowance. Zero violations at 198 ns do not establish
instantaneous full recovery, independent arrivals, absence of afterpulsing
or a calibrated dead-time confidence bound. The low-flux minimum gap is
80.3288 ns despite nominal 48 ns holdoff, consistent with a separate
electronics constraint; it must not be processed using a detector-only
live-time model merely because its illumination is attenuated.

The initial phase-range check is retained as a failure, not silently repaired.
Its [bounded follow-up](lidar-record-followup.json) finds exactly one high-flux
development phase beyond the stated period, by 0.00720 ns, less than one raw
timestamp bin. This is compatible with quantization but does not establish
its cause. Future exposure reconstruction must specify wrapping and timestamp
uncertainty without silently discarding that event. The follow-up inspects
only the same development prefix.

The pulse file includes **253 raw nonnegative integer bins totaling 606,768**,
alongside a smoothed curve and trim indices. Raw counts are available for
investigating calibration uncertainty; they are not automatically a complete
calibration likelihood. The file does not supply acquisition duration,
per-event history, the counts outside the trimmed window or repeated
calibrations establishing drift. Timing-offset, trimming/background and
recovery uncertainty must be justified before treating its template as known.

The high-flux file extends to frame 9,999,924 and the low-flux file to
999,992,461. Outcomes at or after frame 1,000,000 have not been analyzed here.
Those remainders are available for a frozen evaluation, subject to verifying
stability and dependence; they are not claimed independent solely because
the intervals are disjoint. The existing beam reserve is untouched.

### Decision and reproduction

**Retain this source for a calibration-aware ranging comparison.** The
specific opening is a reliable range decision at limited acquisition time,
with pulse and recovery uncertainty propagated rather than treated as exact.
The available low-flux acquisition offers a separate measurement reference;
its timing and uncertainty are still unvalidated. Before fitting the remaining
records, derive a useful finite decision rule and a matched comparison against
joint likelihood and robust one-step inference, with the same calibration,
error tolerance and compute/acquisition budget. Improving only a deliberately
wrong dead-time setting or an uncorrected histogram is not sufficient.

No new gating policy is selected: deleting events from a free-running record
does not recover photons that an alternative gate would have observed. No
depth/flux fit, performance advantage, physical coverage certificate or new
formalization was produced by this check.

[Results](lidar-record-results.json), SHA256
`ec15cf7369a47a2185f39e087f4a6aaa7f484c69e59f25a244ec3e107a6cf68d`,
record metadata, schemas, request ranges, versions and all declared checks.
The follow-up SHA256 is
`4fc4ba882311b274ad1abacc9c9413e6396aede1e86dcfebc0b9ba45f5183135`.
Both frozen input files match Git byte-for-byte. Reproduce the main screen:

```text
python applications/detector-calibration/lidar_record_screen.py --cache-dir PATH_OUTSIDE_REPOSITORY --fetch --output applications/detector-calibration/lidar-record-results.json
```

The follow-up counts `detTime < 0` and `detTime >= 1e9*tr` within the same
frame prefix, reports their distinct values, and checks integrality of
`rawPulseShape`. It applies no correction. No Lean/Lake or GCP run occurred.

## Recovery-model development comparison

2026-10-10 continuation. **The specific age-dependence diagnostic passes.**
An age-by-phase intensity fitted on frames `[0,500000)` predicts the later
development half better than the best hard-cutoff model fitted directly to
that later half. The latter is allowed a continuous cutoff in `[198,200]` ns
and eight separate phase rates. This comparison does not merely hold an
incorrect nominal cutoff fixed. It still does not establish a range benefit.

The [ordinary argument](lidar-recovery-argument.md),
[protocol](lidar-recovery-protocol.json) and
[executable](lidar_recovery_screen.py) were pushed at
`4f70f9299bc3bdf5fb1fddecc36609d3a555e666` before this new exposure/hazard fit.
Earlier gap summaries from the entire development prefix motivated the check.
It is retrospective; the second half is a development evaluation, not final
untouched validation. All outcomes from frame 1,000,000 onward remain reserved.

The scored region has laser phases 15--95 ns, divided into eight strata,
and ages 198--600 ns, divided into 15 strata. Every detection resets the
history, including detections outside this region. Analysis conditions on
the first recorded event and keeps the preceding event at the half boundary.
Exposure is censored at a fixed frame boundary inside the known acquisition;
the unknown acquisition endpoint is not imputed from its last detection.
The known out-of-period timestamp is preserved through absolute-time mapping.

| Timestamp scenario | Alternative minus optimized-null log score |
| --- | ---: |
| Original recorded times | 287.0181 |
| Alternating +8/-8 ps perturbation | 257.2136 |
| Alternating -8/+8 ps perturbation | 318.9197 |

All exceed the declared diagnostic threshold `log(100)`. The optimized
off-pulse cutoff for the original evaluation coordinates is 198.313600 ns;
this differs from the earlier minimum gap over **all** phases. Descriptive
evaluation rates per ns are 0.0016575 at age 198.25--198.5 ns, 0.0095252 at
198.75--199 ns, 0.0140377 at 199.5--200 ns, and 0.0155516 at 201--202 ns.
The corresponding training rates show a similar increase. These are observed
conditional intensities per reconstructed exposure, not detection efficiencies.
Gradual recovery is one explanation; afterpulsing, incident variation and
other observation effects have not been separated.

Independent explicit interval intersections check 9,868 exposure cases with
maximum absolute error `1.244e-8` ns. Phase-union checks agree within
`4.657e-10` ns. A separate count-label implementation reproduces all stored
cell counts, and a scalar score sum agrees within `2.329e-10` log units.
Frozen protocol, executable, argument and input hashes match Git and the
result artifact. The hard-cutoff supremum has an ordinary monotonicity proof
and also passes the prescribed grid check.

The [audit](lidar-recovery-audit.json) retains a numerical sensitivity:
computing phase directly from the original within-frame coordinates changes
some labels exactly on phase boundaries. The circular coordinate discrepancy
is below `1.616e-8` ns, but the count matrices' L1 changes are 50--66.
The three resulting log-score advantages are 287.4932, 257.4420 and 318.1548.
The original results are preserved; this numerical sensitivity does not change
the gate. Future range fits should use the original phase coordinates and
frame-difference gaps to avoid absolute-time cancellation at bin boundaries.

**Inference limits:** the frozen argument's conditional likelihood-ratio
theorem requires a fixed protocol or a valid adjustment for selection.
Here earlier full-prefix outcomes helped select the check. In addition, exact
continuous timestamps are a mathematical assumption, whereas these records
are quantized. Consequently neither the nominal `log(100)` threshold nor the
two perturbations gives this retrospective physical check an exact 1% error
certificate. The perturbations do not bound all possible latent timestamps.
No causal recovery mechanism, absolute calibration or ranging accuracy has
been validated by these log scores.

The [result](lidar-recovery-results.json) SHA256 is
`9ee887258d5cd6956079d6084703d0e318396eefd49735a39dc44cd68439271a`;
the audit SHA256 is
`3369793e58f7c39eed4602ab5ea758b43d240ff4b218505af4218b1d202bc0d7`.
These two JSON outputs retain their original bytes through explicit Git
attributes, so the recorded hashes also identify the committed payloads.
Reproduce with the two executables and `--cache-dir` pointing to the existing
external data directory; each requires a new `--output` path so frozen
results cannot be silently overwritten. No Lean/Lake or GCP run occurred.

## Next selection gate

The age-dependence result warrants a bounded ranging comparison. First quantify
the effect on the range score after allowing amplitude and background to
adjust: a large predictive discrepancy can have negligible effect on range.
Then compare recovery-aware inference against fitted hard-cutoff joint
likelihood, robust one-step estimation, an established flexible recovery
likelihood and a guarded likelihood that retains the full detection history.
Freeze the range tolerance, error requirement, calibration inputs and resource
budget before the comparison. If the range effect is negligible or already
matched by the applicable established method, park promotion of a distinct
method. Do not spend the final reserve to rescue an unsuccessful comparison.

Pulse and reference calibration, latent timestamp treatment, complete history,
stability and dependence remain explicit obligations. A different target from
spacetime volume needs its own measurement bridge; this lidar investigation
does not validate causal-order spacetime reconstruction.

Remaining to-do list: establish a useful calibration-aware range decision and matched comparative argument, validate timing/recovery/pulse and reference assumptions, then demonstrate the benefit using reserved measurements. The full user goal remains active; validated practical use remains unachieved.
