These files contain the raw data and the analysis scripts to re-generate Figure 3 of the paper titled *Modelling detector response for accurate calibration of single-photon detectors under pulsed single-photon illumination*.
Two scripts are used to generate parts of the figure, in SVG format.

## Figure 3a
To re-create this part of the figure, run the script `time_definitions.py`. The raw data is in the file 1,3M_hist.txt.

## Figures 3b and 3c
To re-create this part of the figure, run the script `count_fits.py`.

### Raw data
The raw data for efficiency measurement is the files spad*.txt and snspd1.txt. The raw data is NOT corrected for afterpulsing.


### Afterpulsing correction
Afterpulsing correction is added line 76 in `count_fits.py`. The afterpulsing probability is defined, per detector, in the file
`config.json`.