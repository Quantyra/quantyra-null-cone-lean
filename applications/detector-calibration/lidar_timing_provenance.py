"""Inspect retained timing metadata without fitting or using reserved outcomes.

Only the already selected frame prefixes are used for phase-lattice checks.
MAT headers and variable schemas describe the delivered files, not the original
instrument configuration. T3 compatibility is not proof of an acquisition mode.
"""

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.io import loadmat,whosmat

HERE=Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--cache-dir",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    if args.output.exists():raise FileExistsError(args.output)
    original=json.loads((HERE/"lidar-range-protocol.json").read_text())
    control=json.loads((HERE/"lidar-control-results.json").read_text())
    names=[original[k] for k in ["low_flux","high_flux","pulse"]]+[
        {"path":"2019_01_28/FGS_td180_2019_01_28_acq13.mat","sha256":control["input"]["file_sha256"]}]
    report={"executable_sha256":sha(Path(__file__)),"development_frame_range":[0,1000000],"files":[],
            "interpretation":"File schema, header and numerical lattice provenance only. Saved MATLAB creation dates need not be acquisition dates. A sync-counter plus quantized-relative-delay representation is consistent with the data but does not establish T3 mode, the original clock, actual synchronization times or settings. No new fit, comparative benefit or physical calibration is established.",
            "physical_reference_validated":False}
    for item in names:
        path=args.cache_dir/item["path"]
        assert sha(path)==item["sha256"]
        row={"path":item["path"],"sha256":item["sha256"],
             "mat_header_text":path.read_bytes()[:116].decode("ascii",errors="replace").rstrip("\x00 "),
             "variables":[{"name":n,"shape":list(s),"class":c} for n,s,c in whosmat(path)]}
        if any(v["name"]=="frameNum" for v in row["variables"]):
            data=loadmat(path,variable_names=["frameNum","detTime","tr","binRes","T_holdoff","OD"])
            frames=data["frameNum"].ravel();selected=(frames>=0)&(frames<1000000)
            frames=frames[selected].astype(np.int64);phase=data["detTime"].ravel()[selected]
            width=float(data["binRes"].item())*1e9;period=float(data["tr"].item())*1e9
            phase_bins=phase/width
            reconstructed_gaps=np.diff(frames)*period+np.diff(phase)
            gap_bins=reconstructed_gaps/width
            phase_error=float(np.max(np.abs(phase_bins-np.rint(phase_bins))))
            gap_error=float(np.max(np.abs(gap_bins-np.rint(gap_bins))))
            row["timing"]={"development_events":len(frames),"bin_width_ns":width,"period_ns":period,
                           "period_in_raw_bins":period/width,"phase_lattice_max_fractional_bin_error":phase_error,
                           "reconstructed_gap_lattice_max_fractional_bin_error":gap_error,
                           "phase_on_raw_bin_lattice_at_1e_6_bin_tolerance":phase_error<=1e-6,
                           "reconstructed_gap_on_same_lattice_at_1e_6_bin_tolerance":gap_error<=1e-6,
                           "outside_nominal_period_count":int(np.count_nonzero((phase<0)|(phase>=period))),
                           "relative_phase_min_max_ns":[float(phase.min()),float(phase.max())],
                           "holdoff_ns":float(data["T_holdoff"].item()),"optical_density":float(data["OD"].item())}
            assert np.all(np.isfinite(phase)) and np.all(reconstructed_gaps>0)
        report["files"].append(row)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"sha256":sha(args.output),"files":[{"path":r["path"],"header":r["mat_header_text"],"timing":r.get("timing")} for r in report["files"]]}))


if __name__=="__main__":main()
