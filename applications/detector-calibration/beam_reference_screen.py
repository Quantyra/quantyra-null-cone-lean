"""S049: inspect a pinned BTA fixture without estimating physical efficiency.

Requires numpy, h5py and hdf5plugin. Public inputs stay outside this repository.
The two event halves are descriptive: neither is a blinded validation set.
"""

import argparse
from collections import Counter
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import platform
import urllib.request

import h5py
import hdf5plugin  # Registers the Blosc filter used by the upstream fixture.
import numpy as np


HERE = Path(__file__).resolve().parent


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def summarize(rows, dut):
    events, multiplicities = np.unique(rows["event_number"], return_counts=True)
    dut_bit = 1 << dut
    reference_mask = 63 ^ dut_bit
    return {
        "rows": len(rows),
        "events": len(events),
        "first_event": int(events[0]) if len(events) else None,
        "last_event": int(events[-1]) if len(events) else None,
        "events_with_multiple_rows": int(np.count_nonzero(multiplicities > 1)),
        "event_ids_nondecreasing": bool(np.all(np.diff(rows["event_number"]) >= 0)),
        "missing_dut_hit_rows": int(np.count_nonzero((rows["hit_flag"] & dut_bit) == 0)),
        "missing_reference_hit_rows": int(np.count_nonzero(
            (rows["hit_flag"] & reference_mask) != reference_mask)),
        "nonfinite_fit_rows": int(np.count_nonzero(~np.isfinite(
            np.column_stack([rows[n] for n in ["offset_x", "offset_y", "offset_z",
                                              "slope_x", "slope_y", "slope_z",
                                              "track_chi2"]])).all(axis=1))),
        "hit_patterns": {str(k): v for k, v in sorted(Counter(
            int(x) for x in rows["hit_flag"]).items())},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache-dir", type=Path, required=True)
    parser.add_argument("--fetch", action="store_true", help="Download missing pinned public inputs")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    protocol_path = HERE / "beam-reference-protocol.json"
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    args.cache_dir.mkdir(parents=True, exist_ok=True)
    inputs = {}
    for name, spec in protocol["files"].items():
        path = args.cache_dir / name
        host = ("https://media.githubusercontent.com/media/" if spec.get("lfs")
                else "https://raw.githubusercontent.com/")
        url = (host + "SiLab-Bonn/beam_telescope_analysis/"
               + protocol["source_commit"] + "/" + spec["path"])
        if not path.exists() and args.fetch:
            with urllib.request.urlopen(url, timeout=60) as response:
                data = response.read()
            if hashlib.sha256(data).hexdigest() != spec["sha256"]:
                raise ValueError(f"Downloaded hash mismatch: {name}")
            path.write_bytes(data)
        digest = sha256(path)
        if digest != spec["sha256"]:
            raise ValueError(f"Input hash mismatch: {name}")
        inputs[name] = {"sha256": digest, "bytes": path.stat().st_size, "url": url}

    result = {
        "scope": protocol["scope"],
        "protocol_sha256": sha256(protocol_path),
        "executable_sha256": sha256(Path(__file__)),
        "versions": {"python": platform.python_version(), **{
            name: version(name) for name in ["numpy", "h5py", "hdf5plugin"]}},
        "inputs": inputs,
        "tables": {},
        "claim_boundary": "Structural counts only. No independent-efficiency calibration, comparative benefit, physical validation or spacetime inference is established.",
    }
    with h5py.File(args.cache_dir / "Tracks_result.h5", "r") as data:
        result["stored_fit_arguments"] = {
            row["name"].decode(): row["value"].decode()
            for row in data["arguments/fit_tracks"][()]}
        for dut in range(6):
            rows = data[f"Tracks_DUT{dut}"][()]
            summary = summarize(rows, dut)
            consistency = {}
            for plane in range(6):
                present = (rows["hit_flag"] & (1 << plane)) != 0
                finite_x = np.isfinite(rows[f"x_dut_{plane}"])
                finite_y = np.isfinite(rows[f"y_dut_{plane}"])
                hits = rows[f"n_hits_dut_{plane}"] > 0
                consistency[str(plane)] = {
                    "bit_x_disagreements": int(np.count_nonzero(present != finite_x)),
                    "bit_y_disagreements": int(np.count_nonzero(present != finite_y)),
                    "bit_n_hits_disagreements": int(np.count_nonzero(present != hits)),
                }
            summary["independent_field_consistency"] = consistency
            result["tables"][str(dut)] = summary
            if dut == 3:
                events = np.unique(rows["event_number"])
                split = int(events[len(events) // 2]) if len(events) else None
                reference_mask = 63 ^ (1 << dut)
                selected = ((rows["hit_flag"] & reference_mask) == reference_mask)
                selected &= (rows["quality_flag"] & reference_mask) == reference_mask
                selected &= rows["track_chi2"] < 15
                halves = ({"earlier": rows["event_number"] < split,
                           "later": rows["event_number"] >= split} if split is not None
                          else {"earlier": np.zeros(len(rows), dtype=bool),
                                "later": np.zeros(len(rows), dtype=bool)})
                result["dut3_descriptive_subsets"] = {
                    "split_event": split,
                    "reference_quality_subset": summarize(rows[selected], dut),
                    "chronological_halves": {
                        label: {"all_rows": summarize(rows[mask], dut),
                                "reference_quality_subset": summarize(rows[mask & selected], dut)}
                        for label, mask in halves.items()},
                }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"output": str(args.output), "dut3": result["tables"]["3"],
                      "subsets": result["dut3_descriptive_subsets"]}, indent=2))


if __name__ == "__main__":
    main()
