"""Retrieve selected public HighFluxSPL records and audit bounded record adequacy.

No upstream code is executed. All event-outcome summaries use the protocol's
development range. Reading full frame extents and lengths is explicitly allowed.
"""

import argparse
import hashlib
from importlib.metadata import version
import io
import json
from pathlib import Path
import platform
import urllib.request
import zipfile
import zlib

import numpy as np
from scipy.io import loadmat, whosmat

HERE = Path(__file__).resolve().parent


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


class RemoteZip(io.RawIOBase):
    def __init__(self, url, size):
        self.url, self.size, self.position, self.ranges = url, size, 0, []

    def readable(self):
        return True

    def seekable(self):
        return True

    def tell(self):
        return self.position

    def seek(self, offset, whence=0):
        self.position = offset if whence == 0 else self.position + offset if whence == 1 else self.size + offset
        if not 0 <= self.position <= self.size:
            raise ValueError("Seek outside public archive")
        return self.position

    def read(self, length=-1):
        length = min(length if length >= 0 else self.size - self.position, self.size - self.position)
        if length <= 0:
            return b""
        start, end = self.position, self.position + length - 1
        request = urllib.request.Request(self.url, headers={
            "Range": f"bytes={start}-{end}", "User-Agent": "Quantyra-research-source-review"})
        with urllib.request.urlopen(request, timeout=30) as response:
            if response.status != 206 or response.headers.get("Content-Range") != f"bytes {start}-{end}/{self.size}":
                raise RuntimeError("Archive server did not return the requested range")
            payload = response.read(length + 1)
        if len(payload) != length:
            raise RuntimeError("Archive range length mismatch")
        self.position += length
        self.ranges.append([start, end])
        return payload


def fetch_members(protocol, cache):
    source = protocol["archive"]
    remote = RemoteZip(source["url"], source["bytes"])
    with zipfile.ZipFile(remote) as archive:
        for item in source["members"]:
            info = archive.getinfo(item["name"])
            assert info.file_size == item["bytes"]
            assert f"{info.CRC:08x}" == item["crc32"]
            destination = (cache / item["name"]).resolve()
            assert destination.is_relative_to(cache.resolve())
            if not destination.exists():
                payload = archive.read(info)
                assert len(payload) == item["bytes"]
                assert f"{zlib.crc32(payload):08x}" == item["crc32"]
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(payload)
    return remote.ranges


def scalar_metadata(data):
    return {key: np.asarray(value).reshape(-1)[0].item() for key, value in data.items()
            if not key.startswith("__") and np.asarray(value).size == 1
            and np.asarray(value).dtype.kind in "biuf"}


def inspect_events(data, protocol):
    frames, phase = (np.asarray(data[key]).reshape(-1) for key in ["frameNum", "detTime"])
    assert frames.size == phase.size
    lo, hi = protocol["development_frame_range"]
    selected = (frames >= lo) & (frames < hi)
    dev_frames, dev_phase = frames[selected], phase[selected]
    period_ns = float(np.asarray(data["tr"]).item()) * 1e9
    raw_bin_ns = float(np.asarray(data["binRes"]).item()) * 1e9
    holdoff_ns = float(np.asarray(data["T_holdoff"]).item())
    assert np.all(np.isfinite(dev_frames)) and np.all(np.isfinite(dev_phase))
    assert np.all(dev_frames == np.floor(dev_frames)) and np.all(dev_frames >= 0)
    phase_valid = bool(np.all((dev_phase >= 0) & (dev_phase < period_ns)))
    gaps = np.diff(dev_frames.astype(np.int64)).astype(float) * period_ns + np.diff(dev_phase)
    absolute = dev_frames.astype(float) * period_ns + dev_phase
    gap_disagreement = float(np.max(np.abs(np.diff(absolute) - gaps)))
    assert gap_disagreement <= 1e-5
    allowance = protocol["rounding_allowance_raw_bins"] * raw_bin_ns
    frame_counts = np.unique(dev_frames, return_counts=True)[1]
    quantiles = np.quantile(gaps, protocol["gap_quantiles"])
    return {
        "full_array_length": int(frames.size),
        "full_frame_extent": [float(np.min(frames)), float(np.max(frames))],
        "development_range": [lo, hi], "development_detections": int(dev_frames.size),
        "development_frames_with_detections": int(frame_counts.size),
        "development_frames_with_multiple_detections": int(np.count_nonzero(frame_counts > 1)),
        "phase_within_period": phase_valid, "nondecreasing_absolute_times": bool(np.all(gaps >= 0)),
        "duplicate_absolute_times": int(np.count_nonzero(gaps == 0)),
        "independent_gap_max_disagreement_ns": gap_disagreement,
        "period_ns": period_ns, "raw_bin_ns": raw_bin_ns, "holdoff_ns": holdoff_ns,
        "holdoff_exceeds_80ns_electronics": holdoff_ns > 80,
        "gap_quantiles_ns": {str(q): float(v) for q, v in zip(protocol["gap_quantiles"], quantiles)},
        "rounding_allowance_ns": allowance,
        "cutoff_diagnostics": [{"offset_ns": offset, "cutoff_ns": holdoff_ns + offset,
                                "gaps_below_cutoff_minus_allowance": int(np.count_nonzero(gaps < holdoff_ns + offset - allowance))}
                               for offset in protocol["dead_time_offsets_ns"]],
        "boundary": "Descriptive development-record compatibility only; no fitted or certified dead time."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache-dir", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--fetch", action="store_true")
    args = parser.parse_args()
    protocol_path = HERE / "lidar-record-protocol.json"
    protocol = json.loads(protocol_path.read_text())
    ranges = fetch_members(protocol, args.cache_dir) if args.fetch else []
    results = {"scope": protocol["scope"], "protocol_sha256": digest(protocol_path),
               "script_sha256": digest(Path(__file__)), "requested_ranges": ranges,
               "versions": {"python": platform.python_version(), "numpy": version("numpy"), "scipy": version("scipy")},
               "members": []}
    for item in protocol["archive"]["members"]:
        path = args.cache_dir / item["name"]
        payload = path.read_bytes()
        assert len(payload) == item["bytes"] and f"{zlib.crc32(payload):08x}" == item["crc32"]
        schema = [{"name": name, "shape": list(shape), "class": cls} for name, shape, cls in whosmat(path)]
        data = loadmat(path)
        entry = {**item, "sha256": hashlib.sha256(payload).hexdigest(), "schema": schema,
                 "scalar_metadata": scalar_metadata(data)}
        if "frameNum" in data and "detTime" in data:
            entry["event_record"] = inspect_events(data, protocol)
        else:
            entry["calibration_arrays"] = {key: {"finite": bool(np.all(np.isfinite(value))),
                                                   "minimum": float(np.min(value)), "maximum": float(np.max(value)),
                                                   "sum": float(np.sum(value))}
                                             for key, value in data.items() if not key.startswith("__")
                                             and np.asarray(value).size > 1 and np.asarray(value).dtype.kind in "biuf"}
        results["members"].append(entry)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
