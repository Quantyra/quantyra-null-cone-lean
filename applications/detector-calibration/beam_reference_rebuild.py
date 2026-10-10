"""S049 reference-association adequacy check using pinned upstream BTA routines.

The finder is the existing SiLab-Bonn implementation, not a Quantyra algorithm.
Geometry and track-finder functions are loaded from verified public source bytes.
The wrapper follows BTA find_tracks; see beam-source-NOTICE.txt for attribution.
No outcomes outside the already inspected small fixture are summarized here.
"""

import argparse
import ast
from collections import Counter
import hashlib
from importlib.metadata import version
import json
import logging
import math
from pathlib import Path
import platform
import urllib.request

import h5py
import hdf5plugin
from numba import njit
import numpy as np
import yaml


HERE = Path(__file__).resolve().parent
REFERENCE_PLANES = (0, 1, 2, 4, 5)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def inputs(cache, protocol, fetch):
    cache.mkdir(parents=True, exist_ok=True)
    receipt = {}
    for name, spec in protocol["files"].items():
        path = cache / name
        prefix = ("https://media.githubusercontent.com/media/" if spec.get("lfs")
                  else "https://raw.githubusercontent.com/")
        url = prefix + "SiLab-Bonn/beam_telescope_analysis/" + protocol["source_commit"] + "/" + spec["path"]
        if not path.exists() and fetch:
            with urllib.request.urlopen(url, timeout=60) as response:
                content = response.read()
            if hashlib.sha256(content).hexdigest() != spec["sha256"]:
                raise ValueError(f"Download hash mismatch: {name}")
            path.write_bytes(content)
        if digest(path) != spec["sha256"]:
            raise ValueError(f"Input hash mismatch: {name}")
        receipt[name] = {"sha256": spec["sha256"], "bytes": path.stat().st_size, "url": url}
    return receipt


def load_functions(path, names, namespace):
    """Execute only named function definitions from the hash-verified source."""
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    nodes = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in names]
    if {n.name for n in nodes} != set(names):
        raise ValueError("Requested upstream functions are missing")
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(path), "exec"), namespace)


def upstream(cache):
    namespace = {"np": np, "math": math, "logging": logging, "njit": njit}
    load_functions(cache / "geometry_utils.py", [
        "rotation_matrix_x", "rotation_matrix_y", "rotation_matrix_z", "rotation_matrix",
        "translation_matrix", "local_to_global_transformation_matrix", "apply_transformation_matrix",
        "get_line_intersections_with_dut", "get_line_intersections_with_plane"], namespace)
    load_functions(cache / "track_analysis.py", [
        "_find_tracks_loop", "_find_tracks", "_get_first_dut_index", "_get_last_dut_index"], namespace)
    return namespace


def project_references(rows):
    # Copy into a new packed dtype: a multi-field view would retain excluded bytes.
    names = ["event_number"] + [name for name in rows.dtype.names
                                if any(name.endswith(f"_dut_{p}") for p in REFERENCE_PLANES)]
    projected = np.empty(len(rows), dtype=[(name, rows.dtype[name]) for name in names])
    for name in names:
        projected[name] = rows[name]
    keep = np.logical_or.reduce([np.isfinite(projected[f"x_dut_{p}"]) for p in REFERENCE_PLANES])
    return projected[keep]


def associate(rows, plane_ids, telescope, api):
    """Use BTA's existing geometry and finder with the supplied detector list."""
    config = telescope["DUT"]
    indices = np.column_stack([np.arange(len(rows), dtype=np.int64) for _ in plane_ids])
    positions, translations, normals, intersections = [], [], [], []
    for plane in plane_ids:
        c = config[plane]
        pose = {k: c[k] for k in ["translation_x", "translation_y", "translation_z",
                                   "rotation_alpha", "rotation_beta", "rotation_gamma"]}
        intersections.append(api["get_line_intersections_with_dut"](
            line_origins=np.array([[0., 0., 0.]]), line_directions=np.array([[0., 0., 1.]]), **pose)[0, 2])

        def transform(xyz, source):
            matrix = api["local_to_global_transformation_matrix"](
                **{d: source[f"translation_{d}"] for d in "xyz"},
                **{a: source[f"rotation_{a}"] for a in ["alpha", "beta", "gamma"]})
            return api["apply_transformation_matrix"](*xyz, matrix)

        xyz = transform(tuple(rows[f"{d}_dut_{plane}"] for d in "xyz"), c)
        xyz = transform(xyz, telescope)  # Upstream align_to_beam=True.
        positions.append(xyz)
        translations.append([c[f"translation_{d}"] for d in "xyz"])
        rotation = api["rotation_matrix"](**{a: c[f"rotation_{a}"] for a in ["alpha", "beta", "gamma"]})
        normal = rotation.T.dot(np.eye(3, dtype=np.float64))[2]
        normal /= np.sqrt(np.dot(normal, normal))
        normals.append(-normal if normal[2] < 0 else normal)
    api["_find_tracks_loop"](
        event_numbers=rows["event_number"], indices=indices,
        z_sorted_dut_indices=np.argsort(intersections),
        x=np.column_stack([p[0] for p in positions]),
        y=np.column_stack([p[1] for p in positions]),
        z=np.column_stack([p[2] for p in positions]),
        select_extrapolation_duts=np.arange(len(plane_ids), dtype=np.int64),
        translation=np.vstack(translations), normal=np.vstack(normals))
    output = rows.copy()
    for column, plane in enumerate(plane_ids):
        for name in rows.dtype.names:
            if name.endswith(f"_dut_{plane}"):
                output[name] = rows[name][indices[:, column]]
    if "hit_flag" in output.dtype.names:
        output["hit_flag"] = 0
        for plane in plane_ids:
            output["hit_flag"] += np.isfinite(output[f"x_dut_{plane}"]).astype(np.uint32) << plane
    return output


def disagreements(a, b):
    if a.dtype != b.dtype or a.shape != b.shape:
        return {"schema_or_shape": True}
    result = {}
    for name in a.dtype.names:
        equal = a[name] == b[name]
        if a.dtype[name].kind == "f":
            equal |= np.isnan(a[name]) & np.isnan(b[name])
        if not np.all(equal):
            result[name] = int(np.count_nonzero(~equal))
    return result


def tuples(rows):
    complete = np.logical_and.reduce([np.isfinite(rows[f"x_dut_{p}"]) for p in REFERENCE_PLANES])
    fields = ["event_number"] + [f"cluster_ID_dut_{p}" for p in REFERENCE_PLANES]
    return Counter(tuple(int(row[name]) for name in fields) for row in rows[complete])


def provenance(cache, small):
    subset_events = np.unique(small["event_number"])
    with h5py.File(cache / "Merged_result.h5", "r") as full:
        table = full["MergedClusters"]
        event_ids = table.fields("event_number")[()]
        all_events = np.unique(event_ids)
        selected = []
        for start in range(0, len(table), 100000):
            mask = np.isin(event_ids[start:start + 100000], subset_events)
            if np.any(mask):
                selected.append(table[start:start + 100000][mask])
        selected = np.concatenate(selected)
        return {
            "small_rows": len(small), "small_events": len(subset_events),
            "full_rows": len(table), "full_events": len(all_events),
            "small_events_absent_from_full": int(np.count_nonzero(~np.isin(subset_events, all_events))),
            "other_event_ids": int(np.count_nonzero(~np.isin(all_events, subset_events))),
            "selected_rows": len(selected), "same_dtype": small.dtype == selected.dtype,
            "exact_subset_bytes": small.tobytes() == selected.tobytes(),
            "stored_merge_arguments": {row["name"].decode(): row["value"].decode()
                                       for row in full["arguments/merge_cluster_data"][()]},
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache-dir", type=Path, required=True)
    parser.add_argument("--fetch", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    protocol_path = HERE / "beam-rebuild-protocol.json"
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    result = {"scope": protocol["scope"], "inputs": inputs(args.cache_dir, protocol, args.fetch),
              "protocol_sha256": digest(protocol_path), "executable_sha256": digest(Path(__file__)),
              "versions": {"python": platform.python_version(), **{name: version(name) for name in
                           ["numpy", "h5py", "hdf5plugin", "numba", "llvmlite", "PyYAML"]}}}
    with h5py.File(args.cache_dir / "Merged_small.h5", "r") as f:
        small = f["MergedClusters"][()]
    result["provenance"] = provenance(args.cache_dir, small)
    api = upstream(args.cache_dir)
    telescope = yaml.safe_load((args.cache_dir / "telescope_aligned.yaml").read_text())["TELESCOPE"]
    baseline = associate(small, tuple(range(6)), telescope, api)
    with h5py.File(args.cache_dir / "TrackCandidates_result.h5", "r") as f:
        expected = f["TrackCandidates"][()]
    result["six_plane_replay"] = {"rows": len(baseline), "fields": len(baseline.dtype.names),
                                  "disagreements": disagreements(baseline, expected)}
    if result["six_plane_replay"]["disagreements"]:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
        raise RuntimeError("Upstream replay failed; projected associations not interpreted")
    projected = project_references(small)
    # Only reference-plane geometry is passed to the projected finder.
    reference_geometry = {**telescope, "DUT": {p: telescope["DUT"][p] for p in REFERENCE_PLANES}}
    reference = associate(projected, REFERENCE_PLANES, reference_geometry, api)
    original_tuples, reference_tuples = tuples(baseline), tuples(reference)
    changed = small.copy()
    for name in changed.dtype.names:
        if name.endswith("_dut_3"):
            changed[name] = 1
    changed["hit_flag"] = 8
    extra = np.zeros(10, dtype=small.dtype)
    extra["event_number"] = small["event_number"][-1]
    for plane in REFERENCE_PLANES:
        for dimension in "xyz":
            extra[f"{dimension}_dut_{plane}"] = np.nan
    extra["x_dut_3"] = 1
    extra["n_hits_dut_3"] = 1
    event_ids = np.unique(projected["event_number"])
    split_event = event_ids[len(event_ids) // 2]
    cut = int(np.searchsorted(projected["event_number"], split_event))
    split_reference = np.concatenate([
        associate(projected[:cut], REFERENCE_PLANES, reference_geometry, api),
        associate(projected[cut:], REFERENCE_PLANES, reference_geometry, api)])
    result["reference_rebuild"] = {
        "projected_rows": len(projected), "projected_fields": len(projected.dtype.names),
        "reference_events": len(event_ids), "original_complete_tuples": sum(original_tuples.values()),
        "reference_complete_tuples": sum(reference_tuples.values()),
        "shared_tuples": sum((original_tuples & reference_tuples).values()),
        "original_only_tuples": sum((original_tuples - reference_tuples).values()),
        "reference_only_tuples": sum((reference_tuples - original_tuples).values()),
        "duplicate_complete_tuples": sum(v - 1 for v in reference_tuples.values()),
        "replacement_projection_identical": project_references(changed).tobytes() == projected.tobytes(),
        "DUT_only_padding_projection_identical": project_references(np.concatenate([small, extra])).tobytes() == projected.tobytes(),
        "event_boundary_split_disagreements": disagreements(reference, split_reference),
        "reference_record_sha256": hashlib.sha256(reference.tobytes()).hexdigest(),
    }
    result["claim_boundary"] = "A replayed established association method with DUT3 excluded from per-event inputs given fixed published alignment. No new tracking advantage, calibration certificate, physical efficiency estimate or completed goal is claimed."
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({k: v for k, v in result.items() if k in ["provenance", "six_plane_replay", "reference_rebuild"]}, indent=2))


if __name__ == "__main__":
    main()
