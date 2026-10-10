"""S044 frozen comparison. Uses no Lean and never overwrites an attempt."""
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import gzip
import itertools
import json
import math
from pathlib import Path
import platform
import subprocess
import sys
import time
import traceback
import tracemalloc

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "tools"))
from marked_volume import Interval, marked_count, retention_interval, verify_interval

sys.set_int_max_str_digits(20000)
SCALE = 10**10
METHODS = ("quantyra", "aronow_lee_cp", "known_range", "ignore_bias_diagnostic")


def sha(b):
    return hashlib.sha256(b).hexdigest()


def save(out, name, value):
    data = (json.dumps(value, indent=2) + "\n").encode("utf-8")
    (out / name).write_bytes(gzip.compress(data, mtime=0) if name.endswith(".gz") else data)


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def clip(lo, hi):
    return max(F(1, 8), lo), min(F(3, 8), hi)


def width(c):
    return max(F(0), c[1] - c[0])


def reports(k, n, r, bank):
    c = bank[n][k]
    own = retention_interval(c, r)
    # Binary inverse-weight extrema, expressed separately from retention_interval.
    ref = (c.lower / (c.lower + r * (1 - c.lower)),
           r * c.upper / (r * c.upper + 1 - c.upper))
    return {"quantyra": clip(own.lower, own.upper),
            "aronow_lee_cp": clip(*ref), "known_range": (F(1, 8), F(3, 8)),
            "ignore_bias_diagnostic": clip(c.lower, c.upper)}


def decision(c, nominal, tolerance):
    lo, hi = c
    if lo > hi:
        return "alarm"
    if nominal - tolerance <= lo and hi <= nominal + tolerance:
        return "accept"
    if hi < nominal - tolerance or lo > nominal + tolerance:
        return "reject"
    return "unresolved"


def check_order(order):
    if not isinstance(order, np.ndarray) or order.dtype != np.bool_:
        raise ValueError("Boolean relation required")
    if order.ndim != 2 or order.shape[0] != order.shape[1] or len(order) < 2:
        raise ValueError("Square two-anchor relation required")
    if np.any(np.diag(order)) or np.any(order & order.T):
        raise ValueError("Strict asymmetric relation required")
    if not order[0, 1]:
        raise ValueError("Fixed anchor chronology required")


def observed_reports(order, r, bank):
    check_order(order)
    n = len(order) - 2
    t = time.perf_counter()
    k, nn = marked_count([(bool(order[0, i]), bool(order[i, 1]))
                         for i in range(2, n + 2)])
    c = bank[n][k]
    own = retention_interval(c, r)
    a = clip(own.lower, own.upper)
    own_seconds = time.perf_counter() - t
    t = time.perf_counter()
    other_k = int(np.count_nonzero(order[0, 2:] & order[2:, 1]))
    c = bank[n][other_k]
    b = clip(c.lower / (c.lower + r * (1 - c.lower)),
             r * c.upper / (r * c.upper + 1 - c.upper))
    ref_seconds = time.perf_counter() - t
    assert k == other_k and nn == n and a == b
    return k, a, own_seconds, ref_seconds


def detector(pattern, r):
    weights = []
    for i in range(4):
        row = []
        for j in range(4):
            inside = i < 2 and j < 2
            low = {"uniform": False, "inside_low": inside,
                   "inside_high": not inside, "checker4": (i + j) % 2 == 0,
                   "stripes4": i % 2 == 0}[pattern]
            row.append(1 / r if low else F(1))
        weights.append(row)
    check_detector(weights, r)
    return weights


def check_detector(weights, r):
    if not 1 <= r <= 2 or len(weights) != 4 or any(len(row) != 4 for row in weights):
        raise ValueError("Invalid detector grid or bound")
    if not all(1/r <= w <= 1 for row in weights for w in row):
        raise ValueError("Detector outside declared bounds")


def check_membership(k, uv):
    if k != int(np.count_nonzero(np.all((uv > 0) & (uv < .5), axis=1))):
        raise ValueError("Recorded count disagrees with latent evaluation truth")


def geometry(epsilon, weights):
    # Exact rectangle integration of the accepted bilinear density.
    z = a = total = F(0)
    cells = []
    for i, j in itertools.product(range(4), repeat=2):
        l, u, b, t = F(i, 4), F(i+1, 4), F(j, 4), F(j+1, 4)
        mass = (u-l)*(t-b) + epsilon*(u*u-u-l*l+l)*(t*t-t-b*b+b)
        cells.append(mass)
        total += mass
        z += mass * weights[i][j]
        if i < 2 and j < 2:
            a += mass * weights[i][j]
    assert total == 1 and all(c > 0 for c in cells)
    v = F(1, 4) + epsilon/16
    assert sum(cells[i*4+j] for i in range(2) for j in range(2)) == v
    return v, a/z, z


def sample(n, epsilon, weights, rng):
    chunks = []
    got = proposals = generated = drawn = 0
    w = np.array(weights, dtype=float)
    while got < n:
        batch = max(64, 4 * (n - got))
        x = rng.random((batch, 4))
        drawn += batch
        uv = x[:, :2]
        rho = 1 + float(epsilon)*(2*uv[:, 0]-1)*(2*uv[:, 1]-1)
        gen = x[:, 2] < rho/1.5
        ix = np.floor(uv*4).astype(int)
        keep = gen & (x[:, 3] < w[ix[:, 0], ix[:, 1]])
        indices = np.flatnonzero(keep)
        take = min(n-got, len(indices))
        end = int(indices[take-1])+1 if take == n-got else batch
        proposals += end
        generated += int(np.count_nonzero(gen[:end]))
        chunks.append(uv[indices[:take]])
        got += take
        if proposals > 64*n:
            raise RuntimeError("Frozen proposal ceiling exceeded")
    return np.concatenate(chunks), proposals, generated, drawn


def relation(uv):
    points = np.vstack(([[0., 0.], [.5, .5]], uv))
    return ((points[:, None, 0] < points[None, :, 0]) &
            (points[:, None, 1] < points[None, :, 1]))


def atoms(n, theta):
    a, d = theta.numerator, theta.denominator
    assert 0 < a < d
    term = (d-a)**n
    result = [term]
    for k in range(n):
        term, rem = divmod(term*(n-k)*a, (k+1)*(d-a))
        assert rem == 0
        result.append(term)
    assert sum(result) == d**n
    return result, d**n


def enclosure(weighted_lower, weighted_upper, denominator):
    return [str(F(weighted_lower, SCALE*denominator)),
            str(F(weighted_upper, SCALE*denominator))]


def floorceil(x):
    x *= SCALE
    return x.numerator//x.denominator, -((-x.numerator)//x.denominator)


def exact_metrics(n, r, v, theta, bank, p):
    probabilities, denominator = atoms(n, theta)
    out = {}
    for method in METHODS:
        coverage = empty = useful = wl = wh = el = eh = 0
        decisions = {s: {"correct": 0, "wrong": 0, "unresolved": 0} for s in p["nominated_volumes"]}
        for k, weight in enumerate(probabilities):
            c = reports(k, n, r, bank)[method]
            covered = c[0] <= v <= c[1]
            coverage += weight * covered
            is_empty = c[0] > c[1]
            empty += weight * is_empty
            useful += weight * (not is_empty and width(c) <= F(p["useful_width"]))
            mid = F(1, 4) if is_empty else (c[0]+c[1])/2
            a, b = floorceil(width(c)); wl += weight*a; wh += weight*b
            a, b = floorceil(abs(mid-v)); el += weight*a; eh += weight*b
            for nominal, counts in decisions.items():
                action = decision(c, F(nominal), F(p["decision_tolerance"]))
                inside = abs(v-F(nominal)) <= F(p["decision_tolerance"])
                key = ("unresolved" if action == "unresolved" else "correct" if
                       (action == "accept" and inside or action == "reject" and not inside) else "wrong")
                counts[key] += weight
        out[method] = {"coverage": str(F(coverage, denominator)),
                       "empty": str(F(empty, denominator)), "useful": str(F(useful, denominator)),
                       "mean_width": enclosure(wl, wh, denominator),
                       "mean_midpoint_error": enclosure(el, eh, denominator),
                       "decisions": {nom: {k: str(F(x, denominator)) for k, x in c.items()}
                                     for nom, c in decisions.items()}}
        if method != "ignore_bias_diagnostic":
            assert 20*coverage >= 19*denominator
            assert all(20*d["wrong"] <= denominator for d in decisions.values())
    assert out["quantyra"] == out["aronow_lee_cp"]
    return out


def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--output", required=True)
    args = ap.parse_args()
    p = json.loads((HERE/"protocol.json").read_text(encoding="utf-8"))
    assert p["version"] == "s044-application-v1"
    assert not git("status", "--porcelain").strip(), "Freeze requires clean worktree"
    head = git("rev-parse", "HEAD").decode().strip()
    assert git("ls-remote", "origin", "refs/heads/main").decode().split()[0] == head
    out = (ROOT/args.output).resolve()
    assert out.is_relative_to((HERE/"evidence").resolve())
    out.mkdir(parents=True, exist_ok=False)
    started = time.perf_counter(); tracemalloc.start()
    def resources():
        elapsed = time.perf_counter()-started
        peak = tracemalloc.get_traced_memory()[1]
        size = sum(f.stat().st_size for f in out.iterdir() if f.is_file())
        assert elapsed <= p["resource_ceiling"]["elapsed_seconds"], "elapsed ceiling"
        assert peak <= p["resource_ceiling"]["peak_python_traced_bytes"], "memory ceiling"
        assert size <= p["resource_ceiling"]["new_artifact_bytes"], "artifact ceiling"
        return elapsed, peak, size
    try:
        names = git("ls-tree", "-r", "--name-only", "HEAD").decode().splitlines()
        preserved = {name: sha((ROOT/name).read_bytes()) for name in names}
        sources = ["applications/marked-volume/"+n for n in ("protocol.json", "benchmark.py", "README.md")]
        sources += ["tools/marked_volume.py", p["calibration_bank"], "QuantyraNullCone/VolumeRateExperiment.lean",
                    "QuantyraNullCone/VolumeRateJoint.lean", "QuantyraNullCone/VolumeRateEmpty.lean"]
        binding = {}
        for name in sources:
            data = git("show", "HEAD:"+name)
            assert data == (ROOT/name).read_bytes().replace(b"\r\n", b"\n")
            binding[name] = sha(data)
        save(out, "freeze.json", {"commit": head, "utc": datetime.now(timezone.utc).isoformat(),
             "python": platform.python_version(), "numpy": np.__version__, "sources": binding,
             "preserved": preserved, "protocol": p["version"]})
        t = time.perf_counter()
        raw = json.loads((ROOT/p["calibration_bank"]).read_text(encoding="utf-8"))
        bank = {row["n"]: [Interval(F(a), F(b)) for a, b in row["endpoints"]] for row in raw}
        certs = 0
        for n, cs in bank.items():
            assert len(cs) == n+1
            for k, c in enumerate(cs):
                assert verify_interval(k, n, c)
                certs += 1
            resources()
        calibration_seconds = time.perf_counter()-t
        controls = []
        two = np.array([[False, True], [False, False]], dtype=bool)
        for bad in (two.astype(int), np.array([[True, True], [False, False]]), two.T):
            try: check_order(bad)
            except ValueError: controls.append(True)
            else: raise AssertionError("Invalid relation accepted")
        bad_weights = detector("uniform", F(2)); bad_weights[0][0] = F(1, 3)
        try: check_detector(bad_weights, F(2))
        except ValueError: controls.append(True)
        else: raise AssertionError("Invalid detector accepted")
        try: check_membership(0, np.array([[.25, .25]]))
        except ValueError: controls.append(True)
        else: raise AssertionError("Tampered membership accepted")
        assert all(controls) and len(controls) == 5
        for r in map(F, ("1", "9/8", "5/4", "2")):
            assert observed_reports(two, r, bank)[1] == (F(1, 8), F(3, 8))
        save(out, "controls.json", {"negative_controls_rejected": len(controls), "zero_sample_cases": 4,
                                     "binomial_certificates": certs, "calibration_seconds": calibration_seconds})
        strata = []; trials = []; witnesses = []; exact_seconds = sampling_seconds = order_seconds = 0.
        own_seconds = ref_seconds = 0.; diagnostic_pass = True
        for phase_index, phase in enumerate(("known", "withheld")):
            cfg = p[phase]
            for ei, ri, pi, ni in itertools.product(range(len(cfg["epsilons"])), range(len(cfg["ratios"])),
                                                  range(len(cfg["patterns"])), range(len(p["sizes"]))):
                e, r, pattern, n = F(cfg["epsilons"][ei]), F(cfg["ratios"][ri]), cfg["patterns"][pi], p["sizes"][ni]
                sid = len(strata); weights = detector(pattern, r); v, theta, retained = geometry(e, weights)
                t = time.perf_counter(); metrics = exact_metrics(n, r, v, theta, bank, p)
                exact_seconds += time.perf_counter()-t
                total_count = 0
                for rep in range(p["replications_per_stratum"]):
                    seed = [p["seed"], phase_index, ei, ri, pi, ni, rep]
                    rng = np.random.Generator(np.random.PCG64(np.random.SeedSequence(seed)))
                    t = time.perf_counter(); uv, proposals, generated, drawn = sample(n, e, weights, rng)
                    sampling_seconds += time.perf_counter()-t
                    t = time.perf_counter(); order = relation(uv)
                    order_seconds += time.perf_counter()-t
                    k, c, ta, tb = observed_reports(order, r, bank)
                    own_seconds += ta; ref_seconds += tb; total_count += k
                    check_membership(k, uv)
                    if rep == 0:
                        points = np.vstack(([[0., 0.], [.5, .5]], uv))
                        tt = (points[:, 0]+points[:, 1])/2; xx = (points[:, 0]-points[:, 1])/2
                        assert np.array_equal(order, tt[None, :]-tt[:, None] > abs(xx[None, :]-xx[:, None]))
                        assert np.array_equal(order, relation(uv[:, ::-1]))
                        perm = np.r_[0, 1, np.arange(n+1, 1, -1)]
                        assert observed_reports(order[np.ix_(perm, perm)], r, bank)[:2] == (k, c)
                        witnesses.append({"stratum": sid, "coordinates": uv.tolist()})
                    trials.append({"stratum": sid, "replicate": rep, "seed": seed, "count": k,
                         "proposals": proposals, "generated": generated, "drawn": drawn,
                         "coordinates_sha256": sha(uv.astype('<f8').tobytes()),
                         "relation_sha256": sha(np.packbits(order).tobytes()),
                         "quantyra_seconds": ta, "reference_seconds": tb})
                radius = F(math.ceil(1e9*math.sqrt(math.log(2*132/.01)/(2*n*64))), 10**9)
                diagnostic = abs(F(total_count, n*64)-theta) <= radius
                diagnostic_pass &= diagnostic
                strata.append({"id": sid, "phase": phase, "epsilon": str(e), "R": str(r), "pattern": pattern,
                     "n": n, "volume": str(v), "theta": str(theta), "retained_mass": str(retained),
                     "metrics": metrics, "total_count": total_count,
                     "sampling_radius": str(radius), "sampling_diagnostic_pass": diagnostic})
                resources()
                if sid % 12 == 0:
                    print(json.dumps({"phase": phase, "strata_done": sid+1, "elapsed": time.perf_counter()-started}), flush=True)
        assert len(strata) == 132 and len(trials) == 8448 and len(witnesses) == 132
        gate = [s for s in strata if s["phase"] == "withheld" and s["n"] == 1024 and F(s["R"]) <= F(5, 4)]
        def correct(m):
            return sum(F(d["correct"]) for d in m["decisions"].values())/2
        absolute = all(F(s["metrics"]["quantyra"]["useful"]) >= F(4, 5) and
                       correct(s["metrics"]["quantyra"]) >= F(4, 5) for s in gate)
        assert all(s["metrics"]["quantyra"] == s["metrics"]["aronow_lee_cp"] for s in strata)
        def improved(s):
            a, b = (s["metrics"][m] for m in ("quantyra", "aronow_lee_cp"))
            aw, bw = a["mean_width"], b["mean_width"]
            narrower = F(aw[1]) <= F(9, 10)*F(bw[0]) and correct(a) >= correct(b)
            # Equal exact reports give equal width despite outward display enclosures.
            no_wider = aw == bw or F(aw[1]) <= F(bw[0])
            decisive = correct(a) >= correct(b)+F(1, 20) and no_wider
            no_worse_error = all(F(a["decisions"][nom]["wrong"]) <= F(b["decisions"][nom]["wrong"])
                                 for nom in p["nominated_volumes"])
            return (narrower or decisive) and no_worse_error
        additionality = all(improved(s) for s in gate)
        save(out, "strata.json.gz", strata); save(out, "trials.json.gz", trials); save(out, "witnesses.json.gz", witnesses)
        for name, h in preserved.items():
            assert sha((ROOT/name).read_bytes()) == h, name
        elapsed, peak, size = resources()
        summary = {"status": "PASS" if diagnostic_pass else "DIAGNOSTIC_FAILURE", "strata": len(strata),
             "trials": len(trials), "gate_strata": len(gate), "negative_controls": len(controls),
             "exact_valid_coverage_rows": len(strata)*3, "independent_count_and_relation_checks": len(trials),
             "witnesses": len(witnesses), "sampling_diagnostic_pass": diagnostic_pass,
             "absolute_utility_pass": absolute, "additionality_pass": additionality,
             "reports_identical_to_established_counterpart": True,
             "decision": ("advance_operational_model" if absolute and additionality else "park_operational_candidate")
                         if diagnostic_pass else "investigate_execution",
             "elapsed_seconds": elapsed, "peak_python_traced_bytes": peak, "artifact_bytes_before_summary": size,
             "stage_seconds": {"calibration_verification": calibration_seconds, "exact_laws": exact_seconds,
                 "sampling": sampling_seconds, "relation_construction": order_seconds,
                 "quantyra_reports": own_seconds, "reference_reports": ref_seconds},
             "preserved_files": len(preserved), "new_lean_invocations": 0,
             "limits": "Known continuous-model exact laws and float simulation diagnostics; no physical instrument or carrying-capacity validation; no globally optimal interval claim."}
        save(out, "summary.json", summary); resources(); print(json.dumps(summary), flush=True)
    except BaseException as exc:
        for name in ("strata", "trials", "witnesses"):
            if name in locals():
                save(out, "partial-"+name+".json.gz", locals()[name])
        save(out, "failure.json", {"error": str(exc), "traceback": traceback.format_exc(),
             "elapsed_seconds": time.perf_counter()-started})
        raise


if __name__ == "__main__":
    main()
