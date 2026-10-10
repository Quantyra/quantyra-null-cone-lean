"""Frozen transfer control using a different physical holdoff acquisition."""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import zlib

import numpy as np
from scipy.io import loadmat, whosmat

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import lidar_record_screen as reader
import lidar_range_screen as parent
import lidar_range_audit as exposure
import lidar_history_screen as history


def upstream_check(model,fit,upstream):
    value,gradient = model.evaluate(np.array(fit["parameters"]))
    ll = 0.0
    score = np.zeros_like(gradient)
    for j,group in enumerate(model.groups):
        theta = np.array([fit["a"][j],fit["tau_ns"][group]/model.width+.5,fit["b_per_ns"][j]*model.width])
        row_ll,row_score = upstream.loglik_and_score(model.n[j],model.m[j],theta,model.phases,model.k,1.,1.,5,model.pulse)
        ll += row_ll
        score[j] = row_score[0]*theta[0]
        score[model.rows+j] = row_score[2]*theta[2]
        score[2*model.rows+group] += row_score[1]/model.width
    errors = [abs(ll+value*model.total),float(np.max(np.abs(score/model.total+gradient)))]
    assert errors[0]<1e-7 and errors[1]<1e-10
    return {"upstream_loglik_difference":float(errors[0]),"upstream_normalized_score_difference":errors[1]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache-dir",required=True,type=Path)
    parser.add_argument("--upstream-root",required=True,type=Path)
    parser.add_argument("--output",required=True,type=Path)
    parser.add_argument("--fetch",action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    protocol_path = HERE/"lidar-control-protocol.json"
    protocol = json.loads(protocol_path.read_text())
    original = json.loads((HERE/"lidar-range-protocol.json").read_text())
    parents = {}
    for name in ["lidar_record_screen.py","lidar_range_screen.py","lidar_range_audit.py","lidar_history_screen.py",
                 "lidar-range-protocol.json","lidar-history-results.json","lidar-range-audit.json"]:
        frozen = subprocess.check_output(["git","show",f'{protocol["parent_commit"]}:applications/detector-calibration/{name}'],cwd=HERE)
        working = (HERE/name).read_bytes()
        assert frozen.replace(b"\r\n",b"\n") == working.replace(b"\r\n",b"\n")
        parents[name] = {"working_sha256":parent.sha(HERE/name),"git_sha256":parent.hashlib.sha256(frozen).hexdigest()}
    ranges = reader.fetch_members(protocol,args.cache_dir) if args.fetch else []
    member = protocol["archive"]["members"][0]
    data_path = args.cache_dir/member["name"]
    payload = data_path.read_bytes()
    assert len(payload)==member["bytes"] and f'{zlib.crc32(payload):08x}'==member["crc32"]
    schema = [{"name":n,"shape":list(s),"class":c} for n,s,c in whosmat(data_path)]
    scalar_names = [row["name"] for row in schema if int(np.prod(row["shape"]))==1]
    metadata = reader.scalar_metadata(loadmat(data_path,variable_names=scalar_names))
    assert metadata["T_holdoff"]==protocol["holdoff_ns"] and metadata["T_holdoff"]>80
    raw_frames = loadmat(data_path,variable_names=["frameNum"])["frameNum"].ravel()
    provenance = {"file_sha256":parent.sha(data_path),"schema":schema,"scalars":metadata,
                  "full_frame_extent":[float(raw_frames.min()),float(raw_frames.max())],"full_detections":len(raw_frames)}
    assert parent.sha(args.cache_dir/original["pulse"]["path"])==original["pulse"]["sha256"]
    high = parent.Record(data_path,1000000)
    assert np.all(np.isfinite(high.phase)) and np.all(high.gap>0)
    provenance["development_detections"] = len(high.phase)
    provenance["minimum_development_gap_ns"] = float(high.gap.min())
    upstream,models,hashes = parent.source_modules(args.upstream_root,original)
    calibration = loadmat(args.cache_dir/original["pulse"]["path"],variable_names=["smoothPulseShape","binRes"])
    smooth = calibration["smoothPulseShape"].ravel()
    raw_width = float(calibration["binRes"].item())*1e9
    K = original["native_period_bins"]
    width = high.period/K
    phase_bins = np.floor(high.phase/width+.5).astype(np.int64)
    indices = high.frames*K+phase_bins
    gaps = np.diff(indices)
    prior = json.loads((HERE/"lidar-history-results.json").read_text())
    native = json.loads((HERE/"lidar-range-audit.json").read_text())
    result = {"protocol_sha256":parent.sha(protocol_path),"executable_sha256":parent.sha(__file__),
              "parents":parents,"input":provenance,"upstream_hashes":hashes,"requested_ranges":ranges,
              "synthetic_exposure_audit":exposure.synthetic_audit(),"variants":[],"range_benefit_demonstrated":False}
    edges = protocol["age_edges_ns"]+[np.inf]
    groups = np.array([int(a>=protocol["delay_split_ns"]) for a in edges[:-1]])
    for vi,previous_variant in enumerate(prior["variants"]):
        mass = smooth-smooth.min() if previous_variant["pulse"]=="smooth_min_subtracted" else smooth.copy()
        pulse = models.EmpiricalPulse(mass/mass.sum(),raw_width/width,K)
        row = {"pulse":previous_variant["pulse"],"windows":[]}
        for wi,window in enumerate(protocol["development_windows_frames"]):
            selected = (indices[1:]>=window[0]*K)&(indices[1:]<window[1]*K)
            D = min(int(gaps[selected].min())-1,int(np.floor((protocol["holdoff_ns"]+2)/width)))
            assert D>=int(np.floor(protocol["holdoff_ns"]/width))
            nh,mh = exposure.integer_cells(high,window,K,[(D+1)*width,np.inf])
            assert nh.sum()==np.count_nonzero(selected)
            phases = np.arange(K,dtype=float)
            robust = upstream.robust_pilot(nh[0],mh[0],phases,K,1.,1.,5,pulse)
            one = upstream.one_step(robust,nh[0],mh[0],(window[1]-window[0])*K,phases,K,1.,1.,5,pulse)
            pilot = [robust[0],(robust[1]-.5)*width,robust[2]/width]
            hard = exposure.fit(exposure.Model(nh,mh,pulse,width,False),pilot,protocol)
            ng,mg = exposure.integer_cells(high,window,K,[protocol["delay_split_ns"],np.inf])
            guard = exposure.fit(exposure.Model(ng,mg,pulse,width,False),pilot,protocol)
            n,m = exposure.integer_cells(high,window,K,edges)
            union_n,union_m = exposure.integer_cells(high,window,K,[edges[0],np.inf])
            assert np.array_equal(n.sum(axis=0),union_n[0]) and np.array_equal(m.sum(axis=0),union_m[0])
            common_model = history.Model(n,m,pulse,width,np.zeros(len(n),dtype=int))
            split_model = history.Model(n,m,pulse,width,groups)
            common = history.fit(common_model,pilot,protocol)
            split = history.fit(split_model,pilot,protocol,common)
            previous_mature = previous_variant["windows"][wi]["two_delays"]["tau_ns"][1]
            low = native["variants"][vi]["low_flux_provisional_reference"]["tau_ns"]
            item = {"window_frames":window,"dead_bins_D":D,"supported_first_open_age_ns":(D+1)*width,
                    "counts_by_age":n.sum(axis=1).tolist(),"age_partition_equal":True,
                    "native_hard":hard,"guarded":guard,"native_one_step_tau_ns":float((one[1]-.5)*width),
                    "common_delay":common,"two_delays":split,
                    "common_upstream_check":upstream_check(common_model,common,upstream),
                    "split_upstream_check":upstream_check(split_model,split,upstream),
                    "native_hard_minus_guard_mm":(hard["tau_ns"]-guard["tau_ns"])*parent.C_MM_PER_NS,
                    "early_minus_mature_mm":(split["tau_ns"][0]-split["tau_ns"][1])*parent.C_MM_PER_NS,
                    "mature_180_minus_mature_198_mm":(split["tau_ns"][1]-previous_mature)*parent.C_MM_PER_NS,
                    "mature_180_minus_low_flux_mm":(split["tau_ns"][1]-low)*parent.C_MM_PER_NS,
                    "mature_198_minus_low_flux_mm":(previous_mature-low)*parent.C_MM_PER_NS,
                    "split_minus_common_loglik":(common["negative_mean_loglik"]-split["negative_mean_loglik"])*split_model.total}
            if wi==1:
                trained = np.array(row["windows"][0]["two_delays"]["parameters"])
                item["trained_split_minus_optimized_common_loglik"] = (common["negative_mean_loglik"]-split_model.evaluate(trained)[0])*split_model.total
            row["windows"].append(item)
            print(json.dumps({"pulse":row["pulse"],"window":window,"early_minus_mature_mm":item["early_minus_mature_mm"],
                              "mature_control_difference_mm":item["mature_180_minus_mature_198_mm"],
                              "guard_change_mm":-item["native_hard_minus_guard_mm"]}),flush=True)
        result["variants"].append(row)
    differences = [w["mature_180_minus_mature_198_mm"] for v in result["variants"] for w in v["windows"]]
    result["descriptive_reference_stability_gate_pass"] = bool(max(abs(x) for x in differences)<=.2)
    result["physical_reference_validated"] = False
    result["limits"] = "Adaptive physical control with uncalibrated common timing origin, local working-template likelihood and quantized observations; no target stability bound, causal diagnosis, absolute accuracy or final decision benefit."
    args.output.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"output":str(args.output),"sha256":parent.sha(args.output),"reference_gate":result["descriptive_reference_stability_gate_pass"]}))


if __name__=="__main__":
    main()
