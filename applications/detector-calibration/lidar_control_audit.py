"""Working-model precision diagnostic, not calibrated physical error bars.

For predictable open slots, Bernoulli p=1-exp(-z) contributes expected
information M*exp(-z)/(1-exp(-z)) dz dz^T. Plugging in observed exposure
counts gives the empirical information used by the pinned comparator.
Invert after including every fitted signal/background nuisance parameter.
This holds the pulse calibration fixed and omits drift/model uncertainty.
"""

import argparse
import json
from pathlib import Path
import sys

import numpy as np
from scipy.io import loadmat

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import lidar_range_screen as parent
import lidar_range_audit as exposure


def information(m,fit,pulse,width,groups,upstream,horizon):
    rows,K = m.shape
    phases = np.arange(K,dtype=float)
    matrix = np.zeros((2*rows+2,2*rows+2))
    source = np.zeros_like(matrix)
    for j,group in enumerate(groups):
        a,b = fit["a"][j],fit["b_per_ns"][j]*width
        tau = fit["tau_ns"][group]/width+.5
        f = pulse.bin_mass(phases,tau)
        df = pulse.bin_mass_derivative(phases,tau)/width
        z = a*f+b
        weights = m[j]*np.exp(-z)/(-np.expm1(-z))
        derivatives = np.column_stack([a*f,a*df,np.full(K,b)])
        cell = derivatives.T @ (derivatives*weights[:,None])
        indices = [j,2*rows+group,rows+j]
        matrix[np.ix_(indices,indices)] += cell
        scale = np.array([a,1/width,b])
        native = upstream.fisher_from_open_counts(m[j],horizon,np.array([a,tau,b]),phases,K,1.,1.,5,pulse)*horizon
        source[np.ix_(indices,indices)] += native*np.outer(scale,scale)
    relative_error = float(np.max(np.abs(matrix-source))/np.max(np.abs(matrix)))
    assert relative_error < 1e-12
    eigen = np.linalg.eigvalsh(matrix)
    assert eigen.min()>0
    covariance = np.linalg.inv(matrix)
    inverse_error = float(np.max(np.abs(matrix@covariance-np.eye(len(matrix)))))
    assert inverse_error < 1e-9
    v = covariance[-2:,-2:]*parent.C_MM_PER_NS**2
    return {"delay_covariance_mm2":v.tolist(),"early_sd_mm":float(np.sqrt(v[0,0])),
            "mature_sd_mm":float(np.sqrt(v[1,1])),"contrast_sd_mm":float(np.sqrt(v[0,0]+v[1,1]-2*v[0,1])),
            "information_condition_number":float(eigen.max()/eigen.min()),
            "source_relative_information_difference":relative_error,"inverse_identity_difference":inverse_error}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache-dir",type=Path,required=True)
    parser.add_argument("--upstream-root",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    if args.output.exists():raise FileExistsError(args.output)
    original = json.loads((HERE/"lidar-range-protocol.json").read_text())
    upstream,models,_ = parent.source_modules(args.upstream_root,original)
    calibration = loadmat(args.cache_dir/original["pulse"]["path"],variable_names=["smoothPulseShape","binRes"])
    assert parent.sha(args.cache_dir/original["pulse"]["path"])==original["pulse"]["sha256"]
    smooth = calibration["smoothPulseShape"].ravel()
    raw_width = float(calibration["binRes"].item())*1e9
    report = {"executable_sha256":parent.sha(__file__),"fits":[],"result_hashes":{},"comparisons":[],
              "physical_error_control_validated":False,
              "limits":"Local fitted Bernoulli information with empirical exposures and fixed pulse. No sandwich/drift/reference/calibration uncertainty. Cross-record standard errors additionally assume independent acquisition errors. These are diagnostic scales, not confidence intervals or physical significance tests."}
    for tag,prefix in [(180,"control"),(198,"history")]:
        protocol = json.loads((HERE/f"lidar-{prefix}-protocol.json").read_text())
        result_path = HERE/f"lidar-{prefix}-results.json"
        result = json.loads(result_path.read_text())
        assert result["protocol_sha256"]==parent.sha(HERE/f"lidar-{prefix}-protocol.json")
        assert result["executable_sha256"]==parent.sha(HERE/f"lidar_{prefix}_screen.py")
        data_path = args.cache_dir/(protocol["archive"]["members"][0]["name"] if tag==180 else original["high_flux"]["path"])
        expected = result["input"]["file_sha256"] if tag==180 else original["high_flux"]["sha256"]
        assert parent.sha(data_path)==expected
        record = parent.Record(data_path,1000000)
        K = original["native_period_bins"];width=record.period/K
        edges = protocol["age_edges_ns"]+[np.inf]
        groups = np.array([int(a>=protocol["delay_split_ns"]) for a in edges[:-1]])
        report["result_hashes"][prefix] = parent.sha(result_path)
        for variant in result["variants"]:
            mass = smooth-smooth.min() if variant["pulse"]=="smooth_min_subtracted" else smooth.copy()
            pulse = models.EmpiricalPulse(mass/mass.sum(),raw_width/width,K)
            for window in variant["windows"]:
                bounds = window["window_frames"]
                _,m = exposure.integer_cells(record,bounds,K,edges)
                detail = information(m,window["two_delays"],pulse,width,groups,upstream,(bounds[1]-bounds[0])*K)
                report["fits"].append({"holdoff_ns":tag,"pulse":variant["pulse"],"window":bounds,
                                       "tau_ns":window["two_delays"]["tau_ns"],**detail})
    for control in report["fits"][:4]:
        reference = next(r for r in report["fits"] if r["holdoff_ns"]==198 and r["pulse"]==control["pulse"] and r["window"]==control["window"])
        difference = (control["tau_ns"][1]-reference["tau_ns"][1])*parent.C_MM_PER_NS
        sd = np.hypot(control["mature_sd_mm"],reference["mature_sd_mm"])
        report["comparisons"].append({"pulse":control["pulse"],"window":control["window"],"mature_difference_mm":difference,
                                       "conditional_independent_record_sd_mm":float(sd),"difference_over_diagnostic_sd":float(difference/sd)})
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({"sha256":parent.sha(args.output),"comparisons":report["comparisons"]}))


if __name__=="__main__":main()
