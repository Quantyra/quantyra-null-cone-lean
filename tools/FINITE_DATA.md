# Finite-data reconstruction

Estimate from one full strict directed order, without latent coordinate inputs. [Coverage proof and limits](../notes/finite-data-certified-method.md). The [experiment report](../notes/finite-data-experiment-report.md) states what the finite guarantees achieve. This Python method is separate from the GCP-verified Lean library.

Install Python 3.13-compatible pinned NumPy/SciPy:

```text
python -m pip install -r tools/requirements-finite-data.txt
python -m unittest discover -s tools -p test_finite_data.py -v
```

Input JSON uses vertices 0,...,n-1 and **all** strict relations, including transitive ones:

```json
{"n":4,"relations":[[0,2],[0,3],[1,3]]}
```

```text
python tools/finite_data.py estimate input.json --grid 8 --delta 1/20 --output result.json
python tools/finite_data.py verify result.json
python tools/finite_data.py estimate input.json --calibration grid --output legacy-result.json
python tools/benchmark_finite_data.py --output experiments.json --trials 8 --sizes 128 512 --grid 8
```

Use a fresh output path; existing files are not overwritten. Invalid/cyclic/incomplete-transitive or non-two-dimensional orders are rejected. The dense reference implementation caps n at 4096, estimation grid at 16 and order input JSON at 64 MiB. Certificate reports use compact JSON and a separate 512 MiB cap, since forcing trees add evidence beyond the input. Oversized reports are rejected before writing. Polynomial graph work and 2k^2+1 LP solves may be costly before those caps. The verifier runs with the Python standard library alone: SciPy proposes solutions only during estimation.

The result contains the two permutations, a rooted original-graph forcing certificate, rational calibration, exact dual outer certificates and a histogram/bands. Rational quantities are strings such as `1/20`; human-readable floating diagnostic widths in experiment output are not substituted for certificates. `cdf_radius` is a simultaneous population-CDF bound in one global orientation, with `failure_upper` for the requested confidence. `cell_lower/upper` bound aligned cell-average densities; `point_lower/upper` expand them to simultaneous pointwise bounds. The histogram's exact corner residual is included in its conservative error bound. It is a piecewise coefficient estimate, not a smooth conformal metric.

Full-range bands `[1/2,3/2]` and error bound one mean the method has no certified density resolution at that setting. A smaller CDF bound does not by itself prove practically useful density recovery. Numerical solver failures or inconsistent restrictions return conservative full-range bands and a reported fallback status; they do not certify mathematical infeasibility. No noisy-order repair, optimal sample complexity or curvature claim is included.

For the Windows embedded development interpreter, dependencies are isolated at `C:/Users/dfred/QuantyraTools/FiniteData/site-packages`; insert that directory and `tools` into `sys.path` before `runpy.run_path`/unittest. Ordinary Python users use the commands above. This support runtime does not run Lean.

New estimates default to `split-dkw`: separate finite DKW marginal concentration and fixed-grid joint concentration. [Derivation and exact rounding](../notes/finite-data-confidence-sharpening.md). Use `--calibration grid` to reproduce the original calibration, including the historical 80-trial experiment. Reports lacking a method field continue to verify as legacy reports.

Remaining to-do list: none for CLI usage; research improvements follow the experiment gate.
