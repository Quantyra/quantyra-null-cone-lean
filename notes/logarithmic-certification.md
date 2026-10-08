# Logarithmic inverse certification: S022

2026-10-07 local date (2026-10-08 UTC acceptance). Current software proves the published sharper estimate for original K and every N>=2:

`conformalDistance rho sigma <=130*((log N/N)^(1/6)+unlabeledFiniteLawDiscrepancy rho sigma N)`.

[LogGridRate.lean](../QuantyraNullCone/LogGridRate.lean) proves the natural-log cutoff at 65536, integer floor grid, both failure terms, actual sample reconstruction probability at least 9/10 and observable selector success with CDF radius `174 sqrt(8) sqrt(log n/n)`. The cutoff uses the logarithm tangent inequality; no concentration or good-event conclusion is assumed.

[ImprovedInverse.lean](../QuantyraNullCone/ImprovedInverse.lean) proves finite-law common-event overlap, one global CDF orbit, actual cubic density interpolation and exact constant 130. The all-N export handles high-TV and small-sample branches and transports the result to actual unlabeled directed-order laws through the existing proved TV identity. Main assumptions are exactly original K for both densities and N>=2.

Authoritative run: `space-loggrid-acceptance-20261008T000726Z-1e4d11`, project `quantyra-lean-cert-20260915`, VM `quantyra-lean-builder-01`, zone `us-central1-a`. [Receipt](../evidence/gcp/space-loggrid-acceptance-20261008T000726Z-1e4d11/receipt.json), [capture manifest](../evidence/gcp/space-loggrid-acceptance-20261008T000726Z-1e4d11/capture-manifest.json), [immutable inputs](../evidence/gcp/space-loggrid-acceptance-20261008T000726Z-1e4d11/inputs.tar.gz), [runner](../evidence/gcp/space-loggrid-acceptance-20261008T000726Z-1e4d11/run.sh) and [raw logs](../evidence/gcp/space-loggrid-acceptance-20261008T000726Z-1e4d11/logs) retain complete evidence. Root build: 2909 jobs, exit zero; 78 exact-type/axiom reports; no warnings, admissions or added axioms. Only `propext`, `Classical.choice`, `Quot.sound` occur in new exports. Captured proof/check bytes match the local delivery; source hashes and nine pinned dependency identities/clean tracked trees were checked before and after. Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` remain pinned.

The [development ledger](../evidence/gcp/logarithmic-development-index.json) retains five immutable runs, including two failed proof attempts. First boot-time SSH preflight closed before upload or launch; the same capture was submitted after verifying no remote workspace or competing Lean work. Failed attempts retain inputs and terminal logs. Every Lean/Lake command ran on GCP; local Lean invocations: zero. Shutdown evidence accompanies the final run after collection and checking for other Lean/Lake work.

This enlarges main-branch software certification, preserving the original inverse and all immutable DOI artifacts. Manuscript 0.3.1 describes its historical scope. Certification establishes the encoded bound, not priority, optimality, practical inference or new physics. Proper time, current finite-data guarantees and the higher-dimensional counterexample remain uncertified.

Source/evidence commit `678c9c953f81e3ed0f5393603a84a48a1910a857` is pushed. [Supplementary proof/manuscript CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37706983942), [literature CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37706983934) and [finite-data CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37706983950) all passed. Final cloud state is TERMINATED. Transfer progress whitespace remains preserved in raw logs.

Remaining to-do list: none for S022; complete S023-S025 under the selected four-story goal.
