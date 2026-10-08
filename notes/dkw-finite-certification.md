# Sharp finite-grid counting-law DKW: partial S024

2026-10-07 local date (2026-10-08 UTC). The exact sharp finite-bin counting-law tail bound is now Lean proved. Continuous uniform-sample and actual-K statistical coverage remain open.

For every positive n and q and every real e>=0, `finite_bin_two_sided_DKW` proves

`card{profiles with some grid CDF error > e}/q^n <= 2*exp(-2*n*e^2)`.

Profiles are actual functions `Fin n -> Fin q`, scored by value plus one. Their empirical CDF at k/q counts indices with bin value <k and divides by n. All k=0..q are covered, including support endpoints. The left side is the uniform counting probability on profiles; equality with a continuous sample's quantized product measure is a separate remaining bridge.

`DKWBins.lean` derives the Cartesian revealed-atom representation, exact atom cardinal, terminal product factorization, terminal sum and atom likelihood identity. `DKWMaximal.lean` proves later counts are determined by a revealed state, sums terminal identities over invariant events, partitions the crossing event by its first crossing, and derives the direct finite Ville bound. The maximal conclusion or a martingale property is not assumed in the actual-bin export.

`DKWFiniteCDF.lean` combines the accepted universal analytic likelihood barrier with actual count/CDF bounds, logarithms and positive exponentials. Its one-sided theorem has only n>0, q>0 and 0<e<1 as hypotheses. `DKWFiniteTail.lean` proves exact bin reflection/complement counts, reflection injectivity and the two-tail cardinal bound. It covers e=0 and e>=1 explicitly, exporting the sharp factor two for every nonnegative tolerance. No n-fold threshold union or weaker exponential constant replaces the required sharp target.

Authoritative acceptance: `space-dkw-finite-acceptance-20261008T025036Z-645562`, GCP project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. The complete root build passed 2928 jobs and 125 exact-type/axiom audits, exit zero, with no warnings or added axioms. The [receipt](../evidence/gcp/space-dkw-finite-acceptance-20261008T025036Z-645562/receipt.json), immutable inputs, source/dependency manifest and raw logs preserve exact accepted bytes and all nine dependency identities checked before/after. Lean 4.30.0 and mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f remain pinned. Local Lean invocations: zero.

The [development ledger](../evidence/gcp/dkw-finite-development-index.json) retains six captures, including all five failed attempts; several parent modules successfully compiled during those failed combined targets. No live job was restarted following an observation timeout. Original proofs and immutable manuscripts/DOI artifacts remain preserved. This result is mathematical tail control and does not improve full-range practical density bands.

The task-started VM was verified TERMINATED after collection and a successful check for other Lean/Lake work. Shutdown and final-state evidence are retained in the acceptance run.

The [remaining probability contract](dkw-finite-probability-contract.md) now starts at quantization and actual uniform measure transport, then the dense-grid limit and actual-K marginal/joint/calibration bridge. These must discharge the empirical accuracy premises in `checked_trimmed_CDF`. Cell-average feasibility, all-point expansion, histogram/fallback and the full executable report representation remain separate open obligations.

Source/evidence commit `9ffa877a361eef651da8461950e6f73c42aea560` is pushed. Supplementary [proof/manuscript CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37720349215), [literature CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37720349200) and [Python CI](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37720349232) all passed. This closeout changes evidence/docs only; proof/check/config bytes retain the accepted identities.

Remaining to-do list: continuous uniform quantization/law and dense-grid DKW; actual-K coverage/calibration; density/report suite and full S024 acceptance; S025.
