# Sharp-DKW likelihood barrier: partial S024

2026-10-07 local date (2026-10-08 UTC). The universal analytic likelihood barrier is now formalized. This does not yet certify DKW concentration or the finite-data coverage report.

For every real `0 < e < 1`, `dkw_sharp_likelihood_barrier` proves that there exists a positive `lambda` such that, simultaneously for every `0 < t <= 1-e`,

`2*e^2 <= (t+e)*log(1+lambda/t)-log(1+lambda)`.

Only the tolerance bounds are hypotheses. A stationary point, Pinsker inequality, derivative sign, convexity, concavity or the barrier conclusion is not assumed. The same chosen lambda works for all thresholds.

The seven new modules prove logarithmic ratio bounds from mathlib's proved Taylor estimates; bracket and obtain a stationary parameter by the intermediate value theorem in both tolerance regimes; derive Bernoulli Pinsker from two explicit derivatives and monotonicity; compute the likelihood derivatives; derive its convex/concave shape; identify its stationary value as Bernoulli relative entropy; and prove the endpoint bound. `DKWLikelihood.lean` assembles those facts into the universal statement. Cases where the likelihood is convex everywhere and where its inflection lies beyond the threshold interval are included. No numerical diagnostic supplies a universal premise.

Authoritative run: `space-dkw-analytic-acceptance-20261008T022033Z-1e119b`, GCP project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. The root build passed 2924 jobs and 115 exact-type/axiom audits, exit zero, with no warnings or added axioms. The [receipt](../evidence/gcp/space-dkw-analytic-acceptance-20261008T022033Z-1e119b/receipt.json), immutable input archive, source/dependency manifest and raw logs retain exact accepted bytes and before/after source plus all nine pinned dependency identity checks. Lean 4.30.0 and mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f remain pinned. Local Lean invocations: zero.

The [development ledger](../evidence/gcp/dkw-analytic-development-index.json) retains six captures, including all four failed compilation attempts and the successful development build with its later-removed linter warning. The first boot SSH preflight closed before upload/launch; the same immutable capture was subsequently submitted after a clean workload check. No live proof job was restarted because of an observation timeout. Published manuscripts and DOI artifacts are preserved.

The task-started VM was verified TERMINATED after acceptance collection and a successful check for other Lean/Lake work. Raw shutdown/final-state evidence is retained in the acceptance run.

The next obligation is probabilistic: derive finite uniform-bin likelihood expectations and a maximal bound, transport to actual uniform samples, pass to dense grids, reflect and combine the two tails. Actual-K marginal transport and the joint-grid union/rounding bridge must then supply the accuracy premises in the already-proved conditional trimmed CDF theorem. Density cell feasibility, all-point expansion, histogram/fallback and complete report representation also remain open. This proof retains the sharp exponent needed by the existing calibration rather than substituting a weaker library bound.

Remaining to-do list: sharp finite-bin probability and dense-grid/reflection transport; actual-K coverage/calibration bridge; density/report suite and final S024 acceptance; S025.
