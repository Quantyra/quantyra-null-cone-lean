# Restricted confidence theorem: current checkpoint

S042, 2026-10-10. **The complete restricted all-pairs geometric confidence
theorem has full GCP acceptance.** S042's mathematical endpoint is complete;
S043 can proceed to bounded implementation/validation and its separate
3+1 decision. The overall research roadmap remains active.

The [milestone proof and investment audit](geometric-pair-audit.md) is the
authoritative mathematical account and decision. The preceding development
checkpoint is preserved at commit `f41945baa5ab066afca82aa00260151ed05aeefc`.

## Delivered result

The actual time-quadratic density family on the original 2+1 Lorentz diamond
has its exact pair law, geometric forward constant `3/20` and inverse factor
`225225/54952`. The deterministic statistic counts all strict relations and
descends to the original unlabeled order. Its permutation representation,
the full joint law of disjoint pairs and a Bernstein MGF give the actual
dependence-aware tail bound. The clipped inverse and midpoint policy yield
the stated uniform confidence radius, including the zero/one-sample case.

The endpoint is `time_pair_geometric_confidence3` in
[LorentzPairConfidence.lean](../QuantyraNullCone/LorentzPairConfidence.lean).
The ordinary audit's formula and conservative sufficient sample counts are
retained. The 95% crossover is 33,338 observations. This is a sufficient
guarantee, with no claim of measured utility, sharpness or a full-class rate.
The smooth reconstruction converse remains an explicit external result.

## Verification and execution

- Proof commit: `f4672c4ea5290e65759253e8052efae270702cbb`, pushed before acceptance.
- GCP run: `space-pair3-acceptance-20261010T130617Z-981811`, project `quantyra-lean-cert-20260915`, instance
  `quantyra-lean-builder-01`, zone `us-central1-a`.
- Full root: 3,193 jobs. Exact named type/axiom reports: 1,276, including 111
  additions across 27 modules since the preceding full audit. Zero warnings;
  standard axioms only.
- [Independent source/evidence verification](../evidence/geometric-gauge/pair-confidence-acceptance/acceptance-validation.json)
  matches all 266 captured files, including 232 Lean inputs, to the immutable
  archive, raw committed blobs and normalized local files. All preceding
  1,165 audit statements and earlier mathematical modules are preserved.
  Published manuscripts and frozen studies are unchanged.
- [Shutdown receipt](../evidence/gcp/space-pair3-acceptance-20261010T130617Z-981811/cleanup.json): task ownership from
  dev23, no other Lean/Lake work, all eleven terminal outcomes collected,
  cache hash verified, VM `TERMINATED` at `2026-10-10T13:13:50.861444+00:00`.

The current turn retains development runs dev23 through dev32 and the final
acceptance. Dev23 was canceled after a broad tactic import started unrelated
dependency builds. Before cleanup, exact hashes, birth times and the required
import closure verified that 1,904 newly created files (188,138,233 bytes)
were unnecessary. Only those files were moved into temporary RAM storage.
Existing dependencies, successful cache, source captures and logs were
preserved. The original terminal archive and supplemental maintenance archive
have separate custody checks. The RAM copy is temporary build storage, not a
permanent evidence archive. The retained controller now rejects broad
`Mathlib`/`Mathlib.Tactic` imports and missing Mathlib source imports before
submission. [Controller snapshot](../evidence/geometric-gauge/pair-confidence-acceptance/controller-snapshot.py).

Targeted builds reuse the verified task-owned compressed cache. The cache now
also contains the full accepted root dependency closure. Its SHA-256 is
`2d279c84a78af1c5654fda2d534fa19ce26f17652cf4e06425b51056d173b625` and size is
51,986,664 bytes. The full root build took 98 seconds;
this excludes transport, the separate type/axiom audit and collection.
Earlier unchanged-target and controlled-edit cache probes remain accepted;
they need not be repeated. No local Lean/Lake invocation occurred.

## Next action

Freeze a bounded S043 numerical protocol before generating evaluation data.
Reuse this theorem and model. Compare the inverse and selected policy with
the midpoint on known and withheld parameters. Report parameter error and
the certified geometric upper bound without calling the latter an exact
geometric distance. Include relation construction/counting cost, memory,
runtime and fallback frequency. Record whether practical investment is
warranted, then make the separate 3+1 feasibility decision.

All Lean remains on GCP. Any future run must establish new instance ownership.
The current compressed cache is retained; root disk free space is about
305 MiB, so check capacity before accumulating more immutable runs.

Remaining to-do list: S043 protocol, bounded validation and 3+1 decision;
then queued S047. S048 manuscript preparation remains proposed separately.
