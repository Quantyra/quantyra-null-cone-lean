# Identifiability and inverse rate completion audit

2026-10-06, E002/S005. Objective: establish identifiability from abstract orders, derive or refute the quantitative bound, then select a substantive Lean proof target. The selected target has additionally been proved in Lean. The original class, observable, and geometric error have been preserved.

| Requirement | Authoritative evidence | Conclusion |
| --- | --- | --- |
| Restricted class and gauge | Planning `docs/finite-order-spacetime-theorem-specification.md`: smooth densities, 1/2 and 3/2 bounds, 2-Lipschitz, uniform marginals, unit volume; d_conf modulo one null-axis swap. | Preserved; no dynamics, topology, or curvature reconstruction substituted. |
| Abstract-order observations | `finite-order-rate.md` defines a deterministic label-based realizer choice using P alone. `observable-and-time-audit.md` proves labeled and unlabeled finite-law TV agree under iid exchangeability. | No coordinate rankings supplied as observations. |
| Identifiability in K | `finite-order-rate.md`: equal all-size laws make every Delta_N zero; the explicit inverse bound tends to zero. The earlier broader kernel-based draft is not needed for this conclusion. | Mathematically established in K, modulo swap. |
| Explicit quantitative bound | `finite-order-rate.md` and `quantitative-reduction.md`: occupancy and concentration give 174N^(-1/4) cumulative error; rectangle interpolation gives `d_conf <=100(N^(-1/12)+Delta_N)` for all N>=2, including the small-N branch. | Positive result with C=100, alpha=1/12, beta=1; not a compiled full inverse theorem. |
| Physically meaningful error | `observable-and-time-audit.md`: square-root rationalization, Cauchy-Schwarz, and identical admissible curves yield uniform proper-time error <=d_conf after the selected endpoint swap. | Prose corollary established; no derivative or carrying-capacity consequence claimed. |
| Substantive target and exact statement | `lean-target.md`; compiler types from `checks/Audit.lean`; `Bridges.lean` theorem `finite_realizer_rank_rigidity_specified`. | Original assumptions and BOTH rank bounds matched, with the existential swap before the universal event quantifier. |
| All six selected proof components | `Realizer.lean`, `Grid.lean`, `Counts.lean`, `Bridges.lean`, imported by the root library. | All implemented and checked; no witness or rank conclusions assumed in place of their proofs. |
| Reproducible formal verification | `lake build QuantyraNullCone`: exit zero, 984 jobs. `lake env lean checks/Audit.lean`: exit zero. Exact Lean/mathlib revisions and dependencies saved in `lean-verification.md` and the manifest. | Both final theorems report only `propext`, `Classical.choice`, `Quot.sound`; source audit finds no `sorry`, `admit`, or new axiom declaration. |
| Novelty check | Planning comparisons and `rate-audit.md` cover causal reconstruction, poset kernels, copulas/permutons, random orders, and graph orientations, including the final exact-source recheck. | No inspected exact duplicate located. Originality remains provisional; inaccessible/full-paper gaps are disclosed. A novelty search cannot certify a discovery. |
| Repository boundary | Technical proofs and audits are in mapped satellite `Quantyra/quantyra-null-cone-lean`; planning dispositions remain in `Quantyra-Space-Planning`. | Ownership, workstream mapping, and claims boundaries preserved. |

Independent refereeing before publication and formalizing the entire probability-to-density theorem are future activities. They are not represented as completed, and they do not enlarge this objective's selected Lean target into an unrequested full Lorentzian formalization. No publication or new-physics claim is made.

Repository closeout requires focused commits and verified remote SHAs after this audit is saved. The goal completion decision must follow that verification, rather than treating this document alone as evidence of a successful push.

Remaining to-do list for the requested objective: commit and verify this turn's final artifacts. After verified closeout, none; future publication gates remain independent review and originality assessment.
