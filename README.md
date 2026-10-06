# Quantyra finite-order spacetime research

Technical satellite for Quantyra Space Planning E002/S005. Bounded execution: Codex under Dan's research direction; this does not appoint an organizational officer.

Model and conjecture: `../Quantyra-Space-Planning/docs/finite-order-spacetime-theorem-specification.md`.

Current evidence includes a complete mathematical proof draft of an explicit inverse rate, not a Lean verification or a novelty claim. A Lean/mathlib environment is pinned and dependency setup has started; no selected theorem is compiled yet. Independent review remains pending.

See [identifiability proof draft](notes/identifiability.md).

The [quantitative reduction](notes/quantitative-reduction.md) proves an explicit rectangle-to-density bound in prose, gives its sharp exponent for that intermediary, and isolates the unproved finite-order reconstruction hypothesis sufficient for the main conjecture.

The newer [finite-order rate proof](notes/finite-order-rate.md) supplies that hypothesis and derives `d_conf <= 100 (N^(-1/12) + Delta_N)`. See the [author audit](notes/rate-audit.md) and [selected finite rank Lean target](notes/lean-target.md). The earlier conditional note records the derivation sequence; its formerly unproved hypothesis is now addressed by the newer draft.
