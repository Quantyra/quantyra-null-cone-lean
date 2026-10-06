# Lean verification checkpoint

2026-10-06, E002/S005. The complete selected finite realizer rank theorem is kernel checked, including a specialization matching the original specification. The full spacetime inverse bound remains a mathematical prose proof; it is not claimed as a compiled Lean theorem.

## Checked statements

| Theorem | Checked scope | Reported axioms |
| --- | --- | --- |
| `Realizer.five_edge_forcing` | Every two-order realizer propagates orientation along the five-edge comparable-witness path. | None |
| `Realizer.global_orientation` | One anchor orientation determines all eligible pairs, conditional on actual witness existence. | None |
| `occupied_grid_global_orientation` | Real-coordinate grid occupancy supplies the anchors and witnesses and yields one common orientation for all separated interior incomparable pairs. This discharges the geometric witness hypothesis rather than assuming it. | `propext`, `Classical.choice`, `Quot.sound` |
| `abs_rank_sub_le_disagreements` | Absolute difference of the real-coerced predecessor ranks is bounded by the number of pairwise comparison disagreements. | `propext`, `Classical.choice`, `Quot.sound` |
| `verticalStrip_card_le` | Empirical marginal error at most 2r implies a strip count at most 10rn for each interior event. | `propext`, `Classical.choice`, `Quot.sound` |
| `comparisons_agree` | Both coordinate comparisons agree outside the boundary and narrow vertical strip after the common orientation is chosen. | `propext`, `Classical.choice`, `Quot.sound` |
| `finite_realizer_rank_rigidity` | For ANY two-order realizer, ONE Boolean swap gives BOTH rank errors <=30rn for EVERY interior event. Witnesses, the strip count, and the disagreement bounds are derived, not assumed. | `propext`, `Classical.choice`, `Quot.sound` |
| `finite_realizer_rank_rigidity_specified` | Matches the original selected statement with r=1/m, unit-square coordinates, distinct coordinates, no grid-line ties, both marginal bounds, and normalized boundary fraction <=20r. | `propext`, `Classical.choice`, `Quot.sound` |

Sources are `QuantyraNullCone/Realizer.lean`, `Grid.lean`, `Counts.lean`, and `Bridges.lean`. The root module imports all four. No source contains `sorry`, `admit`, or a new axiom declaration. The axiom printer reports no `sorryAx` for the listed theorems. The foundational dependencies listed above are mathlib's ordinary Lean dependencies, not added geometric assumptions.

## Reproducible environment and checks

Lean executable: v4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, Windows x86_64. Mathlib checkout and manifest pin: `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Dependency revisions are saved in `lake-manifest.json`.

Executed the final `lake build QuantyraNullCone`: exit code 0, build completed successfully with 984 jobs. Each listed axiom report appeared in the build output. `lake env lean checks/Audit.lean` also exited zero and printed the full types and axiom dependencies of both final theorems. Inspection confirmed that the existential Boolean swap precedes the universal event quantifier and is shared by both inequalities. Standalone checks of the proof modules exited zero. This verifies all six components of the selected target, not the probability or continuous-density portions of the full inverse theorem.

For a fresh checkout, suppress the broad automatic cache hook during dependency update with `MATHLIB_NO_CACHE_ON_UPDATE=1`, then fetch only these module closures:

```text
lake update
lake exe cache get Mathlib.Data.Real.Archimedean Mathlib.Algebra.Order.Floor.Semiring Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
lake build QuantyraNullCone
lake env lean checks/Audit.lean
```

The environment variable applies to `lake update`; restore any previous value afterward. The focused cache fetched and decompressed 963 files successfully. An earlier broad cache attempt and the first focused retry ran out of disk space; those attempts failed and are not counted as verification. Task-generated temporary archives and failed extracted artifacts were cleaned, and the subsequent focused attempt and library build succeeded. Source repositories and unrelated files were preserved.

## Scope beyond this target

The original selected statement is a specialization of a stronger theorem: the rank proof only needs the v marginal bound; unit-square and no-grid-line assumptions are not needed once occupancy, the boundary count, and the two coordinate injectivity hypotheses are supplied. The original hypotheses were retained explicitly in the specified specialization to make the scope comparison checkable.

Remaining to-do list for this selected Lean target: none. Future work: formalize probability, cumulative reconstruction, and density interpolation if full inverse-theorem formalization is requested; obtain independent review and publication-level novelty assessment before discovery claims.
