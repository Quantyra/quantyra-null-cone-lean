# Lean verification checkpoint

2026-10-06, E002/S005. Four supporting theorems are kernel checked. The selected finite realizer rank theorem and the full spacetime inverse bound are not yet formally verified.

## Checked statements

| Theorem | Checked scope | Reported axioms |
| --- | --- | --- |
| `Realizer.five_edge_forcing` | Every two-order realizer propagates orientation along the five-edge comparable-witness path. | None |
| `Realizer.global_orientation` | One anchor orientation determines all eligible pairs, conditional on actual witness existence. | None |
| `occupied_grid_global_orientation` | Real-coordinate grid occupancy supplies the anchors and witnesses and yields one common orientation for all separated interior incomparable pairs. This discharges the geometric witness hypothesis rather than assuming it. | `propext`, `Classical.choice`, `Quot.sound` |
| `abs_rank_sub_le_disagreements` | Absolute difference of the real-coerced predecessor ranks is bounded by the number of pairwise comparison disagreements. | `propext`, `Classical.choice`, `Quot.sound` |

Sources are `QuantyraNullCone/Realizer.lean`, `Grid.lean`, and `Counts.lean`. The root module imports all three. No source contains `sorry`, `admit`, or a new axiom declaration. The axiom printer reports no `sorryAx` for the listed theorems. The foundational dependencies listed above are mathlib's ordinary Lean dependencies, not added geometric assumptions.

## Reproducible environment and checks

Lean executable: v4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, Windows x86_64. Mathlib checkout and manifest pin: `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Dependency revisions are saved in `lake-manifest.json`.

Executed `lake build QuantyraNullCone`: exit code 0, build completed successfully with 983 jobs. Each listed axiom report appeared in the build output. Standalone checks of each source also exited zero. A successful root build covers these component theorems, not an absent final theorem.

For a fresh checkout, suppress the broad automatic cache hook during dependency update with `MATHLIB_NO_CACHE_ON_UPDATE=1`, then fetch only these module closures:

```text
lake update
lake exe cache get Mathlib.Data.Real.Archimedean Mathlib.Algebra.Order.Floor.Semiring Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
lake build QuantyraNullCone
```

The environment variable applies to `lake update`; restore any previous value afterward. The focused cache fetched and decompressed 963 files successfully. An earlier broad cache attempt and the first focused retry ran out of disk space; those attempts failed and are not counted as verification. Task-generated temporary archives and failed extracted artifacts were cleaned, and the subsequent focused attempt and library build succeeded. Source repositories and unrelated files were preserved.

## Remaining proof bridge

Use the uniform empirical marginal bound to count the vertical strip, combine it with the boundary count, and show every remaining rank disagreement belongs to that union. Then apply the checked general rank-count lemma and assemble BOTH coordinate bounds with ONE Boolean swap for the entire sample. Until that theorem compiles, the selected six-component target in `lean-target.md` remains incomplete.

Remaining to-do list: formalize the marginal-strip and geometric disagreement bounds; assemble the full finite rank theorem; compile and inspect its axioms; compare the exact inverse-rate argument against prior work and obtain independent review before publication claims.
