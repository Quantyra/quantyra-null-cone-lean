# A certified coordinate-gauge obstruction in a 2+1 diamond

Separate manuscript by Daniel Eric Fredriksen, Quantyra Inc., version 0.1.0, 8 October 2026. **Unpublished; no DOI assigned.** [Read the PDF](conformal-gauge-counterexample.pdf) or [TeX](conformal-gauge-counterexample.tex). This is a second paper, distinct from the [published reconstruction manuscript 0.4.0](https://doi.org/10.5281/zenodo.23247720).

The explicit example has smooth normalized densities in [1/2,3/2] with Euclidean Lipschitz constant at most two, identical finite directed-order laws and positive coefficient distance modulo spatial O(2). The metrics are nevertheless isometric. The construction uses the established causal-diamond conformal flow. The paper supplies the complete construction and proofs, a bounded primary-source comparison, and exact links to the accepted Lean statements; it claims no new conformal flow, physical nonidentifiability or mathematical priority.

[Formal statement map](formal-map.json), [source/evidence verification](source-verification.json), [literature comparison](literature-comparison.md), [algebra check](algebra-check.json) and [page review](review.json) record the scope and exact artifacts. The main export is `QuantyraNullCone.higher_dimensional_gauge_counterexample3`. The accepted proof/evidence revision is `74c1f743d085c63b45ac2bf30008ad5d29b98fbc`, GCP run `space-lorentz-acceptance-20261008T071627Z-221cd8` (295 selected exports across the full library, 76 added by this campaign). Existing source identities are verified without invoking Lean locally.

Build from the repository root with Tectonic 0.17.0 and Python with PyMuPDF 1.28.2:

```text
python manuscript/conformal-gauge/build.py --tectonic /path/to/tectonic
```

The script retains the raw compiler log and renders every page under ignored `tmp/conformal-gauge-review`. Inspect every page before updating the review receipt. All manuscript references must resolve and layout warnings must be addressed. A nonfatal Fontconfig configuration notice on the preparation machine was handled by checking rendered fonts.

The independent symbolic check uses SymPy 1.14.0:

```text
python manuscript/conformal-gauge/check_algebra.py
python manuscript/conformal-gauge/verify_sources.py
```

It checks polynomial derivative/Jacobian, inverse, separation and null identities; the literature parameter conversion; and exact rational class/anchor bounds. These are supplementary checks, separate from the universal Lean proofs and written domain/probability arguments. `verify_sources.py` hashes the accepted Lean/audit/pin/control sources and checks the retained exact-type reports; it never launches Lean/Lake. To reproduce Lean acceptance, follow [INTEGRITY.md](../../INTEGRITY.md) **on remote GCP**, with the pinned dependencies. Hosted CI remains supplementary.

All files here are CC-BY-4.0. The proof library is Apache-2.0. OpenAI Codex assistance is disclosed in the manuscript; decentralized informal feedback, use and testing remain the review workflow. Third-party papers were inspected through primary public sources; their full PDFs are not redistributed in this repository.

Remaining to-do list: none for S028 manuscript preparation and review. DOI publication remains a subsequent action.
