# Genuine 2+1 finite labeling bridge

S042 component, 2026-10-09 (Hawaii). The actual iid Lorentz-order labeling bridge has GCP acceptance. **S042 remains incomplete.** This component does not certify the geometric representation, a quantitative inverse, random labeling of one observed order, or higher-dimensional reconstruction.

## Accepted scope

[LorentzUnlabeled.lean](../QuantyraNullCone/LorentzUnlabeled.lean) uses the existing genuine 2+1 `LorentzPoint3`, `densityMeasure3`, `sampleMeasure3`, `sampledOrder3`, `orderLaw3`, and directed-order isomorphism quotient. The new results prove sample permutation preservation, order-law exchangeability, singleton/fiber constancy, exact equality of labeled and unlabeled total variation, and equivalence of labeled/unlabeled law equality at every fixed finite size, including zero and one.

The general results require only finiteness of the actual density measure, not smoothness. Their distance expression is finite half-L1; on the explicitly instantiated `InDensityClass3` probability model it is the usual total variation distance. This makes the finite bridge usable later for continuous density classes once their measure hypotheses are established. It does not supply those classes' geometric reconstruction theorem.

Twelve exact type/axiom reports were added to the root audit:

- `relabelSample3_apply`, `sampledOrder3_relabel`, `sample_relabel_preserving3`;
- `orderLaw3_exchangeable`, `orderLaw3_singleton_relabel`, `orderLaw3_fiber_constant`, `orderLaw3_finite`;
- `unlabeledOrderLawTV3_eq`, `finite_measure_eq_of_L1_zero`, `unlabeledOrderLaw3_eq_iff`;
- `InDensityClass3.unlabeledOrderLawTV_eq`, `InDensityClass3.unlabeledOrderLaw_eq_iff`.

The generic finite fiber lemma is existing project work. This is its new actual 2+1 specialization, not a new general reconstruction or exchangeability principle. Relabeling does not add time reversal, coordinate observations or anchors. There is no attempt to reorder an infinite generic sample.

## Exact-source cloud acceptance

Proof/source commit: `3a94f7bd2f820d1a1eca5fa6ae5337e9a8caf8de`. Accepted run: [space-gaugelabel-acceptance-20261010T050509Z-efb057](../evidence/gcp/space-gaugelabel-acceptance-20261010T050509Z-efb057/). Project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`; isolated immutable source and build storage. The root build completes 3,098 jobs; the full audit contains 809 exact type/axiom reports, including the previous 797. The acceptance controller checks zero warnings, no unfinished proof tokens, only standard `propext`, `Classical.choice`, `Quot.sound` dependencies, and exact source/pinned dependency identities before and after execution. No local Lean or Lake invocation was used.

All 201 captured files, including 167 Lean inputs, match both the committed Git bytes and the normalized local source. Input archive SHA-256: `85599b706b37a9e726e6846df3d9c0640b4d2b493f8b87c270587012a10c74af`. New module SHA-256: `81bbc85e22fb66cd17a9b7f3ca9aa93c84810919923ab0aae42a4d5a9428406d`. Existing mathematical module files are unchanged from the accepted S046 source, and its 797 audit statements remain verbatim before the additions.

The [first development failure](../evidence/gcp/space-gaugelabel-dev1-20261010T045917Z-a3e0aa/) is preserved with immutable input, raw diagnostics and terminal exit one. It exposed a dependent simplification problem and a redundant final tactic. The corrected source was pushed before acceptance. The failed run is not certification; its temporary build cache/link was reclaimed only after collecting its terminal evidence. Raw logs retain their original bytes through scoped Git attributes.

The instance began terminated and was started for this campaign. After collecting and checking the acceptance, the cleanup preflight found no other Lean/Lake process. [Cleanup evidence](../evidence/gcp/space-gaugelabel-acceptance-20261010T050509Z-efb057/cleanup.json) verifies final state `TERMINATED` at `2026-10-10T05:12:02.847079+00:00`. Both the failed run and accepted outcome remain preserved. No hosted CI is substituted for GCP acceptance.

## Mathematical continuation

The [ordinary representation note](geometric-diamond-representation.md) still needs formal boundary, weighted proper-time, gauge and continuity work. The full selected class has an ordinary qualitative compactness argument but no explicit usable inverse modulus. A separate [restricted-family pair calculation](geometric-pair-conditioning.md) supplies an ordinary candidate with explicit two-point conditioning and conservative finite confidence. Its class membership, geometric moments, actual pair law, loss bound and random-label/disjoint-block observation bridge remain uncertified. Rational arithmetic and numerical quadrature checks are diagnostic only.

Remaining to-do list: complete S042's geometric and quantitative proofs with GCP acceptance; audit the restricted-family route and source comparison; then decide S043's gate. S047 remains queued separately; no new manuscript or physical application is claimed.
