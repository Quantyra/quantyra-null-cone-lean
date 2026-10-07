# S012-S014 acceptance audit

2026-10-07. Scope is the three stories selected by Dan: separate manuscript deposit, original coefficient inverse formalization and grid-scale optimization. This audit checks the actual artifacts and theorem types rather than treating a green build as evidence of a broader claim. Final commit/hosted-check delivery is recorded in the planning closeout.

## S012: separate manuscript deposit

| Requirement | Inspected evidence | Outcome |
| --- | --- | --- |
| Final manuscript, author/license/AI/review disclosures, software relation | Frozen [metadata](../manuscript/deposit/zenodo-metadata.json), [manifest](../manuscript/deposit/manifest.json), [bundle](../manuscript/deposit/bundle.json), current `CITATION.cff` | Version 0.2.0, Daniel Eric Fredriksen/Quantyra Inc, CC-BY-4.0, open preprint, separate software DOI; informal review and actual formal scope disclosed |
| Compile, references, all pages, freeze hashes | Published-package build/visual record in [deposit README](../manuscript/deposit/README.md); eight-page PDF; frozen commit `49b94b7af47a910d13e13d39ee45d4a359451e19` | Prior Tectonic/reference/all-page review identifies the same PDF bytes freshly downloaded below |
| Concrete package and publication instruction | S012's dated preparation/publication/custody record and the immutable published receipt | Dan selected actual deposit and supplied the credential; no new publication action is needed |
| Live identifier/metadata/file identity; preserve software | Fresh [artifact audit](../evidence/completion-2026-10-07/artifact-audit.json), [public manuscript record](../evidence/completion-2026-10-07/public-manuscript-record.json), [software record](../evidence/completion-2026-10-07/public-software-record.json) | DOI `10.5281/zenodo.23206773`; both downloaded SHA256/MD5 values and local files match frozen receipt; software DOI `10.5281/zenodo.23202763` remains version 0.1.0 |
| Citation/planning and focused delivery | Current citation/deposit records, pushed historical publication commits; final delivery recorded in Space Planning | Separate manuscript/software citations preserved; immutable payload not regenerated |

The archived manuscript's formal-scope text is historical. New main-branch Lean proofs do not change its version, content hashes or DOI payload.

## S013: original inverse theorem

| Contract/acceptance requirement | Concrete exports and inspected source | Outcome |
| --- | --- | --- |
| Original K and actual measures/laws, without latent observations | `Model.lean`, `Measures.lean`, `DensityCDF.lean`: neighborhood smoothness, bounds 1/2..3/2, explicit Euclidean Lipschitz two, uniform marginals, product-volume density, actual iid law and Boolean chronology | Probability normalization/measurability are derived; parameters match frozen contracts |
| F1 deterministic cumulative bridge | `Cumulative.lean`, `GridAccuracy.lean`: inclusive rank identity, marginal/boundary/latent-CDF deductions, all-threshold `87r`, one global alignment for every realizer | Auxiliary occupancy/accuracy premises are discharged by the later actual probability stage |
| F2 uniform probability, null events and integer estimates | `Sampling.lean`, `Coordinates.lean`, `Concentration.lean`, `GoodSamples.lean`, `ProbabilityRate.lean` | Actual iid null ties/grid lines, cell mass/occupancy/Hoeffding bounds, fourth-root floor estimates; mass >=9/10 at `174 n^(-1/4)` for n>=65536. Neither axes within a point nor overlapping events are assumed independent |
| F3 density interpolation | `DensityInterpolation.lean` | Actual supremum attainment, boundary-valid square, signed density integral and four-corner inclusion/exclusion prove `delta^3<=2048 epsilon`; no interpolation conclusion is assumed |
| F4 same observable selector, TV separation and transpose | `OrderSelector.lean`, `FiniteTV.lean`, `Transpose.lean` | Density-independent code-only measurable selector with fixed invalid-code output; actual 90% good events, half-L1 event bound, overlap below TV 4/5; one global CDF orientation; original-K transpose closure and measure/CDF/isometry identities |
| F5 original all-N estimate | `InverseRate.lean`, `InDensityClass.full_inverse` | Exactly `d_conf<=100(N^(-1/12)+Delta_N)` for every N>=2. Small-N and high-TV branches proved. Main assumptions are only original K and N>=2 |
| F6 all-law identifiability | `Identifiability.lean`, `InDensityClass.all_law_identifiability` | Equality of all actual laws implies equality everywhere on D under one global identity/transpose, by the vanishing rate and actual supremum norm; no equality outside D is claimed |
| Original unlabeled observable and scope fidelity | `Exchangeability.lean`, `QuotientTV.lean`, `Unlabeled.lean` | Sampled chronology is a strict partial order; actual iid index permutations preserve the laws. Finite quotient equality is directed-order isomorphism. Actual fiber constants prove exact TV/Delta equivalence and probability normalization. `full_inverse_unlabeled` and `all_unlabeled_law_identifiability` use only those quotient laws; time-reversed duals are not identified |
| Root imports, exact types, foundations, immutable source and dependency verification | [GCP receipt](../evidence/gcp/space-unlabeled-20261007T123238Z-759aaa/receipt.json), [raw logs](../evidence/gcp/space-unlabeled-20261007T123238Z-759aaa/logs), [capture](../evidence/gcp/space-unlabeled-20261007T123238Z-759aaa/capture-manifest.json), root and `checks/Audit.lean` | Complete 2907-job GCP root build, 68 selected exact-type/axiom reports, zero errors/warnings/unsolved goals/admitted dependencies; only `propext`, `Classical.choice`, `Quot.sound`. Before/after hashes and all nine pinned dependency revisions/clean tracked trees verified |
| Scope documentation and delivery | README, INTEGRITY, verification/contracts and observable audit notes; frozen software/manuscript preserved | Original coefficient theorem is formalized. Proper-time and the optimized logarithmic-grid Lean proof remain separately selectable prose consequences; originality remains provisional. Focused final delivery/CI is recorded in planning |

The exact quantitative unlabeled theorem assumes only `InDensityClass rho`, `InDensityClass sigma` and `2<=N`. Its discrepancy uses the pushforward of the actual iid chronological law by the finite isomorphism quotient. No normalization, concentration, reconstruction, interpolation, exchangeability, overlap or final coefficient conclusion is an extra hypothesis.

## S014: grid-scale optimization

| Requirement | Inspected evidence | Outcome |
| --- | --- | --- |
| Integer grid, constants, cutoff and small-N fallback | [Complete derivation](grid-scale-optimization.md) | `m=floor(sqrt(n/(8 log n)))`, ncut=65536, m>=16, floor direction, rate term and small-N branch explicit |
| Both failure terms, uniform K and rounding | Derivation's occupancy/vertex section, compared with the original probability bridges | Sum <=1/10 from `1/(8 n^3 log n)+n^(-15)/log n`; no extra independence hypothesis |
| `87r`, interpolation, TV propagation and exact constant | Derivation's coefficient section | `C_*=(4096*174*sqrt(8))^(1/3)<130` by the exact integer comparison `4063575932928<4826809000000`; TV coefficient and fixed orientation retained |
| Informal audit before manuscript revision; no optimality/practical-budget claim | Dated author-directed audit, frozen 0.2.0 manuscript | Complete derivation reviewed under the open-source workflow; no specialist review/adoption gate applies |
| Checks, manuscript build, commits/pushes | Fresh [grid-scale check](../evidence/completion-2026-10-07/grid-scale-check.txt), historical exact-commit CI and deposit hash identity | 612 sizes and 173 floor transitions pass at 100-digit precision; coefficient 126.323668677941050<130. Published eight-page PDF is the previously compiled/visually checked artifact |

No newly requested work remains in the mathematical or publication scope of S012-S014. Final hosted-check and planning-commit closeout is recorded separately before marking the goal complete. S009-S011 reconciliation and future feedback/literature work keep their own scopes.

Remaining to-do list: final exact-commit delivery/hosted checks and planning closeout.

## Final delivery closeout ? 2026-10-07

The full original-observable proof and requirement audit are committed and pushed at `b7d762acc9c10ca881f8366f545f3998b0528448`. [Supplementary hosted checks](https://github.com/Quantyra/quantyra-null-cone-lean/actions/runs/37622943270) passed both jobs, including the root/type/axiom audit, all existing finite/grid sanity checks and manuscript compilation. Exact proof/check/build-configuration bytes match the authoritative GCP capture, with sixty-eight export reports and no compiler warnings. Fresh public manuscript PDF/source identities and software DOI/version were verified; S014's high-precision check passed. The task-started GCP instance is TERMINATED. Final planning closeout records S012-S014 completion and supersedes development-stage delivery to-do lists.

Remaining to-do list: none for S012-S014.
