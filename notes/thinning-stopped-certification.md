# First-n retained sampling: termination, iid law and physical coverage

2026-10-09 (Hawaii), S040. The actual first-n stopping experiment now has GCP acceptance. This completes the stopping/termination endpoint of the [ordinary process derivation](independent-thinning-process.md), building on the [finite-pattern law](thinning-certification.md), [infinite-stream construction](thinning-process-certification.md) and [Laplace-functional acceptance](thinning-laplace-certification.md). Complete geometric/marked-law confounding and S040's final decision audit remain open.

## Experiment and termination

Generate an infinite iid stream of location/uniform pairs (X_i,U_i), with location probability law mu and uniform marks on [0,1]. Keep X_i exactly when U_i < pi(X_i), where pi is measurable, integrable, takes values in [0,1], and has mean Z > 0. For a prescribed n, stop at the least prefix containing exactly n acceptances. Return those n locations in their original generation-index order.

The formal total map `retainedStopPrefix` takes value zero on nontermination; `stoppedRetainedView` uses the existing retained-tuple fallback there. These maps are measurable. Positive Z proves the exceptional set has probability zero, rather than assuming the process terminates. For n=0 the stopping prefix is exactly zero and the returned tuple is empty.

The proof first bounds the probability of no successes after a fixed index by `(1-Z)^r` for every finite window length r. Its limit is zero. A countable union then shows that the acceptance-index set is infinite almost surely. The actual finite-prefix retained count equals `Nat.count`, whose range is all natural numbers on an infinite acceptance set. Thus every prescribed retained count is reached almost surely.

## Actual stopped law

For each prefix length N, a finite collection of Boolean patterns describes precisely the event that the nth acceptance is first reached at N. Every pattern in that collection has n acceptances. The accepted finite-pattern theorem therefore gives the same normalized retained product law, scaled by the terminal event's actual probability.

The null nontermination set is removed using the proved almost-sure result. Summing the disjoint stopping-time fibers gives

    Law(first n retained locations) = nu^n,     nu = pi mu / Z.

The joint stopping-time/location submeasure and the conditional location law at every positive-probability stopping prefix are also certified. Terminal probabilities are represented by their explicit finite-pattern events; this delivery does not add a simplified negative-binomial coefficient formula. Measurable functions of the stopped tuple inherit the corresponding pushforward of nu^n.

This is an actual stopped experiment on the original iid stream. It does not take retained iid sampling or termination as extra assumptions. It covers Z=1, zero-probability terminal patterns and n=0. It does not cover a stopping rule chosen from observed geometry, adaptive anchors, correlated detection or missing relations.

## Physical-volume report

Compose the stopped tuple with the fixed-anchor interval-membership map. Its law is the accepted `markedIntervalLaw nu n C p q`. If `0<a<=pi<=b<=1` and a rational binomial report passes its validity contract, transforming its endpoints with the accepted retention bounds gives failure probability at most delta for normalized physical interval volume under the actual stopped experiment.

`InDensityClass.stopped_physical_report_coverage` specializes this result to the original density class, strict null chronology, fixed anchors and the executable rational report checker. The unknown true target occurs only in the mathematical failure event; it is not supplied to the report algorithm. This provides the mathematical rejection-sampling justification used by the frozen pilot. Python/SciPy execution and floating-point sampling remain separately tested implementation semantics, not Lean-compiled code. No field detector, absolute scale or application advantage is validated.

## Formal map

| Module | Accepted obligations |
| --- | --- |
| `ThinningTermination.lean` | Vanishing no-success tails, infinitely many successes almost surely, actual prefix-count identity and count surjectivity |
| `ThinningStopping.lean` | Measurable hit/stopping/tuple maps, first-prefix specification and minimality, null fallback, n=0 and almost-sure termination |
| `ThinningTerminalPatterns.lean` | Finite-pattern characterization of stopping and selected-pattern/stream submeasure laws |
| `ThinningStoppedLaw.lean` | Joint stopping-prefix submeasure, conditional retained law, unconditional first-n iid law and measurable observation composition |
| `ThinningStoppedCoverage.lean` | Actual stopped marked-membership law, physical report coverage and original geometric-class specialization |

## Acceptance and delivery

Run `space-firstretained-acceptance-20261010T003652Z-af3642` passed **3,079 root-build jobs and 673 exact type/axiom reports**, including all 26 new theorems. All 176 captured source identities and pinned dependencies were verified before and after. There were zero warnings and only `propext`, `Classical.choice` and `Quot.sound`. Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` ran on `quantyra-lean-builder-01`, `us-central1-a`, project `quantyra-lean-cert-20260915`. [Receipt](../evidence/gcp/space-firstretained-acceptance-20261010T003652Z-af3642/receipt.json).

The [custody verifier](../checks/verify_first_retained_acceptance.py) checks the input archive, every captured source, exact current/staged Git bytes, full theorem reports, protected 647-export baseline and frozen pilot. [Verification result](../evidence/firstretained/formal-verification.json). Development failures and transport retries are retained under `evidence/gcp/space-firstretained-*`. Compilation used isolated ephemeral GCP RAM build caches, seeded from the preserved disk cache; sources, inputs and logs remained persistent. Terminal development cache links were reclaimed only after collection and exact path/ownership checks. Prior accepted artifacts and other campaigns were preserved.

After collection and a no-other-Lean-work check, the campaign-owned VM was stopped and verified `TERMINATED` at `2026-10-10T00:44:32.554744+00:00`. [Cleanup](../evidence/gcp/space-firstretained-acceptance-20261010T003652Z-af3642/cleanup.json). No workstation Lean invocation, hosted-CI proof run, new sample, manuscript or DOI change occurred.

Remaining to-do list: complete admissible geometric/full-marked-law confounding, physical target separations and randomized obstruction; S040's final requirement and decision audit. S039, S042-S044 and S046 remain selected.
