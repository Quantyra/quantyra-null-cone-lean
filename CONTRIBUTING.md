# Contributing proofs, tests and prior-work evidence

Quantyra uses open-source, decentralized informal review. Important proofs are available for others to use and test. A specialist appointment, formal review report or adoption threshold is not required. [Research navigation](RESEARCH.md) identifies the versioned paper, exact formal statements, verification scope and reproducibility instructions.

Use [GitHub issues](https://github.com/Quantyra/quantyra-null-cone-lean/issues/new/choose) for an error, counterexample, build failure, prior-work implication, question, improvement or observed downstream use. Pull requests are welcome through the same repository. Include the affected release/DOI or exact commit, theorem/proof step or file, reproduction command or mathematical argument, expected and observed behavior, and supporting logs/source links. An issue identifying a stronger existing theorem should explain the model, observable, symmetry and implication, rather than rely on a similar title.

For proof/build reports, state the Lean/mathlib versions and platform. Quantyra's own development and acceptance Lean invocations run on remote GCP; retained exact-source audits are authoritative and hosted CI is supplementary. Python estimator tests execute without Lean. Never edit frozen release/deposit artifacts to hide a correction; preserve the affected version and supply a versioned fix with its evidence.

## Handling feedback

1. Classify the report as correctness, reproduction, prior work, improvement, question or use/testing. Record the affected claim/version and the evidence available. Acknowledge substantive uncertainty without claiming that a passing build answers a mathematical objection.
2. Reproduce a code/build issue on the pinned input/environment, or check each step of the mathematical argument. If a report is incomplete, ask for the smallest example or missing provenance; record the unresolved obligation.
3. Create a lane-local epic/story for actionable work and link the issue. Prioritize the global forcing/swap, clipped 87r bridge, uniform probability, CDF orbit/TV separation, boundary interpolation, and the new estimator's forcing/dual certificates.
4. Make a focused fix or give a supported response explaining why the claim remains valid. Verify at the scope of the changed claim. Lean changes need exact-source GCP build/type/axiom evidence; manuscript changes need compilation and every-page review. Retain counterexamples and failed attempts when they inform the result.
5. Link the issue, fixing commit, verification receipt and any corrected manuscript version. Close only the resolved part. If a released claim changes, explain affected versions and the correction openly, and publish a new version when authorized.

[Community evidence](notes/community-evidence.md) records observed reports, downstream builds/tests, reuse and corrections with dates, source links, versions and limits. Internal author/Codex tests are identified as internal and do not count as outside review or adoption. A successful downstream build establishes a build on that environment, not general correctness, significance or mathematical priority. Participation remains voluntary after this mechanism is delivered.

Remaining to-do list: none for the contribution mechanism; actual future reports are ongoing maintenance.
