# S031 finite-data feasibility evidence

2026-10-08. **Complete pilot and audited decision: theoretical continuation; practical no-go for the frozen LP candidates.** All thirty reports validate and retain full-width point bands. The eighty conditional confirmation samples are not generated. The [study](../../../notes/finite-data-feasibility-study.md) and [version-1 protocol](../../../notes/finite-data-feasibility-protocol.json) remain unchanged. New arguments have ordinary-proof status, not new Lean acceptance. See the [results](../../../notes/finite-data-feasibility-results.md) and [decision](../../../notes/finite-data-feasibility-decision.md).

## Evidence map

- `manifest.json`: frozen implementation/proof identities, Python/DLL and numerical dependency identities, all worker outcomes and cumulative resource ledger; terminal decision fields are added only after the pilot gate.
- `pilot-run-manifest.json`: exact terminal runner output before the research disposition. `pilot-audit.json`, `pilot-audit.log` and `pilot-audit-resource.json` retain the successful source/pairing/resource/output audit, all thirty diagnostic rows, twenty exact LP witness pairs and the conditional timing forecast.
- `n512-m*-t0/` and `n3072-m*-t0/`: ten fixed case configurations and seeds, shared order/forcing artifacts, separate Bernstein/binomial/baseline report envelopes, per-method metrics/resources and raw logs. The original order is identical across all three methods in each case. No confirmation sample is generated during the pilot.
- `resource-preflight*/`: original small-limit timeout, allocation, RSS and child-process enforcement probes. Earlier probes remain as historical evidence. RSS is the OS lifetime peak working set of the single allowed process; the 10-ms watchdog rejects overshoot. It is not an instantaneous working-set reservation. Job committed memory is a separate metric.
- `pre-pilot-verification.txt`: canonical successful 24-test run. `pre-pilot-tests.txt` preserves an earlier PowerShell/Tee capture whose wrapper treated unittest's stderr as native-command error output; its test body also reports 24 passing tests. The clean receipt resolves the shell-wrapper ambiguity.
- `literature-retrieval.json`: source URLs, retrieval outcomes and hashes. Purchased/subscription PDFs and downloaded third-party full texts are not redistributed here.
- `standalone-verification.json` and `postflight-*.log`: additional standard-library-only reload/checks of all three retained n512 flat reports, with resources. Every successful pilot worker also independently reloads and verifies its own complete serialized report.
- `dependency-file-audit.json` and `dependency-file-audit-resolution.json`: 2,482 hashed installed package files match their wheel RECORD entries. The first audit reports two NumPy command launchers missing at RECORD's relative scripts path; the resolution verifies both exact hashes at the pip target installation's actual `site-packages/bin` location. No dependency file was changed. Unhashed generated entries are excluded from the hash claim.
- `source-line-ending-identities.json`: all 13 frozen source/protocol byte hashes match the actual frozen Git blobs. These identities also record LF normalization for readers using a different checkout line-ending policy; the execution's raw hashes remain authoritative.
- `rate-constant-audit.json`: 16 exact rational checks of constants used in the new theoretical construction. This checks arithmetic and source identity, not the analytic theorem.
- `accepted-source-preservation.json`: the 96 selected source identities from the existing accepted proof/manuscript map remain unchanged. This is preservation of earlier GCP evidence, not certification of the new arguments.

## Inspect a certificate without numerical packages

From the repository root, with Python 3.13:

```text
python -S tools/run_finite_data_feasibility.py verify evidence/finite-data/feasibility-v1/n512-m0-t0/bernstein.json.gz
python -S tools/run_finite_data_feasibility.py verify evidence/finite-data/feasibility-v1/n512-m0-t0/binomial.json.gz
python -S tools/run_finite_data_feasibility.py verify evidence/finite-data/feasibility-v1/n512-m0-t0/split-dkw.json.gz
```

The loader checks shared artifact hashes and uncompressed size limits, then reconstructs the input and forcing certificate before the exact checker runs. Keep each envelope beside its referenced `order.json.gz` and `rank.json.gz`. Checking a larger report requires more time and memory. The LP producer uses pinned NumPy/SciPy; the verifier uses the standard library.

`tools/audit_finite_data_feasibility.py` audits the retained ledger and output identities and constructs exact LP relaxation witnesses. The audit does not generate new samples. Its raw source checks require the frozen execution bytes (also available as Git blobs); a changed checkout line-ending policy is not a new accepted execution identity. The saved `pilot-run-manifest.json` preserves the pre-decision terminal runner output, permitting audit replay after `manifest.json` receives the final disposition.

Do not rerun the pilot into this directory. The controller refuses an existing manifest to prevent sample reuse or overwriting evidence. Fresh confirmation, a new estimator or larger sizes require their corresponding gate/scope; reproducing a certificate does not authorize those experiments.

## Interpretation

The candidate bands and midpoint radius, baseline's original error semantics, actual polynomial-family errors, analytic all-cell coverage and resource metrics are reported separately. A certificate proves that the submitted finite calculation passes its checker. The ordinary coverage argument supplies the probabilistic claim; simulation does not prove uniform coverage. A full-range band is covered but uninformative.

Each model/size has one pilot sample. Exact two-sided 95% binomial uncertainty is `[1/40,1]` for one success, or `[0,39/40]` for zero successes. Counts pooled over five different models are descriptive only. Rechecking a certificate does not add an independent statistical trial.

The theoretical degree-trimmed fourth-root estimator was neither implemented nor piloted here. Its ordinary proof and exact constant checks support a proposed separate certification handoff. Every Lean/Lake invocation remains remote GCP-only; this Python campaign started no cloud instance.

Remaining to-do list: none for the campaign. S032 certification is proposed separately, and no finite-data manuscript is selected.
