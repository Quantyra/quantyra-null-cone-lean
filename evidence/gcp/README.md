# Exact-source GCP verification

Successful run: [space-20261007T093129Z-retry1](space-20261007T093129Z-retry1/receipt.json). Baseline: exact satellite commit `22e00590055b40041bda00d2cc3882788d0abe3b`. Candidate: baseline plus the four owned source/audit files listed in the manifest. `inputs.tar.gz` in [space-20261007T090025Z-58150c4e](space-20261007T090025Z-58150c4e/inputs.tar.gz) retains the exact baseline and candidate source bytes. Manifests, shell runners, all compiler/audit logs, source/dependency checks, timestamps and terminal exits are retained.

The first run exited 1 before compiling the proof library because `cache unpack` rejects module arguments. The successful successor restored dependency tracked files from their pinned Git trees to remove Windows line-ending differences, then used `cache unpack` without arguments. All nine dependency trees were subsequently verified byte for byte. No dependency revision changed. Linux toolchain and offline archive SHA256 values are in `transferred-artifacts.json`.

Lean 4.30.0: baseline root build 2583 jobs and twelve export audits; candidate root build 2584 jobs and sixteen export audits. Both passed without compiler warnings. Existing finite/grid Python checks also passed. This verifies the deterministic intermediate scope, not the unfinished full inverse theorem. The isolated GCP instance was returned to TERMINATED after collecting evidence.

## Original probability stage

[space-sampling-20261007T103552Z-585351](space-sampling-20261007T103552Z-585351/receipt.json) verifies the root build (2898 jobs) and thirty-two export audits with zero warnings. The [development index](sampling-development-index.json) retains failures and the earlier successful compile with two owned lint warnings; only the final clean root/audit run is accepted. Its original-K probability export gives `9/10` reconstruction success with `174 n^(-1/4)` error for `n>=65536`. Source archives, hashes and complete compiler/audit output are retained for every attempt. This remains an intermediate S013 result; the coefficient inverse theorem is unfinished.

## Density interpolation

[space-interpolation-20261007T112652Z-43e687](space-interpolation-20261007T112652Z-43e687/receipt.json) verifies the root build (2899 jobs) and thirty-five export audits without warnings. The [development index](interpolation-development-index.json) retains the earlier failed attempt and successful module check. The actual-K interpolation export proves the cubic `2048 epsilon` bound; observable-TV separation and all-N inverse assembly remain incomplete.
