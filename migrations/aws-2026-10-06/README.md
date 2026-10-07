# Space credential consumer migration

Infrastructure scope under parent S3152/S3155/E003 and Space S012. No research publication or proof changes.

The publisher's AWS credential route now defaults to profile `quantyra`, region `us-east-1`, secret `quantyra/zenodo/access-token`. STS must identify account `063280428495` before GetSecretValue. The returned ARN must be `arn:aws:secretsmanager:us-east-1:063280428495:secret:quantyra/zenodo/access-token-D2k2iI`. Only the JSON field `ZENODO_ACCESS_TOKEN` becomes the Bearer header. Existing environment/file token routes remain available for separately authorized publication; credential-check mode always exercises AWS and ignores ambient token variables.

Read-only check from repository root:

```powershell
& 'C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe' checks/publish_manuscript_deposit.py --check-credentials
```

This mode requires no payload commit and exits before payload access, state-directory creation, upload, metadata edits or publication. It issues GET only, rejects redirects, and reports status/content type plus a list-shape success boolean. It does not log response bodies, token values, private deposit metadata or headers. It returns nonzero if authenticated JSON-list verification fails. `--publish` and `--check-credentials` are mutually exclusive. A plain `--commit` dry run validates frozen payloads without accessing credentials or making requests.

Migration regression checks:

```powershell
& 'C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe' checks/test_zenodo_credentials.py
& 'C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe' checks/publish_manuscript_deposit.py --commit 49b94b7af47a910d13e13d39ee45d4a359451e19
& 'C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe' checks/publish_manuscript_deposit.py --check-credentials --aws-profile cyint-ea-prod
& 'C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe' checks/publish_manuscript_deposit.py --check-credentials --publish
```

The last two commands must fail: source account is refused before secret retrieval, and conflicting modes are rejected by argparse. Six regression tests passed, including malformed-envelope/ARN rejection, account isolation, GET-only/no-redirect checks, response sanitization, HTML failure handling and exit before payload/state access.

Live results are in `consumer-check.json`. ServiceAdmin in destination account can read the expected version/stages and authenticate the deposit-list GET. Python Requests returns 200 JSON for the migrated Bearer and 403 JSON for no/invalid Bearer. Node fetch returns 403 HTML for all three credential cases with the same endpoint and secret. This reproduces the earlier Quantum diagnostic failure but discriminates it from credential validity in the actual Python consumer. A network/client/service-edge response difference is inferred; exact intermediary or rejection rule is undetermined. No body was inspected or retained.

[Zenodo documentation](https://developers.zenodo.org/) specifies Bearer headers and `deposit:write` / `deposit:actions` for publication workflows. The read-only check certifies authenticated list access, not write/action scope or permission to publish. Future publication remains subject to its existing explicit authorization and readiness gates.

No source secret deletion, role revocation, DNS switch, GCP move, Lean/Lake/compiler, proof or manuscript changes occurred. Source retirement remains parent S3156. Node diagnostic behavior belongs to parent S3155; the actual Space consumer passed.
