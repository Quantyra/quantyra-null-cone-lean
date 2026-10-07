"""In-memory AWS credential retrieval and read-only Zenodo diagnostics."""

import json

import boto3
import requests
from botocore.exceptions import BotoCoreError, ClientError

ACCOUNT = "063280428495"
SECRET = "quantyra/zenodo/access-token"
SECRET_ARN = "arn:aws:secretsmanager:us-east-1:063280428495:secret:quantyra/zenodo/access-token-D2k2iI"
API = "https://zenodo.org/api"


def aws_token(secret_id=SECRET, profile="quantyra", region="us-east-1"):
    """Verify account before reading; never expose SDK errors or secret contents."""
    try:
        session = boto3.Session(profile_name=profile, region_name=region)
        identity = session.client("sts").get_caller_identity()
        if identity["Account"] != ACCOUNT:
            raise SystemExit("AWS account mismatch; no secret read or Zenodo request performed")
        secret = session.client("secretsmanager").get_secret_value(SecretId=secret_id)
        if secret["ARN"] != SECRET_ARN:
            raise SystemExit("AWS secret ARN mismatch; no Zenodo request performed")
        envelope = json.loads(secret["SecretString"])
        token = envelope.get("ZENODO_ACCESS_TOKEN")
        if not isinstance(token, str) or not token or token != token.strip() or any(
            c.isspace() for c in token
        ):
            raise ValueError("invalid token field")
    except (BotoCoreError, ClientError):
        raise SystemExit("AWS credential lookup failed; no Zenodo request performed") from None
    except (ValueError, KeyError, TypeError, AttributeError):
        raise SystemExit("Invalid AWS secret envelope; no Zenodo request performed") from None
    return token, {
        "account": identity["Account"], "principal": identity["Arn"],
        "profile": profile, "region": region, "secret_arn": secret["ARN"],
        "version_id": secret["VersionId"], "stages": secret.get("VersionStages", []),
        "token_field": "ZENODO_ACCESS_TOKEN",
    }


def read_only_check(token, aws_metadata):
    """GET only, no redirects, bodies/headers/account data omitted from output."""
    probes = []
    for label, path, bearer in (
        ("public_record", "/records/23206773", None),
        ("unauthenticated", "/deposit/depositions", None),
        ("invalid_bearer", "/deposit/depositions", "migration-invalid-control"),
        ("migrated_bearer", "/deposit/depositions", token),
    ):
        try:
            response = requests.get(
                API + path, headers={"Authorization": f"Bearer {bearer}"} if bearer else {},
                timeout=30, allow_redirects=False,
            )
            content_type = response.headers.get("Content-Type", "").split(";", 1)[0].lower()
            valid_list = False
            if label == "migrated_bearer" and response.status_code == 200 and content_type == "application/json":
                try:
                    valid_list = isinstance(response.json(), list)
                except ValueError:
                    pass
            probes.append({"probe": label, "method": "GET", "path": path,
                           "status": response.status_code, "content_type": content_type,
                           "authenticated_list_verified": valid_list})
        except requests.RequestException:
            probes.append({"probe": label, "method": "GET", "path": path,
                           "transport_error": True})
    passed = probes[-1].get("authenticated_list_verified", False)
    print(json.dumps({"aws": aws_metadata, "zenodo": probes,
                      "credential_check_passed": passed, "publication_writes": 0}, indent=2))
    return passed
