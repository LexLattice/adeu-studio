from __future__ import annotations

import argparse
import base64
import binascii
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json, sha256_canonical_json

from ._v48_signing_common import (
    AHK4803_ARTIFACT_INVALID,
    AHK4804_CROSS_ARTIFACT_HASH_MISMATCH,
    AHK4805_ALGORITHM_POLICY_VIOLATION,
    AHK4806_KEY_LIFECYCLE_POLICY_VIOLATION,
    AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID,
    AHK4810_SIGNATURE_VERIFICATION_FAILED,
    AHK4811_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
    DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    DEFAULT_REJECTIONS_ROOT,
    SigningIssue,
    TaskpackSigningError,
    coerce_artifact_path,
    emit_rejection_diagnostic,
    fail,
    is_sha256,
    load_diagnostic_registry,
    load_json_object,
    normalize_relative_path,
    parse_reference_time_utc,
    project_repo_root,
    require_deterministic_env_v48,
    require_schema,
    require_string,
    safe_join,
    write_json,
)
from .compile import (
    TASKPACK_MANIFEST_SCHEMA,
    TaskpackCompileError,
    VerifiedTaskpackSnapshot,
    load_verified_taskpack_snapshot,
    verify_taskpack_bundle,
)

SIGNATURE_ENVELOPE_SCHEMA = "taskpack_signature_envelope@1"
TRUST_ANCHOR_REGISTRY_SCHEMA = "taskpack_trust_anchor_registry@1"
SIGNATURE_VERIFICATION_RESULT_SCHEMA = "signature_verification_result@1"
SIGNATURE_VERIFIER_RESULT_SCHEMA = "taskpack_signature_verifier_result@1"
SIGNING_CONTRACT_SCHEMA = "v34a_signing_contract@1"

DEFAULT_SIGNING_OUTPUT_ROOT = "artifacts/agent_harness/v48/signing"
_PRE_FLIGHT_ENTRYPOINT = "python -m adeu_agent_harness.verify_taskpack_signature"

_ALGORITHM_POLICY_ENUM = ("ed25519", "p256")
_SIGNATURE_RESULT_REQUIRED_KEYS = {
    "schema",
    "contract_schema",
    "taskpack_manifest_hash",
    "taskpack_bundle_hash",
    "signature_envelope_hash",
    "trust_anchor_registry_hash",
    "verification_reference_time_utc",
    "preflight_invocation_binding_hash",
    "signer_key_id",
    "algorithm",
    "verified",
    "verification_library",
}
_NONDETERMINISTIC_RESULT_FIELDS = {
    "wall_clock_timestamp",
    "host_identity",
    "absolute_paths",
    "random_nonce",
}

_REQUIRED_ENVELOPE_KEYS = {
    "schema",
    "signer_key_id",
    "algorithm",
    "taskpack_bundle_hash",
    "taskpack_manifest_hash",
    "signature",
}

_REQUIRED_TRUST_ANCHOR_REGISTRY_KEYS = {"schema", "keys"}
_REQUIRED_TRUST_ANCHOR_KEY_FIELDS = {
    "key_id",
    "algorithm",
    "public_key",
    "revoked",
    "expires_at_utc",
}

_RFC3339_UTC_Z_SECOND_PRECISION_PATTERN = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z")
_ED25519_SPKI_DER_PREFIX = bytes.fromhex("302a300506032b6570032100")


@dataclass(frozen=True)
class TrustAnchorKeyRecord:
    key_id: str
    algorithm: str
    public_key: bytes
    revoked: bool
    expires_at_utc: datetime


@dataclass(frozen=True)
class TaskpackSignatureVerificationResult:
    verification_result_path: Path
    verification_result_hash: str
    rejection_diagnostic_path: Path | None


@dataclass(frozen=True)
class ValidatedDownstreamSignatureHandoff:
    taskpack_snapshot: VerifiedTaskpackSnapshot
    signature_verification_result_path: Path
    signature_verification_result_payload: dict[str, Any]
    signature_envelope_path: Path
    signature_envelope_payload: dict[str, Any]
    signature_envelope_hash: str
    trust_anchor_registry_path: Path
    trust_anchor_registry_hash: str
    verification_reference_time_utc: str
    signer_key_id: str
    algorithm: str


def _decode_base64_field(*, value: str, field: str, artifact_path: str) -> bytes:
    try:
        decoded = base64.b64decode(value, validate=True)
    except binascii.Error as exc:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="base64 field is malformed",
            details={"field": field},
            artifact_path=artifact_path,
        ) from exc
    if not decoded:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="base64 field must decode to non-empty bytes",
            details={"field": field},
            artifact_path=artifact_path,
        )
    return decoded


def _parse_utc_timestamp(*, value: Any, field: str, artifact_path: str) -> datetime:
    text = require_string(value, field=field, artifact_path=artifact_path)
    if not _RFC3339_UTC_Z_SECOND_PRECISION_PATTERN.fullmatch(text):
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message=f"{field} must match RFC3339 UTC Z second precision",
            details={field: text},
            artifact_path=artifact_path,
            policy_source="trust_anchor_registry",
        )
    try:
        parsed = datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError as exc:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message=f"{field} value is invalid",
            details={field: text},
            artifact_path=artifact_path,
            policy_source="trust_anchor_registry",
        ) from exc
    return parsed.replace(tzinfo=timezone.utc)


def _compute_taskpack_bundle_hash(*, manifest_payload: dict[str, Any], artifact_path: str) -> str:
    components_raw = manifest_payload.get("components")
    if not isinstance(components_raw, list) or not components_raw:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="taskpack manifest components must be a non-empty array",
            details={"path": artifact_path},
            artifact_path=artifact_path,
            policy_source="taskpack_manifest",
        )

    subject_records: list[dict[str, str]] = []
    for index, component in enumerate(components_raw):
        if not isinstance(component, dict):
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="taskpack manifest component entry must be an object",
                details={"path": artifact_path, "index": index},
                artifact_path=artifact_path,
                policy_source="taskpack_manifest",
            )
        relative_path = require_string(
            component.get("relative_path"),
            field="relative_path",
            artifact_path=artifact_path,
        )
        sha256_value = require_string(
            component.get("sha256"),
            field="sha256",
            artifact_path=artifact_path,
        )
        normalized_path = normalize_relative_path(relative_path)
        if not is_sha256(sha256_value):
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="taskpack manifest component sha256 must be lowercase 64-char hash",
                details={"path": artifact_path, "index": index, "sha256": sha256_value},
                artifact_path=artifact_path,
                policy_source="taskpack_manifest",
            )
        subject_records.append({"path": normalized_path, "sha256": sha256_value})

    subject_records.sort(key=lambda entry: entry["path"])
    return sha256_canonical_json(subject_records)


def _compute_preflight_invocation_binding_hash(
    *,
    manifest_hash: str,
    bundle_hash: str,
    signature_envelope_hash: str,
    trust_anchor_registry_hash: str,
    verification_reference_time_utc: str,
) -> str:
    return sha256_canonical_json(
        [
            _PRE_FLIGHT_ENTRYPOINT,
            manifest_hash,
            bundle_hash,
            signature_envelope_hash,
            trust_anchor_registry_hash,
            verification_reference_time_utc,
        ]
    )


def _load_signature_envelope(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=SIGNATURE_ENVELOPE_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_ENVELOPE_KEYS:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="signature envelope keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="signature_envelope",
        )

    signer_key_id = require_string(
        payload.get("signer_key_id"), field="signer_key_id", artifact_path=str(path)
    )
    algorithm = require_string(payload.get("algorithm"), field="algorithm", artifact_path=str(path))
    if algorithm not in _ALGORITHM_POLICY_ENUM:
        raise fail(
            code=AHK4805_ALGORITHM_POLICY_VIOLATION,
            message="signature envelope algorithm is outside frozen policy enum",
            details={"path": str(path), "algorithm": algorithm},
            artifact_path=str(path),
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source="signature_envelope",
        )

    for field in ("taskpack_bundle_hash", "taskpack_manifest_hash"):
        value = require_string(payload.get(field), field=field, artifact_path=str(path))
        if not is_sha256(value):
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="signature envelope hash binding field is invalid",
                details={"path": str(path), "field": field, "value": value},
                artifact_path=str(path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_envelope",
            )

    require_string(payload.get("signature"), field="signature", artifact_path=str(path))
    return payload


def _load_trust_anchor_registry(path: Path) -> dict[str, TrustAnchorKeyRecord]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=TRUST_ANCHOR_REGISTRY_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_TRUST_ANCHOR_REGISTRY_KEYS:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="trust anchor registry keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="trust_anchor_registry",
        )

    keys_raw = payload.get("keys")
    if not isinstance(keys_raw, list) or not keys_raw:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="trust anchor registry keys must be a non-empty array",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="trust_anchor_registry",
        )

    records: dict[str, TrustAnchorKeyRecord] = {}
    ordered_key_ids: list[str] = []
    for index, entry in enumerate(keys_raw):
        if not isinstance(entry, dict):
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="trust anchor registry key entry must be an object",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="trust_anchor_registry",
            )
        if set(entry.keys()) != _REQUIRED_TRUST_ANCHOR_KEY_FIELDS:
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="trust anchor registry key entry keys must match frozen grammar",
                details={
                    "path": str(path),
                    "index": index,
                    "keys": sorted(entry.keys()),
                },
                artifact_path=str(path),
                policy_source="trust_anchor_registry",
            )

        key_id = require_string(entry.get("key_id"), field="key_id", artifact_path=str(path))
        algorithm = require_string(
            entry.get("algorithm"), field="algorithm", artifact_path=str(path)
        )
        if algorithm not in _ALGORITHM_POLICY_ENUM:
            raise fail(
                code=AHK4805_ALGORITHM_POLICY_VIOLATION,
                message="trust anchor registry algorithm is outside frozen policy enum",
                details={"path": str(path), "index": index, "algorithm": algorithm},
                artifact_path=str(path),
                signer_key_id=key_id,
                algorithm=algorithm,
                policy_source="trust_anchor_registry",
            )

        if key_id in records:
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="trust anchor registry key_id entries must be unique",
                details={"path": str(path), "key_id": key_id},
                artifact_path=str(path),
                signer_key_id=key_id,
                algorithm=algorithm,
                policy_source="trust_anchor_registry",
            )

        revoked = entry.get("revoked")
        if not isinstance(revoked, bool):
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="trust anchor registry revoked field must be boolean",
                details={"path": str(path), "key_id": key_id},
                artifact_path=str(path),
                signer_key_id=key_id,
                algorithm=algorithm,
                policy_source="trust_anchor_registry",
            )

        expires_at_utc = _parse_utc_timestamp(
            value=entry.get("expires_at_utc"),
            field="expires_at_utc",
            artifact_path=str(path),
        )

        public_key_text = require_string(
            entry.get("public_key"), field="public_key", artifact_path=str(path)
        )
        public_key_bytes = _decode_base64_field(
            value=public_key_text,
            field="public_key",
            artifact_path=str(path),
        )

        records[key_id] = TrustAnchorKeyRecord(
            key_id=key_id,
            algorithm=algorithm,
            public_key=public_key_bytes,
            revoked=revoked,
            expires_at_utc=expires_at_utc,
        )
        ordered_key_ids.append(key_id)

    if ordered_key_ids != sorted(ordered_key_ids):
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="trust anchor registry key_id ordering must be lexicographic",
            details={"path": str(path), "key_ids": ordered_key_ids},
            artifact_path=str(path),
            policy_source="trust_anchor_registry",
        )

    return records


def _verify_with_openssl(
    *,
    algorithm: str,
    public_key_bytes: bytes,
    signature_bytes: bytes,
    message_bytes: bytes,
    artifact_path: str,
    signer_key_id: str,
) -> bool:
    if algorithm == "ed25519":
        if len(public_key_bytes) != 32:
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="ed25519 public_key must decode to exactly 32 bytes",
                details={"length": len(public_key_bytes)},
                artifact_path=artifact_path,
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="trust_anchor_registry",
            )
        if len(signature_bytes) != 64:
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="ed25519 signature must decode to exactly 64 bytes",
                details={"length": len(signature_bytes)},
                artifact_path=artifact_path,
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_envelope",
            )
        public_key_der = _ED25519_SPKI_DER_PREFIX + public_key_bytes
    elif algorithm == "p256":
        public_key_der = public_key_bytes
    else:
        raise fail(
            code=AHK4805_ALGORITHM_POLICY_VIOLATION,
            message="algorithm is outside frozen policy enum",
            details={"algorithm": algorithm},
            artifact_path=artifact_path,
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source="signature_envelope",
        )

    try:
        with tempfile.TemporaryDirectory(prefix="adeu_v48_sign_") as temp_dir:
            temp_root = Path(temp_dir)
            public_key_path = temp_root / "public_key.der"
            signature_path = temp_root / "signature.bin"
            message_path = temp_root / "message.bin"
            public_key_path.write_bytes(public_key_der)
            signature_path.write_bytes(signature_bytes)
            message_path.write_bytes(message_bytes)

            if algorithm == "ed25519":
                command = [
                    "openssl",
                    "pkeyutl",
                    "-verify",
                    "-pubin",
                    "-inkey",
                    str(public_key_path),
                    "-keyform",
                    "DER",
                    "-rawin",
                    "-in",
                    str(message_path),
                    "-sigfile",
                    str(signature_path),
                ]
            else:
                command = [
                    "openssl",
                    "dgst",
                    "-sha256",
                    "-verify",
                    str(public_key_path),
                    "-keyform",
                    "DER",
                    "-signature",
                    str(signature_path),
                    str(message_path),
                ]
            completed = subprocess.run(
                command,
                check=False,
                capture_output=True,
                text=False,
            )
    except FileNotFoundError as exc:
        raise fail(
            code=AHK4810_SIGNATURE_VERIFICATION_FAILED,
            message="openssl executable is required for signature verification",
            details={},
            artifact_path=artifact_path,
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source="signature_envelope",
        ) from exc

    return completed.returncode == 0


def verify_taskpack_signature(
    *,
    taskpack_dir: str,
    signature_envelope_path: str,
    trust_anchor_registry_path: str,
    verification_reference_time_utc: str,
    verification_output_root: str = DEFAULT_SIGNING_OUTPUT_ROOT,
    diagnostic_registry_path: str = DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    repo_root_path: str | Path | None = None,
) -> TaskpackSignatureVerificationResult:
    root = project_repo_root(
        anchor=Path(repo_root_path) if repo_root_path is not None else Path.cwd(),
    )

    manifest_hash: str | None = None
    bundle_hash: str | None = None
    signer_key_id: str = ""
    algorithm: str = ""
    registry_codes: set[str] | None = None

    try:
        require_deterministic_env_v48()
        _, registry_codes = load_diagnostic_registry(
            root=root,
            registry_rel_path=diagnostic_registry_path,
        )

        taskpack_dir_rel = normalize_relative_path(taskpack_dir)
        taskpack_path = safe_join(root, taskpack_dir_rel)
        manifest_hash = verify_taskpack_bundle(
            out_dir=taskpack_dir_rel,
            repo_root_path=root,
        )

        manifest_path = taskpack_path / "taskpack_manifest.json"
        manifest_payload = load_json_object(manifest_path)
        require_schema(
            manifest_payload,
            expected_schema=TASKPACK_MANIFEST_SCHEMA,
            path=manifest_path,
        )
        bundle_hash = _compute_taskpack_bundle_hash(
            manifest_payload=manifest_payload,
            artifact_path=str(manifest_path),
        )

        verification_reference_time = parse_reference_time_utc(
            verification_reference_time_utc,
            artifact_path="verification_reference_time_utc",
        )

        signature_envelope_artifact_path = coerce_artifact_path(root, signature_envelope_path)
        trust_anchor_registry_artifact_path = coerce_artifact_path(root, trust_anchor_registry_path)

        signature_envelope_payload = _load_signature_envelope(signature_envelope_artifact_path)
        trust_anchor_registry_records = _load_trust_anchor_registry(
            trust_anchor_registry_artifact_path
        )

        signer_key_id = signature_envelope_payload["signer_key_id"]
        algorithm = signature_envelope_payload["algorithm"]

        envelope_bundle_hash = signature_envelope_payload["taskpack_bundle_hash"]
        if envelope_bundle_hash != bundle_hash:
            raise fail(
                code=AHK4804_CROSS_ARTIFACT_HASH_MISMATCH,
                message=(
                    "signature envelope taskpack_bundle_hash mismatches "
                    "computed taskpack bundle hash"
                ),
                details={
                    "expected_taskpack_bundle_hash": bundle_hash,
                    "observed_taskpack_bundle_hash": envelope_bundle_hash,
                },
                artifact_path=str(signature_envelope_artifact_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_envelope",
            )

        envelope_manifest_hash = signature_envelope_payload["taskpack_manifest_hash"]
        if envelope_manifest_hash != manifest_hash:
            raise fail(
                code=AHK4804_CROSS_ARTIFACT_HASH_MISMATCH,
                message=(
                    "signature envelope taskpack_manifest_hash mismatches "
                    "computed taskpack manifest hash"
                ),
                details={
                    "expected_taskpack_manifest_hash": manifest_hash,
                    "observed_taskpack_manifest_hash": envelope_manifest_hash,
                },
                artifact_path=str(signature_envelope_artifact_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_envelope",
            )

        key_record = trust_anchor_registry_records.get(signer_key_id)
        if key_record is None:
            raise fail(
                code=AHK4803_ARTIFACT_INVALID,
                message="signer_key_id is not present in trust anchor registry",
                details={"signer_key_id": signer_key_id},
                artifact_path=str(trust_anchor_registry_artifact_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="trust_anchor_registry",
            )

        if key_record.algorithm != algorithm:
            raise fail(
                code=AHK4805_ALGORITHM_POLICY_VIOLATION,
                message="signer key algorithm does not match signature envelope algorithm",
                details={
                    "signer_key_id": signer_key_id,
                    "registry_algorithm": key_record.algorithm,
                    "envelope_algorithm": algorithm,
                },
                artifact_path=str(trust_anchor_registry_artifact_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="trust_anchor_registry",
            )

        if key_record.revoked:
            raise fail(
                code=AHK4806_KEY_LIFECYCLE_POLICY_VIOLATION,
                message="trust anchor key is revoked",
                details={"signer_key_id": signer_key_id},
                artifact_path=str(trust_anchor_registry_artifact_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="trust_anchor_registry",
            )

        if verification_reference_time >= key_record.expires_at_utc:
            raise fail(
                code=AHK4806_KEY_LIFECYCLE_POLICY_VIOLATION,
                message="trust anchor key is expired for verification reference time",
                details={
                    "signer_key_id": signer_key_id,
                    "verification_reference_time_utc": verification_reference_time_utc,
                    "expires_at_utc": key_record.expires_at_utc.strftime("%Y-%m-%dT%H:%M:%SZ"),
                },
                artifact_path=str(trust_anchor_registry_artifact_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="trust_anchor_registry",
            )

        signature_bytes = _decode_base64_field(
            value=signature_envelope_payload["signature"],
            field="signature",
            artifact_path=str(signature_envelope_artifact_path),
        )
        message_bytes = bundle_hash.encode("utf-8")

        verified = _verify_with_openssl(
            algorithm=algorithm,
            public_key_bytes=key_record.public_key,
            signature_bytes=signature_bytes,
            message_bytes=message_bytes,
            artifact_path=str(signature_envelope_artifact_path),
            signer_key_id=signer_key_id,
        )
        if not verified:
            raise fail(
                code=AHK4810_SIGNATURE_VERIFICATION_FAILED,
                message="signature cryptographic verification failed",
                details={"signer_key_id": signer_key_id, "algorithm": algorithm},
                artifact_path=str(signature_envelope_artifact_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_envelope",
            )

        signature_envelope_hash = sha256_canonical_json(signature_envelope_payload)
        trust_anchor_registry_hash = sha256_canonical_json(
            load_json_object(trust_anchor_registry_artifact_path)
        )

        preflight_invocation_binding_hash = _compute_preflight_invocation_binding_hash(
            manifest_hash=manifest_hash,
            bundle_hash=bundle_hash,
            signature_envelope_hash=signature_envelope_hash,
            trust_anchor_registry_hash=trust_anchor_registry_hash,
            verification_reference_time_utc=verification_reference_time_utc,
        )

        verification_payload = {
            "schema": SIGNATURE_VERIFICATION_RESULT_SCHEMA,
            "contract_schema": SIGNING_CONTRACT_SCHEMA,
            "taskpack_manifest_hash": manifest_hash,
            "taskpack_bundle_hash": bundle_hash,
            "signature_envelope_hash": signature_envelope_hash,
            "trust_anchor_registry_hash": trust_anchor_registry_hash,
            "verification_reference_time_utc": verification_reference_time_utc,
            "preflight_invocation_binding_hash": preflight_invocation_binding_hash,
            "signer_key_id": signer_key_id,
            "algorithm": algorithm,
            "verified": True,
            "verification_library": "openssl_cli",
        }

        if set(verification_payload.keys()) != _SIGNATURE_RESULT_REQUIRED_KEYS:
            raise fail(
                code=AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID,
                message="signature verification result keys must match frozen grammar",
                details={"keys": sorted(verification_payload.keys())},
                artifact_path="signature_verification_result",
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_verification_result",
            )

        verification_output_root_rel = normalize_relative_path(verification_output_root)
        output_root = safe_join(root, verification_output_root_rel)
        verification_result_path = output_root / f"{manifest_hash}_{bundle_hash}.json"
        write_json(verification_result_path, verification_payload)

        verification_result_loaded = load_json_object(verification_result_path)
        require_schema(
            verification_result_loaded,
            expected_schema=SIGNATURE_VERIFICATION_RESULT_SCHEMA,
            path=verification_result_path,
        )
        if set(verification_result_loaded.keys()) != _SIGNATURE_RESULT_REQUIRED_KEYS:
            raise fail(
                code=AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID,
                message="persisted signature verification result keys must match frozen grammar",
                details={
                    "path": str(verification_result_path),
                    "keys": sorted(verification_result_loaded.keys()),
                },
                artifact_path=str(verification_result_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_verification_result",
            )
        if verification_result_loaded.get("verified") is not True:
            raise fail(
                code=AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID,
                message="signature verification result verified must be true",
                details={"path": str(verification_result_path)},
                artifact_path=str(verification_result_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_verification_result",
            )

        verification_result_hash = sha256_canonical_json(verification_result_loaded)
        return TaskpackSignatureVerificationResult(
            verification_result_path=verification_result_path,
            verification_result_hash=verification_result_hash,
            rejection_diagnostic_path=None,
        )

    except TaskpackCompileError as exc:
        signing_error = fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="taskpack bundle verification failed before signature verification",
            details={"original_error": str(exc)},
            artifact_path=taskpack_dir,
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source="taskpack_manifest",
        )

    except TaskpackSigningError as exc:
        signing_error = exc

    issue = signing_error.issue or SigningIssue(
        issue_code=signing_error.code,
        reason=signing_error.message,
        artifact_path=signing_error.details.get("path", ""),
        signer_key_id=signer_key_id,
        algorithm=algorithm,
        policy_source="signature_envelope",
    )

    try:
        if registry_codes is None:
            _, registry_codes = load_diagnostic_registry(
                root=root,
                registry_rel_path=diagnostic_registry_path,
            )
        rejection_diagnostic_path = emit_rejection_diagnostic(
            root=root,
            output_root_rel=DEFAULT_REJECTIONS_ROOT,
            taskpack_manifest_hash=manifest_hash,
            taskpack_bundle_hash=bundle_hash,
            issues=[issue],
            allowed_codes=registry_codes,
        )
    except TaskpackSigningError as rejection_exc:
        raise TaskpackSigningError(
            code=AHK4811_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
            message="signature verification failure without rejection diagnostic emission",
            details={
                "original_error": str(signing_error),
                "rejection_error": str(rejection_exc),
            },
            issue=SigningIssue(
                issue_code=AHK4811_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
                reason="signature verification failure without rejection diagnostic emission",
                artifact_path=issue.artifact_path,
                signer_key_id=issue.signer_key_id,
                algorithm=issue.algorithm,
                policy_source="stop_gate_metrics",
            ),
        ) from signing_error

    details = dict(signing_error.details)
    details["rejection_diagnostic_path"] = rejection_diagnostic_path.as_posix()
    raise TaskpackSigningError(
        code=signing_error.code,
        message=signing_error.message,
        details=details,
        issue=issue,
    ) from signing_error


def validate_signature_verification_result_for_downstream(
    *,
    signature_verification_result_path: str,
    taskpack_manifest_hash: str,
    taskpack_bundle_hash: str,
    signature_envelope_hash: str,
    trust_anchor_registry_hash: str,
    verification_reference_time_utc: str,
    signer_key_id: str,
    algorithm: str,
    repo_root_path: str | Path | None = None,
) -> dict[str, Any]:
    root = project_repo_root(
        anchor=Path(repo_root_path) if repo_root_path is not None else Path.cwd(),
    )
    result_path = coerce_artifact_path(root, signature_verification_result_path)
    payload = load_json_object(result_path)
    require_schema(payload, expected_schema=SIGNATURE_VERIFICATION_RESULT_SCHEMA, path=result_path)

    keys = set(payload.keys())
    if keys != _SIGNATURE_RESULT_REQUIRED_KEYS:
        raise fail(
            code=AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID,
            message="signature verification result keys must match frozen grammar",
            details={"path": str(result_path), "keys": sorted(keys)},
            artifact_path=str(result_path),
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source="signature_verification_result",
        )

    forbidden_observed = sorted(keys.intersection(_NONDETERMINISTIC_RESULT_FIELDS))
    if forbidden_observed:
        raise fail(
            code=AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID,
            message="signature verification result contains forbidden non-deterministic fields",
            details={"path": str(result_path), "fields": forbidden_observed},
            artifact_path=str(result_path),
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source="signature_verification_result",
        )

    if payload.get("verified") is not True:
        raise fail(
            code=AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID,
            message="signature verification result verified must be true for downstream execution",
            details={"path": str(result_path), "verified": payload.get("verified")},
            artifact_path=str(result_path),
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source="signature_verification_result",
        )

    expected_fixed_fields: dict[str, str] = {
        "contract_schema": SIGNING_CONTRACT_SCHEMA,
        "verification_library": "openssl_cli",
    }
    for field, expected in expected_fixed_fields.items():
        observed = payload.get(field)
        if observed != expected:
            raise fail(
                code=AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID,
                message="signature verification result fixed contract field mismatch",
                details={
                    "path": str(result_path),
                    "field": field,
                    "expected": expected,
                    "observed": observed,
                },
                artifact_path=str(result_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_verification_result",
            )

    expected_bindings: dict[str, Any] = {
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "taskpack_bundle_hash": taskpack_bundle_hash,
        "signature_envelope_hash": signature_envelope_hash,
        "trust_anchor_registry_hash": trust_anchor_registry_hash,
        "verification_reference_time_utc": verification_reference_time_utc,
        "signer_key_id": signer_key_id,
        "algorithm": algorithm,
    }
    for field, expected in expected_bindings.items():
        observed = payload.get(field)
        if observed != expected:
            raise fail(
                code=AHK4804_CROSS_ARTIFACT_HASH_MISMATCH,
                message="signature verification result binding mismatch",
                details={
                    "path": str(result_path),
                    "field": field,
                    "expected": expected,
                    "observed": observed,
                },
                artifact_path=str(result_path),
                signer_key_id=signer_key_id,
                algorithm=algorithm,
                policy_source="signature_verification_result",
            )

    expected_preflight_hash = _compute_preflight_invocation_binding_hash(
        manifest_hash=taskpack_manifest_hash,
        bundle_hash=taskpack_bundle_hash,
        signature_envelope_hash=signature_envelope_hash,
        trust_anchor_registry_hash=trust_anchor_registry_hash,
        verification_reference_time_utc=verification_reference_time_utc,
    )
    if payload.get("preflight_invocation_binding_hash") != expected_preflight_hash:
        raise fail(
            code=AHK4804_CROSS_ARTIFACT_HASH_MISMATCH,
            message="signature verification result preflight invocation binding mismatch",
            details={
                "path": str(result_path),
                "expected_preflight_invocation_binding_hash": expected_preflight_hash,
                "observed_preflight_invocation_binding_hash": payload.get(
                    "preflight_invocation_binding_hash"
                ),
            },
            artifact_path=str(result_path),
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source="signature_verification_result",
        )

    return payload


def load_validated_downstream_signature_handoff(
    *,
    taskpack_dir: str | Path,
    signature_verification_result_path: str | Path,
    signature_envelope_path: str | Path,
    trust_anchor_registry_path: str | Path,
    verification_reference_time_utc: str,
    repo_root_path: str | Path | None = None,
) -> ValidatedDownstreamSignatureHandoff:
    root = project_repo_root(
        anchor=Path(repo_root_path) if repo_root_path is not None else Path.cwd(),
    )
    taskpack_rel = normalize_relative_path(str(taskpack_dir))
    taskpack_snapshot = load_verified_taskpack_snapshot(out_dir=taskpack_rel, repo_root_path=root)

    verification_reference_time_text = require_string(
        verification_reference_time_utc,
        field="verification_reference_time_utc",
        artifact_path=str(taskpack_snapshot.manifest_path),
    )
    parse_reference_time_utc(
        verification_reference_time_text,
        artifact_path=str(taskpack_snapshot.manifest_path),
    )

    signature_envelope_rel = normalize_relative_path(str(signature_envelope_path))
    signature_envelope_artifact = coerce_artifact_path(root, signature_envelope_rel)
    signature_envelope_payload = _load_signature_envelope(signature_envelope_artifact)
    signature_envelope_hash = sha256_canonical_json(signature_envelope_payload)

    trust_anchor_registry_rel = normalize_relative_path(str(trust_anchor_registry_path))
    trust_anchor_registry_artifact = coerce_artifact_path(root, trust_anchor_registry_rel)
    trust_anchor_registry_payload = load_json_object(trust_anchor_registry_artifact)
    require_schema(
        trust_anchor_registry_payload,
        expected_schema=TRUST_ANCHOR_REGISTRY_SCHEMA,
        path=trust_anchor_registry_artifact,
    )
    _load_trust_anchor_registry(trust_anchor_registry_artifact)
    trust_anchor_registry_hash = sha256_canonical_json(trust_anchor_registry_payload)

    signer_key_id = require_string(
        signature_envelope_payload.get("signer_key_id"),
        field="signer_key_id",
        artifact_path=str(signature_envelope_artifact),
    )
    algorithm = require_string(
        signature_envelope_payload.get("algorithm"),
        field="algorithm",
        artifact_path=str(signature_envelope_artifact),
    )
    result_payload = validate_signature_verification_result_for_downstream(
        signature_verification_result_path=str(signature_verification_result_path),
        taskpack_manifest_hash=taskpack_snapshot.manifest_hash,
        taskpack_bundle_hash=taskpack_snapshot.bundle_hash,
        signature_envelope_hash=signature_envelope_hash,
        trust_anchor_registry_hash=trust_anchor_registry_hash,
        verification_reference_time_utc=verification_reference_time_text,
        signer_key_id=signer_key_id,
        algorithm=algorithm,
        repo_root_path=root,
    )
    result_path = coerce_artifact_path(root, str(signature_verification_result_path))
    return ValidatedDownstreamSignatureHandoff(
        taskpack_snapshot=taskpack_snapshot,
        signature_verification_result_path=result_path,
        signature_verification_result_payload=result_payload,
        signature_envelope_path=signature_envelope_artifact,
        signature_envelope_payload=signature_envelope_payload,
        signature_envelope_hash=signature_envelope_hash,
        trust_anchor_registry_path=trust_anchor_registry_artifact,
        trust_anchor_registry_hash=trust_anchor_registry_hash,
        verification_reference_time_utc=verification_reference_time_text,
        signer_key_id=signer_key_id,
        algorithm=algorithm,
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Verify deterministic v48 taskpack signature envelope and trust-anchor "
            "registry bindings before downstream harness execution."
        ),
    )
    parser.add_argument(
        "--taskpack-dir",
        required=True,
        help="Repo-relative taskpack directory containing taskpack_manifest.json and components.",
    )
    parser.add_argument(
        "--signature-envelope",
        required=True,
        help="Repo-relative path to taskpack_signature_envelope@1 JSON artifact.",
    )
    parser.add_argument(
        "--trust-anchor-registry",
        required=True,
        help="Repo-relative path to taskpack_trust_anchor_registry@1 JSON artifact.",
    )
    parser.add_argument(
        "--verification-reference-time-utc",
        required=True,
        help="Explicit RFC3339 UTC Z reference time used for lifecycle checks.",
    )
    parser.add_argument(
        "--verification-output-root",
        default=DEFAULT_SIGNING_OUTPUT_ROOT,
        help="Repo-relative output root for signature_verification_result@1 artifact.",
    )
    parser.add_argument(
        "--diagnostic-registry",
        default=DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
        help="Repo-relative path to authoritative v48 signing diagnostic registry JSON.",
    )
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Optional repository root override. Defaults to deterministic repo_root(anchor=cwd).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = verify_taskpack_signature(
            taskpack_dir=args.taskpack_dir,
            signature_envelope_path=args.signature_envelope,
            trust_anchor_registry_path=args.trust_anchor_registry,
            verification_reference_time_utc=args.verification_reference_time_utc,
            verification_output_root=args.verification_output_root,
            diagnostic_registry_path=args.diagnostic_registry,
            repo_root_path=args.repo_root,
        )
    except TaskpackSigningError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": SIGNATURE_VERIFIER_RESULT_SCHEMA,
        "verification_result_path": result.verification_result_path.as_posix(),
        "verification_result_hash": result.verification_result_hash,
        "rejection_diagnostic_path": (
            result.rejection_diagnostic_path.as_posix()
            if result.rejection_diagnostic_path is not None
            else None
        ),
    }
    sys.stdout.write(canonical_json(payload) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
