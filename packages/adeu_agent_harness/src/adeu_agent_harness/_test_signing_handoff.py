from __future__ import annotations

import base64
from dataclasses import dataclass
from pathlib import Path

from urm_runtime.hashing import canonical_json, sha256_canonical_json

from .compile import load_verified_taskpack_snapshot
from .verify_taskpack_signature import (
    SIGNATURE_VERIFICATION_RESULT_SCHEMA,
    SIGNING_CONTRACT_SCHEMA,
    _compute_preflight_invocation_binding_hash,
)

_DEFAULT_REFERENCE_TIME_UTC = "2026-03-05T00:00:00Z"


@dataclass(frozen=True)
class SigningHandoffFixture:
    signature_verification_result_path: str
    signature_envelope_path: str
    trust_anchor_registry_path: str
    verification_reference_time_utc: str

    def as_kwargs(self) -> dict[str, str]:
        return {
            "signature_verification_result_path": self.signature_verification_result_path,
            "signature_envelope_path": self.signature_envelope_path,
            "trust_anchor_registry_path": self.trust_anchor_registry_path,
            "verification_reference_time_utc": self.verification_reference_time_utc,
        }


def _relative(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def seed_signing_handoff_fixture(
    root: Path,
    *,
    taskpack_dir: Path | str,
    verification_reference_time_utc: str = _DEFAULT_REFERENCE_TIME_UTC,
) -> SigningHandoffFixture:
    taskpack_rel = (
        _relative(root, taskpack_dir)
        if isinstance(taskpack_dir, Path) and taskpack_dir.is_absolute()
        else str(taskpack_dir)
    )
    snapshot = load_verified_taskpack_snapshot(out_dir=taskpack_rel, repo_root_path=root)

    signing_root = root / "artifacts" / "agent_harness" / "v49" / "test_signing"
    envelope_path = signing_root / "taskpack_signature_envelope.json"
    registry_path = signing_root / "taskpack_trust_anchor_registry.json"
    result_path = signing_root / "signature_verification_result.json"

    envelope_payload = {
        "schema": "taskpack_signature_envelope@1",
        "signer_key_id": "key_ed25519_test",
        "algorithm": "ed25519",
        "taskpack_bundle_hash": snapshot.bundle_hash,
        "taskpack_manifest_hash": snapshot.manifest_hash,
        "signature": base64.b64encode(b"\x00" * 64).decode("ascii"),
    }
    registry_payload = {
        "schema": "taskpack_trust_anchor_registry@1",
        "keys": [
            {
                "key_id": "key_ed25519_test",
                "algorithm": "ed25519",
                "public_key": base64.b64encode(b"\x11" * 32).decode("ascii"),
                "revoked": False,
                "expires_at_utc": "2026-12-31T00:00:00Z",
            }
        ],
    }
    _write_json(envelope_path, envelope_payload)
    _write_json(registry_path, registry_payload)

    signature_envelope_hash = sha256_canonical_json(envelope_payload)
    trust_anchor_registry_hash = sha256_canonical_json(registry_payload)
    result_payload = {
        "schema": SIGNATURE_VERIFICATION_RESULT_SCHEMA,
        "contract_schema": SIGNING_CONTRACT_SCHEMA,
        "taskpack_manifest_hash": snapshot.manifest_hash,
        "taskpack_bundle_hash": snapshot.bundle_hash,
        "signature_envelope_hash": signature_envelope_hash,
        "trust_anchor_registry_hash": trust_anchor_registry_hash,
        "verification_reference_time_utc": verification_reference_time_utc,
        "preflight_invocation_binding_hash": _compute_preflight_invocation_binding_hash(
            manifest_hash=snapshot.manifest_hash,
            bundle_hash=snapshot.bundle_hash,
            signature_envelope_hash=signature_envelope_hash,
            trust_anchor_registry_hash=trust_anchor_registry_hash,
            verification_reference_time_utc=verification_reference_time_utc,
        ),
        "signer_key_id": "key_ed25519_test",
        "algorithm": "ed25519",
        "verified": True,
        "verification_library": "openssl_cli",
    }
    _write_json(result_path, result_payload)

    return SigningHandoffFixture(
        signature_verification_result_path=_relative(root, result_path),
        signature_envelope_path=_relative(root, envelope_path),
        trust_anchor_registry_path=_relative(root, registry_path),
        verification_reference_time_utc=verification_reference_time_utc,
    )
