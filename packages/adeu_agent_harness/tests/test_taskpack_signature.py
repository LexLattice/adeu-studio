from __future__ import annotations

import base64
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest
from adeu_agent_harness._v48_signing_common import (
    AHK4802_SCHEMA_MISMATCH,
    AHK4803_ARTIFACT_INVALID,
    AHK4804_CROSS_ARTIFACT_HASH_MISMATCH,
    AHK4805_ALGORITHM_POLICY_VIOLATION,
    AHK4806_KEY_LIFECYCLE_POLICY_VIOLATION,
    AHK4808_CONTRACT_REGISTRY_INVALID,
    load_diagnostic_registry,
)
from adeu_agent_harness.compile import (
    PIPELINE_PROFILE_SCHEMA,
    TASKPACK_PROFILE_REGISTRY_SCHEMA,
    compile_taskpack,
)
from adeu_agent_harness.verify_taskpack_signature import (
    SIGNATURE_VERIFICATION_RESULT_SCHEMA,
    TRUST_ANCHOR_REGISTRY_SCHEMA,
    TaskpackSigningError,
    validate_signature_verification_result_for_downstream,
    verify_taskpack_signature,
)
from urm_runtime.hashing import canonical_json, sha256_canonical_json

_OUT_DIR = "artifacts/agent_harness/v48/taskpacks/v41/v48_default"
_DIAGNOSTIC_REGISTRY_REL = (
    "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v48.json"
)

_ED25519_SPKI_DER_PREFIX = bytes.fromhex("302a300506032b6570032100")


@pytest.fixture(scope="module", autouse=True)
def _require_openssl() -> None:
    if shutil.which("openssl") is None:
        pytest.skip("openssl is required for v48 signing tests")


@pytest.fixture(autouse=True)
def _enforce_deterministic_env(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TZ", "UTC")
    monkeypatch.setenv("LC_ALL", "C")
    monkeypatch.setenv("PYTHONHASHSEED", "0")


def _run(*args: str, cwd: Path) -> None:
    subprocess.run(args, check=True, cwd=cwd, capture_output=True, text=True)


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    _write(path, canonical_json(payload) + "\n")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _relative(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def _base_repo(tmp_path: Path) -> Path:
    root = tmp_path
    _write(root / "pyproject.toml", "[tool.ruff]\nline-length = 100\n")
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    return root


def _seed_semantic_authority_artifacts(root: Path) -> None:
    _write_json(
        root / "artifacts" / "semantic_compiler" / "v41" / "evidence_manifest.json",
        {
            "schema": "semantic_compiler_evidence_manifest@0.1",
            "arc": "vnext_plus41",
            "compiler_entrypoint": "python -m adeu_semantic_compiler.compile",
            "source_set_hash": "0" * 64,
            "required_evidence": [],
            "artifacts": {
                "surface_snapshot": "artifacts/semantic_compiler/v41/surface_snapshot.json",
                "surface_diff": "artifacts/semantic_compiler/v41/surface_diff.json",
                "evidence_manifest": "artifacts/semantic_compiler/v41/evidence_manifest.json",
            },
            "artifact_hashes": {
                "surface_snapshot": "1" * 64,
                "surface_diff": "2" * 64,
            },
        },
    )
    _write_json(
        root / "artifacts" / "semantic_compiler" / "v41" / "surface_diff.json",
        {
            "schema": "semantic_compiler_surface_diff@0.1",
            "baseline_present": True,
            "delta_eval_mode": "exact_set",
            "adds": [],
            "removes": [],
            "changes": [],
        },
    )
    _write_json(
        root / "artifacts" / "semantic_compiler" / "v40" / "commitments_ir.json",
        {
            "schema": "adeu_commitments_ir@0.1",
            "modules": [],
            "locks": [],
        },
    )


def _seed_profile_and_registry(root: Path) -> Path:
    profile_payload = {
        "schema": PIPELINE_PROFILE_SCHEMA,
        "profile_id": "v48_default",
        "task_scope_title": "V48 X1 Signing Preflight",
        "task_scope_summary": "Compile deterministic taskpack for signing preflight tests.",
        "compiled_commitments_ir_path": "artifacts/semantic_compiler/v40/commitments_ir.json",
        "acceptance_criteria": [
            "Signature preflight consumes canonical taskpack manifest.",
        ],
        "allowlist_paths": [
            "packages/adeu_agent_harness/src/adeu_agent_harness",
            "packages/adeu_agent_harness/tests",
            "artifacts/stop_gate",
        ],
        "forbidden_paths": ["apps/api"],
        "forbidden_effects": ["network_calls"],
        "commands": [
            {
                "command_id": "noop",
                "run": "true",
                "working_directory_or_repo_root": "repo_root",
                "env_overrides": {},
            }
        ],
        "evidence_slots": [
            {
                "slot_id": "runtime_observability_comparison",
                "description": "Runtime observability comparison row.",
                "required": True,
            }
        ],
    }
    profile_path = root / "artifacts" / "agent_harness" / "v48" / "profiles" / "v48_default.json"
    _write_json(profile_path, profile_payload)

    registry_path = root / "artifacts" / "agent_harness" / "v48" / "taskpack_profile_registry.json"
    _write_json(
        registry_path,
        {
            "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
            "profiles": [
                {
                    "profile_id": "v48_default",
                    "profile_sha256": sha256_canonical_json(profile_payload),
                    "profile_payload_path": "artifacts/agent_harness/v48/profiles/v48_default.json",
                }
            ],
        },
    )
    return registry_path


def _compile_taskpack(root: Path, *, registry_path: Path) -> Path:
    result = compile_taskpack(
        profile_registry_path=_relative(root, registry_path),
        profile_id="v48_default",
        source_semantic_arc="v41",
        out_dir=_OUT_DIR,
        repo_root_path=root,
    )
    return result.out_dir


def _seed_diagnostic_registry(root: Path) -> str:
    path = root / _DIAGNOSTIC_REGISTRY_REL
    _write_json(
        path,
        {
            "schema": "taskpack_signing_diagnostic_registry@1",
            "codes": [
                {
                    "issue_code": f"AHK48{index:02d}",
                    "title": f"V48_{index:02d}",
                    "description": "v48 signing diagnostic code",
                }
                for index in range(12)
            ],
        },
    )
    return _DIAGNOSTIC_REGISTRY_REL


def _compute_taskpack_hashes(taskpack_dir: Path) -> tuple[str, str]:
    manifest = _read_json(taskpack_dir / "taskpack_manifest.json")
    manifest_hash = sha256_canonical_json(manifest)
    subject = sorted(
        (
            {
                "path": entry["relative_path"],
                "sha256": entry["sha256"],
            }
            for entry in manifest["components"]
        ),
        key=lambda row: row["path"],
    )
    bundle_hash = sha256_canonical_json(subject)
    return manifest_hash, bundle_hash


def _seed_ed25519_material(
    root: Path,
    *,
    manifest_hash: str,
    bundle_hash: str,
) -> tuple[str, str]:
    material_dir = root / "artifacts" / "agent_harness" / "v48" / "signing_material"
    material_dir.mkdir(parents=True, exist_ok=True)

    private_key_path = material_dir / "ed25519_private.pem"
    public_key_der_path = material_dir / "ed25519_public.der"
    message_path = material_dir / "message.bin"
    signature_path = material_dir / "signature.bin"

    _run("openssl", "genpkey", "-algorithm", "ed25519", "-out", str(private_key_path), cwd=root)
    _run(
        "openssl",
        "pkey",
        "-in",
        str(private_key_path),
        "-pubout",
        "-outform",
        "DER",
        "-out",
        str(public_key_der_path),
        cwd=root,
    )

    public_der = public_key_der_path.read_bytes()
    assert public_der.startswith(_ED25519_SPKI_DER_PREFIX)
    public_raw = public_der[len(_ED25519_SPKI_DER_PREFIX) :]
    assert len(public_raw) == 32

    message_path.write_bytes(bundle_hash.encode("utf-8"))
    _run(
        "openssl",
        "pkeyutl",
        "-sign",
        "-inkey",
        str(private_key_path),
        "-rawin",
        "-in",
        str(message_path),
        "-out",
        str(signature_path),
        cwd=root,
    )

    envelope_path = root / "artifacts" / "agent_harness" / "v48" / "signature_envelope.json"
    registry_path = root / "artifacts" / "agent_harness" / "v48" / "trust_anchor_registry.json"

    _write_json(
        envelope_path,
        {
            "schema": "taskpack_signature_envelope@1",
            "signer_key_id": "key_ed25519_default",
            "algorithm": "ed25519",
            "taskpack_bundle_hash": bundle_hash,
            "taskpack_manifest_hash": manifest_hash,
            "signature": base64.b64encode(signature_path.read_bytes()).decode("ascii"),
        },
    )
    _write_json(
        registry_path,
        {
            "schema": TRUST_ANCHOR_REGISTRY_SCHEMA,
            "keys": [
                {
                    "key_id": "key_ed25519_default",
                    "algorithm": "ed25519",
                    "public_key": base64.b64encode(public_raw).decode("ascii"),
                    "revoked": False,
                    "expires_at_utc": "2030-01-01T00:00:00Z",
                }
            ],
        },
    )
    return _relative(root, envelope_path), _relative(root, registry_path)


def _seed_p256_material(
    root: Path,
    *,
    manifest_hash: str,
    bundle_hash: str,
) -> tuple[str, str]:
    material_dir = root / "artifacts" / "agent_harness" / "v48" / "signing_material"
    material_dir.mkdir(parents=True, exist_ok=True)

    private_key_path = material_dir / "p256_private.pem"
    public_key_der_path = material_dir / "p256_public.der"
    message_path = material_dir / "message.bin"
    signature_path = material_dir / "signature.bin"

    _run(
        "openssl",
        "ecparam",
        "-name",
        "prime256v1",
        "-genkey",
        "-noout",
        "-out",
        str(private_key_path),
        cwd=root,
    )
    _run(
        "openssl",
        "pkey",
        "-in",
        str(private_key_path),
        "-pubout",
        "-outform",
        "DER",
        "-out",
        str(public_key_der_path),
        cwd=root,
    )

    message_path.write_bytes(bundle_hash.encode("utf-8"))
    _run(
        "openssl",
        "dgst",
        "-sha256",
        "-sign",
        str(private_key_path),
        "-out",
        str(signature_path),
        str(message_path),
        cwd=root,
    )

    envelope_path = root / "artifacts" / "agent_harness" / "v48" / "signature_envelope.json"
    registry_path = root / "artifacts" / "agent_harness" / "v48" / "trust_anchor_registry.json"

    _write_json(
        envelope_path,
        {
            "schema": "taskpack_signature_envelope@1",
            "signer_key_id": "key_p256_default",
            "algorithm": "p256",
            "taskpack_bundle_hash": bundle_hash,
            "taskpack_manifest_hash": manifest_hash,
            "signature": base64.b64encode(signature_path.read_bytes()).decode("ascii"),
        },
    )
    _write_json(
        registry_path,
        {
            "schema": TRUST_ANCHOR_REGISTRY_SCHEMA,
            "keys": [
                {
                    "key_id": "key_p256_default",
                    "algorithm": "p256",
                    "public_key": (
                        base64.b64encode(public_key_der_path.read_bytes()).decode("ascii")
                    ),
                    "revoked": False,
                    "expires_at_utc": "2030-01-01T00:00:00Z",
                }
            ],
        },
    )
    return _relative(root, envelope_path), _relative(root, registry_path)


def _setup_repo(tmp_path: Path) -> tuple[Path, str, str]:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    _seed_diagnostic_registry(root)
    return root, _relative(root, taskpack_dir), _DIAGNOSTIC_REGISTRY_REL


def _error_payload(exc: TaskpackSigningError) -> dict[str, Any]:
    payload = json.loads(str(exc))
    assert payload["schema"] == "taskpack_signing_error@1"
    return payload


def _assert_stop_gate_keyset_equal(*, baseline_path: Path, candidate_path: Path) -> None:
    baseline_payload = _read_json(baseline_path)
    candidate_payload = _read_json(candidate_path)
    baseline_metrics = baseline_payload.get("metrics")
    candidate_metrics = candidate_payload.get("metrics")
    assert isinstance(baseline_metrics, dict)
    assert isinstance(candidate_metrics, dict)
    assert set(candidate_metrics.keys()) == set(baseline_metrics.keys())


def _assert_stop_gate_cardinality_80(*, metrics_path: Path) -> None:
    metrics_payload = _read_json(metrics_path)
    metrics = metrics_payload.get("metrics")
    assert isinstance(metrics, dict)
    assert len(set(metrics.keys())) == 80


def test_verify_taskpack_signature_ed25519_success(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    result = verify_taskpack_signature(
        taskpack_dir=taskpack_dir_rel,
        signature_envelope_path=envelope_rel,
        trust_anchor_registry_path=trust_registry_rel,
        verification_reference_time_utc="2026-03-05T00:00:00Z",
        verification_output_root="artifacts/agent_harness/v48/signing",
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
    )

    payload = _read_json(result.verification_result_path)
    assert payload["schema"] == SIGNATURE_VERIFICATION_RESULT_SCHEMA
    assert payload["verified"] is True
    assert payload["algorithm"] == "ed25519"
    assert payload["taskpack_bundle_hash"] == bundle_hash


def test_verify_taskpack_signature_p256_success(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_p256_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    result = verify_taskpack_signature(
        taskpack_dir=taskpack_dir_rel,
        signature_envelope_path=envelope_rel,
        trust_anchor_registry_path=trust_registry_rel,
        verification_reference_time_utc="2026-03-05T00:00:00Z",
        verification_output_root="artifacts/agent_harness/v48/signing",
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
    )

    payload = _read_json(result.verification_result_path)
    assert payload["schema"] == SIGNATURE_VERIFICATION_RESULT_SCHEMA
    assert payload["verified"] is True
    assert payload["algorithm"] == "p256"


def test_verify_taskpack_signature_bundle_hash_mismatch_emits_rejection(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    envelope_path = root / envelope_rel
    envelope_payload = _read_json(envelope_path)
    envelope_payload["taskpack_bundle_hash"] = "0" * 64
    _write_json(envelope_path, envelope_payload)

    with pytest.raises(TaskpackSigningError) as exc_info:
        verify_taskpack_signature(
            taskpack_dir=taskpack_dir_rel,
            signature_envelope_path=envelope_rel,
            trust_anchor_registry_path=trust_registry_rel,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            verification_output_root="artifacts/agent_harness/v48/signing",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4804_CROSS_ARTIFACT_HASH_MISMATCH
    rejection_path = root / payload["details"]["rejection_diagnostic_path"]
    assert rejection_path.is_file()
    rejection_payload = _read_json(rejection_path)
    assert rejection_payload["schema"] == "v34a_signing_rejection_diagnostic@1"
    assert rejection_payload["issues"][0]["issue_code"] == AHK4804_CROSS_ARTIFACT_HASH_MISMATCH


def test_verify_taskpack_signature_revoked_key_fails_closed(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    trust_registry_path = root / trust_registry_rel
    trust_registry_payload = _read_json(trust_registry_path)
    trust_registry_payload["keys"][0]["revoked"] = True
    _write_json(trust_registry_path, trust_registry_payload)

    with pytest.raises(TaskpackSigningError) as exc_info:
        verify_taskpack_signature(
            taskpack_dir=taskpack_dir_rel,
            signature_envelope_path=envelope_rel,
            trust_anchor_registry_path=trust_registry_rel,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            verification_output_root="artifacts/agent_harness/v48/signing",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4806_KEY_LIFECYCLE_POLICY_VIOLATION
    rejection_path = root / payload["details"]["rejection_diagnostic_path"]
    assert rejection_path.is_file()


def test_signature_envelope_requires_single_signature(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    envelope_path = root / envelope_rel
    envelope_payload = _read_json(envelope_path)
    envelope_payload["signatures"] = [envelope_payload["signature"]]
    _write_json(envelope_path, envelope_payload)

    with pytest.raises(TaskpackSigningError) as exc_info:
        verify_taskpack_signature(
            taskpack_dir=taskpack_dir_rel,
            signature_envelope_path=envelope_rel,
            trust_anchor_registry_path=trust_registry_rel,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            verification_output_root="artifacts/agent_harness/v48/signing",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4803_ARTIFACT_INVALID


def test_signature_manifest_hash_redundant_binding_must_match(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    envelope_path = root / envelope_rel
    envelope_payload = _read_json(envelope_path)
    envelope_payload["taskpack_manifest_hash"] = "f" * 64
    _write_json(envelope_path, envelope_payload)

    with pytest.raises(TaskpackSigningError) as exc_info:
        verify_taskpack_signature(
            taskpack_dir=taskpack_dir_rel,
            signature_envelope_path=envelope_rel,
            trust_anchor_registry_path=trust_registry_rel,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            verification_output_root="artifacts/agent_harness/v48/signing",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4804_CROSS_ARTIFACT_HASH_MISMATCH


def test_algorithm_key_binding_mismatch_fails_closed(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    trust_registry_path = root / trust_registry_rel
    trust_registry_payload = _read_json(trust_registry_path)
    trust_registry_payload["keys"][0]["algorithm"] = "p256"
    _write_json(trust_registry_path, trust_registry_payload)

    with pytest.raises(TaskpackSigningError) as exc_info:
        verify_taskpack_signature(
            taskpack_dir=taskpack_dir_rel,
            signature_envelope_path=envelope_rel,
            trust_anchor_registry_path=trust_registry_rel,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            verification_output_root="artifacts/agent_harness/v48/signing",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4805_ALGORITHM_POLICY_VIOLATION


def test_unknown_signer_key_id_fails_closed(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    envelope_path = root / envelope_rel
    envelope_payload = _read_json(envelope_path)
    envelope_payload["signer_key_id"] = "key_missing"
    _write_json(envelope_path, envelope_payload)

    with pytest.raises(TaskpackSigningError) as exc_info:
        verify_taskpack_signature(
            taskpack_dir=taskpack_dir_rel,
            signature_envelope_path=envelope_rel,
            trust_anchor_registry_path=trust_registry_rel,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            verification_output_root="artifacts/agent_harness/v48/signing",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4803_ARTIFACT_INVALID


def test_expired_signer_key_fails_closed_with_explicit_verification_time(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    trust_registry_path = root / trust_registry_rel
    trust_registry_payload = _read_json(trust_registry_path)
    trust_registry_payload["keys"][0]["expires_at_utc"] = "2026-03-05T00:00:00Z"
    _write_json(trust_registry_path, trust_registry_payload)

    with pytest.raises(TaskpackSigningError) as exc_info:
        verify_taskpack_signature(
            taskpack_dir=taskpack_dir_rel,
            signature_envelope_path=envelope_rel,
            trust_anchor_registry_path=trust_registry_rel,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            verification_output_root="artifacts/agent_harness/v48/signing",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4806_KEY_LIFECYCLE_POLICY_VIOLATION


def test_signature_verification_result_schema_required_for_downstream(tmp_path: Path) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    result = verify_taskpack_signature(
        taskpack_dir=taskpack_dir_rel,
        signature_envelope_path=envelope_rel,
        trust_anchor_registry_path=trust_registry_rel,
        verification_reference_time_utc="2026-03-05T00:00:00Z",
        verification_output_root="artifacts/agent_harness/v48/signing",
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
    )

    result_path = result.verification_result_path
    result_payload = _read_json(result_path)
    result_payload["schema"] = "wrong_schema@1"
    _write_json(result_path, result_payload)

    signature_envelope_hash = sha256_canonical_json(_read_json(root / envelope_rel))
    trust_anchor_registry_hash = sha256_canonical_json(_read_json(root / trust_registry_rel))

    with pytest.raises(TaskpackSigningError) as exc_info:
        validate_signature_verification_result_for_downstream(
            signature_verification_result_path=_relative(root, result_path),
            taskpack_manifest_hash=manifest_hash,
            taskpack_bundle_hash=bundle_hash,
            signature_envelope_hash=signature_envelope_hash,
            trust_anchor_registry_hash=trust_anchor_registry_hash,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            signer_key_id="key_ed25519_default",
            algorithm="ed25519",
            repo_root_path=root,
        )
    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4802_SCHEMA_MISMATCH


def test_signature_verification_result_source_binding_rejects_unbound_artifact(
    tmp_path: Path,
) -> None:
    root, taskpack_dir_rel, diagnostic_registry_rel = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    result = verify_taskpack_signature(
        taskpack_dir=taskpack_dir_rel,
        signature_envelope_path=envelope_rel,
        trust_anchor_registry_path=trust_registry_rel,
        verification_reference_time_utc="2026-03-05T00:00:00Z",
        verification_output_root="artifacts/agent_harness/v48/signing",
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
    )
    result_path = result.verification_result_path
    result_payload = _read_json(result_path)
    result_payload["preflight_invocation_binding_hash"] = "0" * 64
    _write_json(result_path, result_payload)

    signature_envelope_hash = sha256_canonical_json(_read_json(root / envelope_rel))
    trust_anchor_registry_hash = sha256_canonical_json(_read_json(root / trust_registry_rel))

    with pytest.raises(TaskpackSigningError) as exc_info:
        validate_signature_verification_result_for_downstream(
            signature_verification_result_path=_relative(root, result_path),
            taskpack_manifest_hash=manifest_hash,
            taskpack_bundle_hash=bundle_hash,
            signature_envelope_hash=signature_envelope_hash,
            trust_anchor_registry_hash=trust_anchor_registry_hash,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            signer_key_id="key_ed25519_default",
            algorithm="ed25519",
            repo_root_path=root,
        )
    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4804_CROSS_ARTIFACT_HASH_MISMATCH


def test_preflight_signature_verification_is_required_before_runner(tmp_path: Path) -> None:
    root, _, _ = _setup_repo(tmp_path)
    with pytest.raises(TaskpackSigningError) as exc_info:
        validate_signature_verification_result_for_downstream(
            signature_verification_result_path="artifacts/agent_harness/v48/signing/missing.json",
            taskpack_manifest_hash="0" * 64,
            taskpack_bundle_hash="1" * 64,
            signature_envelope_hash="2" * 64,
            trust_anchor_registry_hash="3" * 64,
            verification_reference_time_utc="2026-03-05T00:00:00Z",
            signer_key_id="missing",
            algorithm="ed25519",
            repo_root_path=root,
        )
    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4800"


def test_signing_diagnostics_enforce_ahk48_registry(tmp_path: Path) -> None:
    root, _, _ = _setup_repo(tmp_path)
    invalid_registry = root / _DIAGNOSTIC_REGISTRY_REL
    payload = _read_json(invalid_registry)
    payload["codes"][0]["issue_code"] = "AHK4700"
    _write_json(invalid_registry, payload)

    with pytest.raises(TaskpackSigningError) as exc_info:
        load_diagnostic_registry(root=root, registry_rel_path=_DIAGNOSTIC_REGISTRY_REL)
    error_payload = _error_payload(exc_info.value)
    assert error_payload["code"] == AHK4808_CONTRACT_REGISTRY_INVALID


def test_signing_required_violations_are_error_channel_only(tmp_path: Path) -> None:
    root, taskpack_dir_rel, _ = _setup_repo(tmp_path)
    manifest_hash, bundle_hash = _compute_taskpack_hashes(root / taskpack_dir_rel)
    envelope_rel, trust_registry_rel = _seed_ed25519_material(
        root,
        manifest_hash=manifest_hash,
        bundle_hash=bundle_hash,
    )

    envelope_path = root / envelope_rel
    envelope_payload = _read_json(envelope_path)
    envelope_payload["taskpack_bundle_hash"] = "0" * 64
    _write_json(envelope_path, envelope_payload)

    command = [
        sys.executable,
        "-m",
        "adeu_agent_harness.verify_taskpack_signature",
        "--taskpack-dir",
        taskpack_dir_rel,
        "--signature-envelope",
        envelope_rel,
        "--trust-anchor-registry",
        trust_registry_rel,
        "--verification-reference-time-utc",
        "2026-03-05T00:00:00Z",
        "--diagnostic-registry",
        _DIAGNOSTIC_REGISTRY_REL,
        "--repo-root",
        str(root),
    ]
    completed = subprocess.run(command, cwd=root, capture_output=True, text=True, check=False)
    assert completed.returncode != 0
    assert completed.stdout == ""
    stderr_payload = json.loads(completed.stderr.strip())
    assert stderr_payload["schema"] == "taskpack_signing_error@1"
    assert stderr_payload["code"] == AHK4804_CROSS_ARTIFACT_HASH_MISMATCH


def test_stop_gate_metric_keyset_exact_equal_v47() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    baseline_path = repo_root / "artifacts" / "stop_gate" / "metrics_v47_closeout.json"
    candidate_path = repo_root / "artifacts" / "stop_gate" / "metrics_v47_closeout.json"
    _assert_stop_gate_keyset_equal(baseline_path=baseline_path, candidate_path=candidate_path)


def test_stop_gate_metric_cardinality_equals_80_from_metrics_keys_only() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    metrics_path = repo_root / "artifacts" / "stop_gate" / "metrics_v47_closeout.json"
    _assert_stop_gate_cardinality_80(metrics_path=metrics_path)
