from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_agent_harness._test_signing_handoff import (
    SigningHandoffFixture,
    seed_signing_handoff_fixture,
)
from adeu_agent_harness.attestation import (
    ATTESTATION_VERIFICATION_RESULT_SCHEMA,
    DEFAULT_ATTESTATION_OUTPUT_ROOT,
    DEFAULT_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT,
    DEFAULT_LOCAL_VERIFICATION_OUTPUT_ROOT,
    PROVIDER_ATTESTATION_INPUT_SCHEMA,
    REMOTE_ENCLAVE_ATTESTATION_SCHEMA,
    SHARED_ATTESTATION_VALIDATOR,
    SHARED_ATTESTATION_VALIDATOR_IDENTIFIER,
    TaskpackAttestationError,
    validate_attested_verification,
)
from adeu_agent_harness.compile import (
    PIPELINE_PROFILE_SCHEMA,
    TASKPACK_PROFILE_REGISTRY_SCHEMA,
    compile_taskpack,
)
from adeu_agent_harness.run_taskpack import RUNNER_RESULT_SCHEMA, TaskpackRunnerResult, run_taskpack
from adeu_agent_harness.verify_taskpack_run import verify_taskpack_run
from urm_runtime.hashing import canonical_json, sha256_canonical_json

_OUT_DIR = "artifacts/agent_harness/v53/taskpacks/v41/v53_default"
_DIAGNOSTIC_REGISTRY_REL = "artifacts/agent_harness/v46/diagnostic_registry_v46.json"


@pytest.fixture(autouse=True)
def _enforce_deterministic_env(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TZ", "UTC")
    monkeypatch.setenv("LC_ALL", "C")
    monkeypatch.setenv("PYTHONHASHSEED", "0")


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    _write(path, canonical_json(payload) + "\n")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


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
        "profile_id": "v53_default",
        "task_scope_title": "V53 B1 Attested Verifier Baseline",
        "task_scope_summary": "Compile deterministic taskpack for attestation baseline.",
        "compiled_commitments_ir_path": "artifacts/semantic_compiler/v40/commitments_ir.json",
        "acceptance_criteria": [
            "Emit canonical v46 verifier outputs on success.",
            "Reuse v34a signing handoff authority for downstream verifier lanes.",
        ],
        "allowlist_paths": [
            "packages/adeu_agent_harness/src/adeu_agent_harness",
            "packages/adeu_agent_harness/tests",
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
                "slot_id": "runner_provenance_hash",
                "description": "Runner provenance hash.",
                "required": True,
            }
        ],
    }
    profile_path = root / "artifacts" / "agent_harness" / "v53" / "profiles" / "v53_default.json"
    _write_json(profile_path, profile_payload)
    registry_path = root / "artifacts" / "agent_harness" / "v53" / "taskpack_profile_registry.json"
    _write_json(
        registry_path,
        {
            "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
            "profiles": [
                {
                    "profile_id": "v53_default",
                    "profile_sha256": sha256_canonical_json(profile_payload),
                    "profile_payload_path": "artifacts/agent_harness/v53/profiles/v53_default.json",
                }
            ],
        },
    )
    return registry_path


def _compile_taskpack(root: Path, *, registry_path: Path) -> Path:
    result = compile_taskpack(
        profile_registry_path=registry_path.relative_to(root),
        profile_id="v53_default",
        source_semantic_arc="v41",
        out_dir=_OUT_DIR,
        repo_root_path=root,
    )
    return result.out_dir


def _seed_adapter_registry(root: Path) -> Path:
    path = root / "artifacts" / "agent_harness" / "v45" / "taskpack_runner_adapter_registry.json"
    _write_json(
        path,
        {
            "schema": "taskpack_runner_adapter_registry@1",
            "adapters": [
                {
                    "adapter_id": "default",
                    "adapter_kind": "candidate_plan_passthrough",
                }
            ],
        },
    )
    return path


def _seed_diagnostic_registry(root: Path) -> str:
    path = root / _DIAGNOSTIC_REGISTRY_REL
    _write_json(
        path,
        {
            "schema": "taskpack_verifier_diagnostic_registry@1",
            "codes": [
                {
                    "issue_code": f"AHK46{index:02d}",
                    "title": f"V46_{index:02d}",
                    "description": "v46 verifier diagnostic code",
                }
                for index in range(16)
            ],
        },
    )
    return _DIAGNOSTIC_REGISTRY_REL


def _write_candidate_change_plan(root: Path) -> Path:
    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/v53_success_fixture.txt"
    target_path = root / rel_path
    target_path.parent.mkdir(parents=True, exist_ok=True)
    _write(target_path, "before\n")
    path = root / "artifacts" / "agent_harness" / "v53" / "candidate_change_plan.json"
    _write_json(
        path,
        {
            "schema": "candidate_change_plan@1",
            "file_operations": [
                {
                    "path": rel_path,
                    "operation_kind": "update",
                    "unified_diff": (
                        f"--- a/{rel_path}\n"
                        f"+++ b/{rel_path}\n"
                        "@@ -1,1 +1,1 @@\n"
                        "-before\n"
                        "+after\n"
                    ),
                }
            ],
            "proposed_commands": [],
        },
    )
    return path


def _run_taskpack_signed(
    root: Path,
    *,
    taskpack_dir: Path,
    adapter_registry_path: Path,
    candidate_change_plan_path: Path,
    signing: SigningHandoffFixture,
) -> TaskpackRunnerResult:
    return run_taskpack(
        taskpack_dir=taskpack_dir.relative_to(root).as_posix(),
        adapter_registry_path=adapter_registry_path.relative_to(root).as_posix(),
        adapter_id="default",
        candidate_change_plan_path=candidate_change_plan_path.relative_to(root).as_posix(),
        dry_run=True,
        repo_root_path=root,
        **signing.as_kwargs(),
    )


def _write_runner_result(root: Path, *, run_result: TaskpackRunnerResult) -> Path:
    path = root / "artifacts" / "agent_harness" / "v53" / "runner_result_success.json"
    payload = {
        "schema": RUNNER_RESULT_SCHEMA,
        "dry_run": run_result.dry_run,
        "candidate_change_plan_hash": run_result.candidate_change_plan_hash,
        "dry_run_preview_path": (
            run_result.dry_run_preview_path.relative_to(root).as_posix()
            if run_result.dry_run_preview_path is not None
            else None
        ),
        "provenance_path": run_result.provenance_path.relative_to(root).as_posix(),
        "provenance_hash": run_result.provenance_hash,
        "rejection_diagnostic_path": (
            run_result.rejection_diagnostic_path.relative_to(root).as_posix()
            if run_result.rejection_diagnostic_path is not None
            else None
        ),
    }
    _write_json(path, payload)
    return path


def _seed_attested_verified_result(root: Path, *, source_payload: dict[str, Any]) -> Path:
    path = (
        root
        / "artifacts"
        / "agent_harness"
        / "v53"
        / "attested"
        / "attested_verified_result.json"
    )
    _write_json(path, source_payload)
    return path


def _seed_provider_attestation_input(
    root: Path,
    *,
    signing: SigningHandoffFixture,
    manifest_hash: str,
    candidate_change_plan_hash: str,
    full_runner_provenance_hash: str,
    verified_result_hash: str,
) -> Path:
    path = (
        root
        / "artifacts"
        / "agent_harness"
        / "v53"
        / "attested"
        / "provider_attestation_input.json"
    )
    _write_json(
        path,
        {
            "schema": PROVIDER_ATTESTATION_INPUT_SCHEMA,
            "provider_id": "deterministic_test_enclave",
            "attestation_key_id": "key_ed25519_test",
            "algorithm": "ed25519",
            "verification_reference_time_utc": signing.verification_reference_time_utc,
            "taskpack_manifest_hash": manifest_hash,
            "candidate_change_plan_hash": candidate_change_plan_hash,
            "runner_provenance_hash": full_runner_provenance_hash,
            "verified_result_hash": verified_result_hash,
            "attestation_verified": True,
            "opaque_provider_evidence": "raw-provider-proof::deterministic_test_enclave",
        },
    )
    return path


def _prepare_attestation_inputs(
    tmp_path: Path,
) -> tuple[Path, Path, Path, Path, Path, Path, Path, SigningHandoffFixture]:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    _seed_diagnostic_registry(root)
    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)
    candidate_change_plan_path = _write_candidate_change_plan(root)
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)
    run_result = _run_taskpack_signed(
        root,
        taskpack_dir=taskpack_dir,
        adapter_registry_path=adapter_registry_path,
        candidate_change_plan_path=candidate_change_plan_path,
        signing=signing,
    )
    runner_result_path = _write_runner_result(root, run_result=run_result)

    verify_result = verify_taskpack_run(
        taskpack_dir=taskpack_dir.relative_to(root).as_posix(),
        candidate_change_plan_path=candidate_change_plan_path.relative_to(root).as_posix(),
        runner_result_path=runner_result_path.relative_to(root).as_posix(),
        runner_provenance_path=run_result.provenance_path.relative_to(root).as_posix(),
        policy_rejection_diagnostics_path=None,
        verification_output_root="artifacts/agent_harness/v53/attested_seed_verification",
        diagnostic_registry_path=_DIAGNOSTIC_REGISTRY_REL,
        repo_root_path=root,
        **signing.as_kwargs(),
    )
    attested_verified_payload = _read_json(verify_result.verification_result_path)
    attested_verified_result_path = _seed_attested_verified_result(
        root,
        source_payload=attested_verified_payload,
    )
    full_runner_provenance_hash = sha256_canonical_json(_read_json(run_result.provenance_path))
    provider_attestation_input_path = _seed_provider_attestation_input(
        root,
        signing=signing,
        manifest_hash=attested_verified_payload["taskpack_manifest_hash"],
        candidate_change_plan_hash=attested_verified_payload["candidate_change_plan_hash"],
        full_runner_provenance_hash=full_runner_provenance_hash,
        verified_result_hash=attested_verified_payload["verified_result_hash"],
    )
    return (
        root,
        taskpack_dir,
        candidate_change_plan_path,
        runner_result_path,
        run_result.provenance_path,
        attested_verified_result_path,
        provider_attestation_input_path,
        signing,
    )


def _validate_attested_verification(
    root: Path,
    *,
    taskpack_dir: Path,
    candidate_change_plan_path: Path,
    runner_result_path: Path,
    runner_provenance_path: Path,
    attested_verified_result_path: Path,
    provider_attestation_input_path: Path,
    signing: SigningHandoffFixture,
):
    return validate_attested_verification(
        taskpack_dir=taskpack_dir.relative_to(root).as_posix(),
        candidate_change_plan_path=candidate_change_plan_path.relative_to(root).as_posix(),
        runner_result_path=runner_result_path.relative_to(root).as_posix(),
        runner_provenance_path=runner_provenance_path.relative_to(root).as_posix(),
        attested_verified_result_path=attested_verified_result_path.relative_to(root).as_posix(),
        provider_attestation_input_path=provider_attestation_input_path.relative_to(root).as_posix(),
        repo_root_path=root,
        attestation_output_root=DEFAULT_ATTESTATION_OUTPUT_ROOT,
        local_verification_output_root=DEFAULT_LOCAL_VERIFICATION_OUTPUT_ROOT,
        local_policy_recompute_output_root=DEFAULT_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT,
        diagnostic_registry_path=_DIAGNOSTIC_REGISTRY_REL,
        **signing.as_kwargs(),
    )


def _error_payload(exc: TaskpackAttestationError) -> dict[str, Any]:
    payload = json.loads(str(exc))
    assert payload["schema"] == "taskpack_attestation_error@1"
    return payload


def _retarget_verified_result_hash(payload: dict[str, Any]) -> None:
    subject = {
        "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
        "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
        "runner_provenance_hash": payload["runner_provenance_hash"],
        "verification_result": payload["verification_result"],
        "exit_status": payload["exit_status"],
    }
    payload["verified_result_hash"] = sha256_canonical_json(subject)


def test_validate_attested_verification_emits_deterministic_attestation_artifacts(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_change_plan_path,
        runner_result_path,
        runner_provenance_path,
        attested_verified_result_path,
        provider_attestation_input_path,
        signing,
    ) = _prepare_attestation_inputs(tmp_path)

    first = _validate_attested_verification(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=candidate_change_plan_path,
        runner_result_path=runner_result_path,
        runner_provenance_path=runner_provenance_path,
        attested_verified_result_path=attested_verified_result_path,
        provider_attestation_input_path=provider_attestation_input_path,
        signing=signing,
    )
    second = _validate_attested_verification(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=candidate_change_plan_path,
        runner_result_path=runner_result_path,
        runner_provenance_path=runner_provenance_path,
        attested_verified_result_path=attested_verified_result_path,
        provider_attestation_input_path=provider_attestation_input_path,
        signing=signing,
    )

    assert (
        first.remote_enclave_attestation_path.read_bytes()
        == second.remote_enclave_attestation_path.read_bytes()
    )
    assert (
        first.attestation_verification_result_path.read_bytes()
        == second.attestation_verification_result_path.read_bytes()
    )

    remote_attestation_payload = _read_json(first.remote_enclave_attestation_path)
    verification_payload = _read_json(first.attestation_verification_result_path)

    assert remote_attestation_payload["schema"] == REMOTE_ENCLAVE_ATTESTATION_SCHEMA
    assert (
        remote_attestation_payload["shared_attestation_validator"]
        == SHARED_ATTESTATION_VALIDATOR
    )
    assert (
        remote_attestation_payload["shared_attestation_validator_identifier"]
        == SHARED_ATTESTATION_VALIDATOR_IDENTIFIER
    )
    assert (
        remote_attestation_payload["normalized_claims"]["provider_id"]
        == "deterministic_test_enclave"
    )
    assert "opaque_provider_evidence" not in remote_attestation_payload

    assert verification_payload["schema"] == ATTESTATION_VERIFICATION_RESULT_SCHEMA
    assert verification_payload["verification_passed"] is True
    assert verification_payload["current_local_verification_recomputed"] is True
    assert verification_payload["local_equivalence_verified"] is True


def test_validate_attested_verification_rejects_provider_id_outside_singleton(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_change_plan_path,
        runner_result_path,
        runner_provenance_path,
        attested_verified_result_path,
        provider_attestation_input_path,
        signing,
    ) = _prepare_attestation_inputs(tmp_path)
    provider_input = _read_json(provider_attestation_input_path)
    provider_input["provider_id"] = "Deterministic_Test_Enclave"
    _write_json(provider_attestation_input_path, provider_input)

    with pytest.raises(TaskpackAttestationError) as exc_info:
        _validate_attested_verification(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=candidate_change_plan_path,
            runner_result_path=runner_result_path,
            runner_provenance_path=runner_provenance_path,
            attested_verified_result_path=attested_verified_result_path,
            provider_attestation_input_path=provider_attestation_input_path,
            signing=signing,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5305"


def test_validate_attested_verification_rejects_attestation_verified_false(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_change_plan_path,
        runner_result_path,
        runner_provenance_path,
        attested_verified_result_path,
        provider_attestation_input_path,
        signing,
    ) = _prepare_attestation_inputs(tmp_path)
    provider_input = _read_json(provider_attestation_input_path)
    provider_input["attestation_verified"] = False
    _write_json(provider_attestation_input_path, provider_input)

    with pytest.raises(TaskpackAttestationError) as exc_info:
        _validate_attested_verification(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=candidate_change_plan_path,
            runner_result_path=runner_result_path,
            runner_provenance_path=runner_provenance_path,
            attested_verified_result_path=attested_verified_result_path,
            provider_attestation_input_path=provider_attestation_input_path,
            signing=signing,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5303"


def test_validate_attested_verification_requires_attested_verified_result_schema(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_change_plan_path,
        runner_result_path,
        runner_provenance_path,
        attested_verified_result_path,
        provider_attestation_input_path,
        signing,
    ) = _prepare_attestation_inputs(tmp_path)
    attested_payload = _read_json(attested_verified_result_path)
    attested_payload["schema"] = "taskpack_verification_result@999"
    _write_json(attested_verified_result_path, attested_payload)

    with pytest.raises(TaskpackAttestationError) as exc_info:
        _validate_attested_verification(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=candidate_change_plan_path,
            runner_result_path=runner_result_path,
            runner_provenance_path=runner_provenance_path,
            attested_verified_result_path=attested_verified_result_path,
            provider_attestation_input_path=provider_attestation_input_path,
            signing=signing,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5302"


def test_validate_attested_verification_fails_closed_on_local_equivalence_mismatch(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_change_plan_path,
        runner_result_path,
        runner_provenance_path,
        attested_verified_result_path,
        provider_attestation_input_path,
        signing,
    ) = _prepare_attestation_inputs(tmp_path)
    attested_payload = _read_json(attested_verified_result_path)
    attested_payload["exit_status"] = "remote_success_variant"
    _retarget_verified_result_hash(attested_payload)
    _write_json(attested_verified_result_path, attested_payload)
    provider_input = _read_json(provider_attestation_input_path)
    provider_input["verified_result_hash"] = attested_payload["verified_result_hash"]
    _write_json(provider_attestation_input_path, provider_input)

    with pytest.raises(TaskpackAttestationError) as exc_info:
        _validate_attested_verification(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=candidate_change_plan_path,
            runner_result_path=runner_result_path,
            runner_provenance_path=runner_provenance_path,
            attested_verified_result_path=attested_verified_result_path,
            provider_attestation_input_path=provider_attestation_input_path,
            signing=signing,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5308"


def test_validate_attested_verification_rejects_conflicting_normalized_claims(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_change_plan_path,
        runner_result_path,
        runner_provenance_path,
        attested_verified_result_path,
        provider_attestation_input_path,
        signing,
    ) = _prepare_attestation_inputs(tmp_path)
    provider_input = _read_json(provider_attestation_input_path)
    provider_input["candidate_change_plan_hash"] = "0" * 64
    _write_json(provider_attestation_input_path, provider_input)

    with pytest.raises(TaskpackAttestationError) as exc_info:
        _validate_attested_verification(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=candidate_change_plan_path,
            runner_result_path=runner_result_path,
            runner_provenance_path=runner_provenance_path,
            attested_verified_result_path=attested_verified_result_path,
            provider_attestation_input_path=provider_attestation_input_path,
            signing=signing,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5304"


def test_validate_attested_verification_hashes_only_opaque_provider_evidence(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_change_plan_path,
        runner_result_path,
        runner_provenance_path,
        attested_verified_result_path,
        provider_attestation_input_path,
        signing,
    ) = _prepare_attestation_inputs(tmp_path)

    first = _validate_attested_verification(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=candidate_change_plan_path,
        runner_result_path=runner_result_path,
        runner_provenance_path=runner_provenance_path,
        attested_verified_result_path=attested_verified_result_path,
        provider_attestation_input_path=provider_attestation_input_path,
        signing=signing,
    )
    first_payload = _read_json(first.remote_enclave_attestation_path)
    first_hash = first_payload["normalized_claims"]["opaque_provider_evidence_hash"]

    provider_input = _read_json(provider_attestation_input_path)
    provider_attestation_input_path.write_text(
        json.dumps(provider_input, indent=2, sort_keys=False) + "\n",
        encoding="utf-8",
    )

    second = _validate_attested_verification(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=candidate_change_plan_path,
        runner_result_path=runner_result_path,
        runner_provenance_path=runner_provenance_path,
        attested_verified_result_path=attested_verified_result_path,
        provider_attestation_input_path=provider_attestation_input_path,
        signing=signing,
    )
    second_payload = _read_json(second.remote_enclave_attestation_path)
    second_hash = second_payload["normalized_claims"]["opaque_provider_evidence_hash"]

    assert second_hash == first_hash

    provider_input["opaque_provider_evidence"] = "raw-provider-proof::changed"
    _write_json(provider_attestation_input_path, provider_input)

    third = _validate_attested_verification(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=candidate_change_plan_path,
        runner_result_path=runner_result_path,
        runner_provenance_path=runner_provenance_path,
        attested_verified_result_path=attested_verified_result_path,
        provider_attestation_input_path=provider_attestation_input_path,
        signing=signing,
    )
    third_payload = _read_json(third.remote_enclave_attestation_path)
    third_hash = third_payload["normalized_claims"]["opaque_provider_evidence_hash"]

    assert third_hash != first_hash
