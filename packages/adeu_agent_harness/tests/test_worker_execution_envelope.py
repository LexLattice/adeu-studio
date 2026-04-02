from __future__ import annotations

import json
import shutil
from pathlib import Path
from typing import Any

import pytest
from adeu_agent_harness._test_signing_handoff import seed_signing_handoff_fixture
from adeu_agent_harness.attestation import (
    ATTESTATION_OUTPUT_SCHEMA,
    DEFAULT_ATTESTATION_OUTPUT_ROOT,
    DEFAULT_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT,
    DEFAULT_LOCAL_VERIFICATION_OUTPUT_ROOT,
    PROVIDER_ATTESTATION_INPUT_SCHEMA,
    validate_attested_verification,
)
from adeu_agent_harness.compiled_taskpack_binding import compile_v48b_taskpack_binding
from adeu_agent_harness.run_taskpack import RUNNER_RESULT_SCHEMA, TaskpackRunnerResult, run_taskpack
from adeu_agent_harness.verify_taskpack_run import (
    DEFAULT_VERIFICATION_ROOT,
    verify_taskpack_run,
)
from adeu_agent_harness.worker_execution_envelope import (
    AHK5801_INPUT_INVALID,
    AHK5802_SCHEMA_MISMATCH,
    AHK5805_LINEAGE_MISMATCH,
    AHK5806_HASH_DRIFT,
    AHK5807_PROMPT_AUTHORITY_DRIFT,
    TASK_RUN_BOUNDARY_INSTANCE_SCHEMA,
    WORKER_EXECUTION_ATTESTATION_SCHEMA,
    WORKER_EXECUTION_PROVENANCE_SCHEMA,
    TaskRunBoundaryInstance,
    WorkerExecutionAttestation,
    WorkerExecutionEnvelopeError,
    WorkerExecutionProvenance,
    build_v48c_worker_execution_envelope,
)
from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json

_DIAGNOSTIC_REGISTRY_REL = "artifacts/agent_harness/v46/diagnostic_registry_v46.json"


@pytest.fixture(autouse=True)
def _enforce_deterministic_env(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TZ", "UTC")
    monkeypatch.setenv("LC_ALL", "C")
    monkeypatch.setenv("PYTHONHASHSEED", "0")


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v48c" / name


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_fixture(name: str) -> dict[str, Any]:
    return _read_json(_fixture_path(name))


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    _write(path, canonical_json(payload) + "\n")


def _seed_reference_repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    root.mkdir()
    _write(root / "pyproject.toml", "[tool.ruff]\nline-length = 100\n")
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)

    source_root = _repo_root()
    for rel_path in (
        "packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json",
        "packages/adeu_commitments_ir/tests/fixtures/v47e/reference_anm_policy_consumer_binding_profile.json",
        "apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json",
        "apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json",
        "artifacts/semantic_compiler/v41/evidence_manifest.json",
        "artifacts/semantic_compiler/v41/surface_diff.json",
    ):
        destination = root / rel_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_root / rel_path, destination)

    _write_json(
        root / "artifacts" / "semantic_compiler" / "v40" / "commitments_ir.json",
        {
            "schema": "adeu_commitments_ir@0.1",
            "modules": [],
            "locks": [],
        },
    )
    return root


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
    rel_path = "packages/adeu_agent_harness/tests/test_taskpack_binding.py"
    target_path = root / rel_path
    target_path.parent.mkdir(parents=True, exist_ok=True)
    _write(target_path, "before\n")
    path = root / "artifacts" / "agent_harness" / "v48c" / "candidate_change_plan.json"
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


def _write_runner_result(root: Path, *, run_result: TaskpackRunnerResult) -> Path:
    path = root / "artifacts" / "agent_harness" / "v48c" / "runner_result_success.json"
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
    path = root / "artifacts" / "agent_harness" / "v48c" / "attested_verified_result.json"
    _write_json(path, source_payload)
    return path


def _seed_provider_attestation_input(
    root: Path,
    *,
    signing_reference_time_utc: str,
    manifest_hash: str,
    candidate_change_plan_hash: str,
    runner_provenance_hash: str,
    verified_result_hash: str,
) -> Path:
    path = root / "artifacts" / "agent_harness" / "v48c" / "provider_attestation_input.json"
    _write_json(
        path,
        {
            "schema": PROVIDER_ATTESTATION_INPUT_SCHEMA,
            "provider_id": "deterministic_test_enclave",
            "attestation_key_id": "key_ed25519_test",
            "algorithm": "ed25519",
            "verification_reference_time_utc": signing_reference_time_utc,
            "taskpack_manifest_hash": manifest_hash,
            "candidate_change_plan_hash": candidate_change_plan_hash,
            "runner_provenance_hash": runner_provenance_hash,
            "verified_result_hash": verified_result_hash,
            "attestation_verified": True,
            "opaque_provider_evidence": "raw-provider-proof::deterministic_test_enclave",
        },
    )
    return path


def _seed_v48c_support_chain(tmp_path: Path) -> dict[str, Any]:
    root = _seed_reference_repo(tmp_path)
    compiled_binding_spec = _read_json(
        _repo_root()
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48b"
        / "reference_compiled_taskpack_binding_spec.json"
    )
    compiled = compile_v48b_taskpack_binding(
        **compiled_binding_spec,
        repo_root_path=root,
    )

    taskpack_dir = compiled.compiled_binding_path.parent
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)
    adapter_registry_path = _seed_adapter_registry(root)
    candidate_change_plan_path = _write_candidate_change_plan(root)
    run_result = run_taskpack(
        taskpack_dir=taskpack_dir.relative_to(root).as_posix(),
        adapter_registry_path=adapter_registry_path.relative_to(root).as_posix(),
        adapter_id="default",
        candidate_change_plan_path=candidate_change_plan_path.relative_to(root).as_posix(),
        dry_run=True,
        repo_root_path=root,
        **signing.as_kwargs(),
    )
    runner_result_path = _write_runner_result(root, run_result=run_result)
    _seed_diagnostic_registry(root)

    verifier_result = verify_taskpack_run(
        taskpack_dir=taskpack_dir.relative_to(root).as_posix(),
        candidate_change_plan_path=candidate_change_plan_path.relative_to(root).as_posix(),
        runner_result_path=runner_result_path.relative_to(root).as_posix(),
        runner_provenance_path=run_result.provenance_path.relative_to(root).as_posix(),
        policy_rejection_diagnostics_path=None,
        verification_output_root=DEFAULT_VERIFICATION_ROOT,
        policy_recompute_output_root="artifacts/agent_harness/v48c/recompute",
        diagnostic_registry_path=_DIAGNOSTIC_REGISTRY_REL,
        repo_root_path=root,
        **signing.as_kwargs(),
    )
    verification_result_path = verifier_result.verification_result_path
    verification_result_payload = _read_json(verification_result_path)
    attested_verified_result_path = _seed_attested_verified_result(
        root,
        source_payload=verification_result_payload,
    )
    provider_attestation_input_path = _seed_provider_attestation_input(
        root,
        signing_reference_time_utc=signing.verification_reference_time_utc,
        manifest_hash=compiled.compiled_binding.manifest_sha256,
        candidate_change_plan_hash=run_result.candidate_change_plan_hash,
        runner_provenance_hash=sha256_canonical_json(_read_json(run_result.provenance_path)),
        verified_result_hash=verification_result_payload["verified_result_hash"],
    )
    attestation_artifacts = validate_attested_verification(
        taskpack_dir=taskpack_dir.relative_to(root).as_posix(),
        candidate_change_plan_path=candidate_change_plan_path.relative_to(root).as_posix(),
        runner_result_path=runner_result_path.relative_to(root).as_posix(),
        runner_provenance_path=run_result.provenance_path.relative_to(root).as_posix(),
        attested_verified_result_path=attested_verified_result_path.relative_to(root).as_posix(),
        provider_attestation_input_path=provider_attestation_input_path.relative_to(root).as_posix(),
        attestation_output_root=DEFAULT_ATTESTATION_OUTPUT_ROOT,
        local_verification_output_root=DEFAULT_LOCAL_VERIFICATION_OUTPUT_ROOT,
        local_policy_recompute_output_root=DEFAULT_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT,
        diagnostic_registry_path=_DIAGNOSTIC_REGISTRY_REL,
        repo_root_path=root,
        **signing.as_kwargs(),
    )
    attestation_validator_result_path = (
        root / "artifacts" / "agent_harness" / "v48c" / "attestation_validator_result.json"
    )
    _write_json(
        attestation_validator_result_path,
        {
            "schema": ATTESTATION_OUTPUT_SCHEMA,
            "remote_enclave_attestation_path": (
                attestation_artifacts.remote_enclave_attestation_path.relative_to(root).as_posix()
            ),
            "remote_enclave_attestation_hash": (
                attestation_artifacts.remote_enclave_attestation_hash
            ),
            "attestation_verification_result_path": (
                attestation_artifacts.attestation_verification_result_path.relative_to(root).as_posix()
            ),
            "attestation_verification_result_hash": (
                attestation_artifacts.attestation_verification_result_hash
            ),
            "attested_verified_result_path": (
                attestation_artifacts.attested_verified_result_path.relative_to(root).as_posix()
            ),
            "attested_verified_result_hash": attestation_artifacts.attested_verified_result_hash,
            "local_verified_result_path": (
                attestation_artifacts.local_verified_result_path.relative_to(root).as_posix()
            ),
            "local_verified_result_hash": attestation_artifacts.local_verified_result_hash,
        },
    )

    return {
        "root": root,
        "compiled_binding_path": compiled.compiled_binding_path,
        "compiled_binding": compiled.compiled_binding,
        "runner_result_path": runner_result_path,
        "runner_provenance_path": run_result.provenance_path,
        "verification_result_path": verification_result_path,
        "attestation_validator_result_path": attestation_validator_result_path,
    }


def test_v48c_reference_worker_execution_envelope_replays_deterministically(
    tmp_path: Path,
) -> None:
    seeded = _seed_v48c_support_chain(tmp_path)
    root = seeded["root"]
    compiled_binding = seeded["compiled_binding"]

    first = build_v48c_worker_execution_envelope(
        compiled_binding_refs=[seeded["compiled_binding_path"].relative_to(root).as_posix()],
        repo_refs=[f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"],
        task_instance_identities=["task:v48c:reference_worker_execution"],
        worker_provider_ids=["openai"],
        worker_model_ids=["gpt-5.4-codex"],
        execution_adapter_refs=[
            "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
        ],
        runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
        runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
        verification_result_refs=[
            seeded["verification_result_path"].relative_to(root).as_posix(),
        ],
        attestation_validator_result_refs=[
            seeded["attestation_validator_result_path"].relative_to(root).as_posix(),
        ],
        prompt_authority_postures=["projection_only_conflict_fail_closed"],
        out_dir="artifacts/agent_harness/v48c/reference_worker_execution",
        repo_root_path=root,
    )
    first_bytes = {
        "boundary": first.boundary_instance_path.read_bytes(),
        "attestation": first.worker_execution_attestation_path.read_bytes(),
        "provenance": first.worker_execution_provenance_path.read_bytes(),
    }
    second = build_v48c_worker_execution_envelope(
        compiled_binding_refs=[seeded["compiled_binding_path"].relative_to(root).as_posix()],
        repo_refs=[f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"],
        task_instance_identities=["task:v48c:reference_worker_execution"],
        worker_provider_ids=["openai"],
        worker_model_ids=["gpt-5.4-codex"],
        execution_adapter_refs=[
            "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
        ],
        runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
        runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
        verification_result_refs=[
            seeded["verification_result_path"].relative_to(root).as_posix(),
        ],
        attestation_validator_result_refs=[
            seeded["attestation_validator_result_path"].relative_to(root).as_posix(),
        ],
        prompt_authority_postures=["projection_only_conflict_fail_closed"],
        out_dir="artifacts/agent_harness/v48c/reference_worker_execution",
        repo_root_path=root,
    )

    assert first.boundary_instance.model_dump(mode="json", exclude_none=True) == _read_fixture(
        "reference_task_run_boundary_instance.json"
    )
    assert first.worker_execution_attestation.model_dump(
        mode="json",
        exclude_none=True,
    ) == _read_fixture("reference_worker_execution_attestation.json")
    assert first.worker_execution_provenance.model_dump(
        mode="json",
        exclude_none=True,
    ) == _read_fixture("reference_worker_execution_provenance.json")

    assert first_bytes["boundary"] == second.boundary_instance_path.read_bytes()
    assert first_bytes["attestation"] == second.worker_execution_attestation_path.read_bytes()
    assert first_bytes["provenance"] == second.worker_execution_provenance_path.read_bytes()


def test_v48c_models_accept_committed_reference_payloads() -> None:
    boundary = TaskRunBoundaryInstance.model_validate(
        _read_fixture("reference_task_run_boundary_instance.json")
    )
    attestation = WorkerExecutionAttestation.model_validate(
        _read_fixture("reference_worker_execution_attestation.json")
    )
    provenance = WorkerExecutionProvenance.model_validate(
        _read_fixture("reference_worker_execution_provenance.json")
    )

    assert boundary.schema == TASK_RUN_BOUNDARY_INSTANCE_SCHEMA
    assert attestation.schema == WORKER_EXECUTION_ATTESTATION_SCHEMA
    assert provenance.schema == WORKER_EXECUTION_PROVENANCE_SCHEMA


def test_v48c_rejects_raw_v48a_bypass(tmp_path: Path) -> None:
    seeded = _seed_v48c_support_chain(tmp_path)
    root = seeded["root"]
    compiled_binding = seeded["compiled_binding"]

    with pytest.raises(WorkerExecutionEnvelopeError, match=AHK5802_SCHEMA_MISMATCH):
        build_v48c_worker_execution_envelope(
            compiled_binding_refs=[
                "packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json"
            ],
            repo_refs=[
                f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"
            ],
            task_instance_identities=["task:v48c:reference_worker_execution"],
            worker_provider_ids=["openai"],
            worker_model_ids=["gpt-5.4-codex"],
            execution_adapter_refs=[
                "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
            ],
            runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
            runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
            verification_result_refs=None,
            attestation_validator_result_refs=None,
            prompt_authority_postures=["projection_only_conflict_fail_closed"],
            out_dir="artifacts/agent_harness/v48c/reject_raw_v48a_bypass",
            repo_root_path=root,
        )


def test_v48c_rejects_worker_provider_conflation_with_attestation_provider(
    tmp_path: Path,
) -> None:
    seeded = _seed_v48c_support_chain(tmp_path)
    root = seeded["root"]
    compiled_binding = seeded["compiled_binding"]

    with pytest.raises(WorkerExecutionEnvelopeError, match=AHK5805_LINEAGE_MISMATCH):
        build_v48c_worker_execution_envelope(
            compiled_binding_refs=[seeded["compiled_binding_path"].relative_to(root).as_posix()],
            repo_refs=[f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"],
            task_instance_identities=["task:v48c:reference_worker_execution"],
            worker_provider_ids=["deterministic_test_enclave"],
            worker_model_ids=["gpt-5.4-codex"],
            execution_adapter_refs=[
                "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
            ],
            runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
            runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
            verification_result_refs=None,
            attestation_validator_result_refs=None,
            prompt_authority_postures=["projection_only_conflict_fail_closed"],
            out_dir="artifacts/agent_harness/v48c/reject_worker_provider_conflation",
            repo_root_path=root,
        )


def test_v48c_rejects_runner_provenance_hash_mismatch(tmp_path: Path) -> None:
    seeded = _seed_v48c_support_chain(tmp_path)
    root = seeded["root"]
    compiled_binding = seeded["compiled_binding"]
    runner_provenance_payload = _read_json(seeded["runner_provenance_path"])
    runner_provenance_payload["provenance_hash"] = "0" * 64
    _write_json(seeded["runner_provenance_path"], runner_provenance_payload)

    with pytest.raises(WorkerExecutionEnvelopeError, match=AHK5806_HASH_DRIFT):
        build_v48c_worker_execution_envelope(
            compiled_binding_refs=[seeded["compiled_binding_path"].relative_to(root).as_posix()],
            repo_refs=[f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"],
            task_instance_identities=["task:v48c:reference_worker_execution"],
            worker_provider_ids=["openai"],
            worker_model_ids=["gpt-5.4-codex"],
            execution_adapter_refs=[
                "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
            ],
            runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
            runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
            verification_result_refs=None,
            attestation_validator_result_refs=None,
            prompt_authority_postures=["projection_only_conflict_fail_closed"],
            out_dir="artifacts/agent_harness/v48c/reject_runner_provenance_hash_mismatch",
            repo_root_path=root,
        )


def test_v48c_rejects_missing_verification_result_required_field(tmp_path: Path) -> None:
    seeded = _seed_v48c_support_chain(tmp_path)
    root = seeded["root"]
    compiled_binding = seeded["compiled_binding"]
    verification_result_payload = _read_json(seeded["verification_result_path"])
    verification_result_payload.pop("taskpack_manifest_hash")
    _write_json(seeded["verification_result_path"], verification_result_payload)

    with pytest.raises(WorkerExecutionEnvelopeError, match=AHK5801_INPUT_INVALID):
        build_v48c_worker_execution_envelope(
            compiled_binding_refs=[seeded["compiled_binding_path"].relative_to(root).as_posix()],
            repo_refs=[f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"],
            task_instance_identities=["task:v48c:reference_worker_execution"],
            worker_provider_ids=["openai"],
            worker_model_ids=["gpt-5.4-codex"],
            execution_adapter_refs=[
                "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
            ],
            runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
            runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
            verification_result_refs=[
                seeded["verification_result_path"].relative_to(root).as_posix(),
            ],
            attestation_validator_result_refs=None,
            prompt_authority_postures=["projection_only_conflict_fail_closed"],
            out_dir="artifacts/agent_harness/v48c/reject_missing_verification_field",
            repo_root_path=root,
        )


def test_v48c_rejects_missing_attestation_verification_required_field(tmp_path: Path) -> None:
    seeded = _seed_v48c_support_chain(tmp_path)
    root = seeded["root"]
    compiled_binding = seeded["compiled_binding"]
    attestation_validator_payload = _read_json(seeded["attestation_validator_result_path"])
    attestation_verification_result_path = (
        root / attestation_validator_payload["attestation_verification_result_path"]
    )
    attestation_verification_payload = _read_json(attestation_verification_result_path)
    attestation_verification_payload.pop("provider_id")
    _write_json(attestation_verification_result_path, attestation_verification_payload)

    with pytest.raises(WorkerExecutionEnvelopeError, match=AHK5801_INPUT_INVALID):
        build_v48c_worker_execution_envelope(
            compiled_binding_refs=[seeded["compiled_binding_path"].relative_to(root).as_posix()],
            repo_refs=[f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"],
            task_instance_identities=["task:v48c:reference_worker_execution"],
            worker_provider_ids=["openai"],
            worker_model_ids=["gpt-5.4-codex"],
            execution_adapter_refs=[
                "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
            ],
            runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
            runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
            verification_result_refs=[
                seeded["verification_result_path"].relative_to(root).as_posix(),
            ],
            attestation_validator_result_refs=[
                seeded["attestation_validator_result_path"].relative_to(root).as_posix(),
            ],
            prompt_authority_postures=["projection_only_conflict_fail_closed"],
            out_dir="artifacts/agent_harness/v48c/reject_missing_attestation_verification_field",
            repo_root_path=root,
        )


def test_v48c_rejects_missing_attestation_output_remote_fields(tmp_path: Path) -> None:
    seeded = _seed_v48c_support_chain(tmp_path)
    root = seeded["root"]
    compiled_binding = seeded["compiled_binding"]
    attestation_validator_payload = _read_json(seeded["attestation_validator_result_path"])
    attestation_validator_payload.pop("remote_enclave_attestation_path")
    _write_json(seeded["attestation_validator_result_path"], attestation_validator_payload)

    with pytest.raises(WorkerExecutionEnvelopeError, match=AHK5801_INPUT_INVALID):
        build_v48c_worker_execution_envelope(
            compiled_binding_refs=[seeded["compiled_binding_path"].relative_to(root).as_posix()],
            repo_refs=[f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"],
            task_instance_identities=["task:v48c:reference_worker_execution"],
            worker_provider_ids=["openai"],
            worker_model_ids=["gpt-5.4-codex"],
            execution_adapter_refs=[
                "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
            ],
            runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
            runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
            verification_result_refs=None,
            attestation_validator_result_refs=[
                seeded["attestation_validator_result_path"].relative_to(root).as_posix(),
            ],
            prompt_authority_postures=["projection_only_conflict_fail_closed"],
            out_dir="artifacts/agent_harness/v48c/reject_missing_attestation_output_remote_fields",
            repo_root_path=root,
        )


def test_v48c_rejects_prompt_authority_drift(tmp_path: Path) -> None:
    seeded = _seed_v48c_support_chain(tmp_path)
    root = seeded["root"]
    compiled_binding = seeded["compiled_binding"]

    with pytest.raises(WorkerExecutionEnvelopeError, match=AHK5807_PROMPT_AUTHORITY_DRIFT):
        build_v48c_worker_execution_envelope(
            compiled_binding_refs=[seeded["compiled_binding_path"].relative_to(root).as_posix()],
            repo_refs=[f"repo_identity:{compiled_binding.snapshot_id}:{compiled_binding.snapshot_sha256}"],
            task_instance_identities=["task:v48c:reference_worker_execution"],
            worker_provider_ids=["openai"],
            worker_model_ids=["gpt-5.4-codex"],
            execution_adapter_refs=[
                "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json#default"
            ],
            runner_result_refs=[seeded["runner_result_path"].relative_to(root).as_posix()],
            runner_provenance_refs=[seeded["runner_provenance_path"].relative_to(root).as_posix()],
            verification_result_refs=None,
            attestation_validator_result_refs=None,
            prompt_authority_postures=["prompt_can_add_authority"],
            out_dir="artifacts/agent_harness/v48c/reject_prompt_authority_drift",
            repo_root_path=root,
        )
