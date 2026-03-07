from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
from typing import Any

import adeu_agent_harness.verify_taskpack_run as verifier_mod
import adeu_agent_harness.write_closeout_evidence as evidence_writer_mod
import pytest
from adeu_agent_harness._test_signing_handoff import seed_signing_handoff_fixture
from adeu_agent_harness._v46_verifier_common import (
    VerifierIssue,
    emit_rejection_diagnostic,
    load_diagnostic_registry,
)
from adeu_agent_harness.attestation import (
    DEFAULT_ATTESTATION_OUTPUT_ROOT,
    LOCAL_EQUIVALENCE_BINDING_FIELDS,
    LOCAL_EQUIVALENCE_SUBJECT_FIELDS,
    LOCAL_EQUIVALENCE_SUBJECT_POLICY,
    PROVIDER_ID,
    PROVIDER_ID_COMPARISON_POLICY,
    REMOTE_ENCLAVE_ATTESTATION_SCHEMA,
    SHARED_ATTESTATION_VALIDATOR,
    SHARED_ATTESTATION_VALIDATOR_IDENTIFIER,
    SHARED_ATTESTATION_VALIDATOR_IDENTIFIER_POLICY,
    validate_attested_verification,
)
from adeu_agent_harness.attestation import (
    DEFAULT_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT as ATTESTATION_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT,
)
from adeu_agent_harness.attestation import (
    DEFAULT_LOCAL_VERIFICATION_OUTPUT_ROOT as ATTESTATION_LOCAL_VERIFICATION_OUTPUT_ROOT,
)
from adeu_agent_harness.attestation import (
    RUNNER_PROVENANCE_HASH_POLICY as ATTESTATION_RUNNER_PROVENANCE_HASH_POLICY,
)
from adeu_agent_harness.attestation import (
    VERIFICATION_PASSED_POLICY as ATTESTATION_VERIFICATION_PASSED_POLICY,
)
from adeu_agent_harness.compile import (
    PIPELINE_PROFILE_SCHEMA,
    TASKPACK_PROFILE_REGISTRY_SCHEMA,
    compile_taskpack,
)
from adeu_agent_harness.matrix_parity import (
    ADAPTER_MATRIX_PARITY_REPORT_SCHEMA,
    ADAPTER_MATRIX_SCHEMA,
)
from adeu_agent_harness.policy_recompute import (
    DEFAULT_POLICY_RECOMPUTE_OUTPUT_ROOT,
    POLICY_RECOMPUTE_RESULT_SCHEMA,
    SHARED_RECOMPUTE_ENGINE,
)
from adeu_agent_harness.retry_context import (
    DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
    MISSING_EXCERPT_SOURCE_POLICY,
    OVERFLOW_POLICY,
    RETRY_CONTEXT_FEEDER_RESULT_SCHEMA,
    SHARED_FEEDER_ENGINE,
    SHARED_FEEDER_ENGINE_IDENTIFIER,
    generate_retry_context,
)
from adeu_agent_harness.retry_context import (
    VERIFICATION_PASSED_POLICY as RETRY_CONTEXT_VERIFICATION_PASSED_POLICY,
)
from adeu_agent_harness.run_taskpack import RUNNER_RESULT_SCHEMA, TaskpackRunnerError, run_taskpack
from adeu_agent_harness.verify_taskpack_run import (
    VERIFICATION_RESULT_SCHEMA,
    TaskpackVerifierError,
    verify_taskpack_run,
)
from adeu_agent_harness.write_closeout_evidence import (
    EVIDENCE_BUNDLE_SCHEMA,
    VERIFIER_PROVENANCE_SCHEMA,
    write_closeout_evidence,
)
from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json

_OUT_DIR = "artifacts/agent_harness/v46/taskpacks/v41/v46_default"
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


def _sync_manifest_component_hash(taskpack_dir: Path, *, relative_path: str) -> None:
    manifest_path = taskpack_dir / "taskpack_manifest.json"
    manifest_payload = _read_json(manifest_path)
    component = next(
        item
        for item in manifest_payload["components"]
        if item["relative_path"] == relative_path
    )
    component["sha256"] = hashlib.sha256((taskpack_dir / relative_path).read_bytes()).hexdigest()
    _write_json(manifest_path, manifest_payload)


def _relative(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def _relative_input(root: Path, value: Path | str) -> str:
    if isinstance(value, Path):
        return value.relative_to(root).as_posix() if value.is_absolute() else value.as_posix()
    return value


def _run_taskpack_signed(
    root: Path,
    *,
    taskpack_dir: Path | str,
    adapter_registry_path: Path | str,
    adapter_id: str,
    candidate_change_plan_path: Path | str,
    dry_run: bool,
):
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)
    return run_taskpack(
        taskpack_dir=_relative_input(root, taskpack_dir),
        adapter_registry_path=_relative_input(root, adapter_registry_path),
        adapter_id=adapter_id,
        candidate_change_plan_path=_relative_input(root, candidate_change_plan_path),
        dry_run=dry_run,
        repo_root_path=root,
        **signing.as_kwargs(),
    )


def _verify_taskpack_run_signed(
    root: Path,
    *,
    taskpack_dir: Path | str,
    candidate_change_plan_path: Path | str,
    runner_result_path: Path | str,
    runner_provenance_path: Path | str,
    policy_rejection_diagnostics_path: Path | str | None,
    verification_output_root: Path | str,
    diagnostic_registry_path: Path | str,
):
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)
    return verify_taskpack_run(
        taskpack_dir=_relative_input(root, taskpack_dir),
        candidate_change_plan_path=_relative_input(root, candidate_change_plan_path),
        runner_result_path=_relative_input(root, runner_result_path),
        runner_provenance_path=_relative_input(root, runner_provenance_path),
        policy_rejection_diagnostics_path=(
            None
            if policy_rejection_diagnostics_path is None
            else _relative_input(root, policy_rejection_diagnostics_path)
        ),
        verification_output_root=_relative_input(root, verification_output_root),
        diagnostic_registry_path=_relative_input(root, diagnostic_registry_path),
        repo_root_path=root,
        **signing.as_kwargs(),
    )


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
        "profile_id": "v46_default",
        "task_scope_title": "V46 U1 Verifier/Evidence MVP",
        "task_scope_summary": "Compile deterministic taskpack for verifier lane.",
        "compiled_commitments_ir_path": "artifacts/semantic_compiler/v40/commitments_ir.json",
        "acceptance_criteria": [
            "Verifier cross-checks runner artifacts before evidence emission.",
            "Evidence writer emits deterministic canonical bundle/provenance.",
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
            },
            {
                "slot_id": "metric_key_continuity_assertion",
                "description": "Metric key continuity assertion block.",
                "required": True,
            },
            {
                "slot_id": "v34a_handoff_completion_evidence",
                "description": "Signing handoff completion evidence block.",
                "required": True,
            },
        ],
    }
    profile_path = root / "artifacts" / "agent_harness" / "v46" / "profiles" / "v46_default.json"
    _write_json(profile_path, profile_payload)

    registry_path = root / "artifacts" / "agent_harness" / "v46" / "taskpack_profile_registry.json"
    _write_json(
        registry_path,
        {
            "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
            "profiles": [
                {
                    "profile_id": "v46_default",
                    "profile_sha256": sha256_canonical_json(profile_payload),
                    "profile_payload_path": "artifacts/agent_harness/v46/profiles/v46_default.json",
                }
            ],
        },
    )
    return registry_path


def _compile_taskpack(root: Path, *, registry_path: Path) -> Path:
    result = compile_taskpack(
        profile_registry_path=_relative(root, registry_path),
        profile_id="v46_default",
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


def _write_candidate_change_plan(
    root: Path,
    *,
    rel_path: str = "packages/adeu_agent_harness/src/adeu_agent_harness/v46_verify_fixture.txt",
    operations: list[dict[str, Any]] | None = None,
    proposed_commands: list[str] | None = None,
    artifact_rel_path: str = "artifacts/agent_harness/v46/candidate_change_plan.json",
) -> Path:
    path = root / artifact_rel_path
    _write_json(
        path,
        {
            "schema": "candidate_change_plan@1",
            "file_operations": (
                operations
                if operations is not None
                else [
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
                ]
            ),
            "proposed_commands": proposed_commands or [],
        },
    )
    return path


def _create_diff(*, rel_path: str, content: str) -> str:
    return (
        "--- /dev/null\n"
        f"+++ b/{rel_path}\n"
        "@@ -0,0 +1,1 @@\n"
        f"+{content}\n"
    )


def _write_runner_result_artifact(root: Path, *, run_result: Any) -> Path:
    path = root / "artifacts" / "agent_harness" / "v46" / "runner_result.json"
    payload = {
        "schema": RUNNER_RESULT_SCHEMA,
        "dry_run": run_result.dry_run,
        "candidate_change_plan_hash": run_result.candidate_change_plan_hash,
        "dry_run_preview_path": (
            _relative(root, run_result.dry_run_preview_path)
            if run_result.dry_run_preview_path is not None
            else None
        ),
        "provenance_path": _relative(root, run_result.provenance_path),
        "provenance_hash": run_result.provenance_hash,
        "rejection_diagnostic_path": (
            _relative(root, run_result.rejection_diagnostic_path)
            if run_result.rejection_diagnostic_path is not None
            else None
        ),
    }
    _write_json(path, payload)
    return path


def _write_runner_result_from_error_details(root: Path, *, details: dict[str, Any]) -> Path:
    path = root / "artifacts" / "agent_harness" / "v51" / "runner_result_policy_failure.json"
    payload = {
        "schema": RUNNER_RESULT_SCHEMA,
        "dry_run": details["dry_run"],
        "candidate_change_plan_hash": details["candidate_change_plan_hash"],
        "dry_run_preview_path": details["dry_run_preview_path"],
        "provenance_path": details["provenance_path"],
        "provenance_hash": details["provenance_hash"],
        "rejection_diagnostic_path": details["rejection_diagnostic_path"],
    }
    _write_json(path, payload)
    return path


def _error_payload(exc: TaskpackVerifierError) -> dict[str, Any]:
    payload = json.loads(str(exc))
    assert payload["schema"] == "taskpack_verifier_error@1"
    return payload


def _prepare_verified_success(tmp_path: Path) -> tuple[Path, Path, Path, str]:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    diagnostic_registry_rel = _seed_diagnostic_registry(root)
    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)

    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/v46_verify_fixture.txt"
    fixture_path = root / rel_path
    _write(fixture_path, "before\n")
    candidate_path = _write_candidate_change_plan(root, rel_path=rel_path)
    run_result = _run_taskpack_signed(
        root,
        taskpack_dir=taskpack_dir,
        adapter_registry_path=adapter_registry_path,
        adapter_id="default",
        candidate_change_plan_path=candidate_path,
        dry_run=True,
    )
    assert fixture_path.read_text(encoding="utf-8") == "before\n"

    runner_result_path = _write_runner_result_artifact(root, run_result=run_result)
    verify_result = _verify_taskpack_run_signed(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=candidate_path,
        runner_result_path=runner_result_path,
        runner_provenance_path=run_result.provenance_path,
        policy_rejection_diagnostics_path=None,
        verification_output_root="artifacts/agent_harness/v46/verification",
        diagnostic_registry_path=diagnostic_registry_rel,
    )
    return root, taskpack_dir, verify_result.verification_result_path, diagnostic_registry_rel


def _prepare_runner_policy_failure(
    tmp_path: Path,
) -> tuple[Path, Path, Path, Path, Path, Path, str, str]:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    diagnostic_registry_rel = _seed_diagnostic_registry(root)
    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)

    blocked_rel = "apps/api/v51_policy_failure_fixture.txt"
    candidate_path = _write_candidate_change_plan(
        root,
        operations=[
            {
                "path": blocked_rel,
                "operation_kind": "create",
                "unified_diff": _create_diff(rel_path=blocked_rel, content="blocked"),
            }
        ],
        proposed_commands=[],
    )

    with pytest.raises(TaskpackRunnerError) as exc_info:
        _run_taskpack_signed(
            root,
            taskpack_dir=taskpack_dir,
            adapter_registry_path=adapter_registry_path,
            adapter_id="default",
            candidate_change_plan_path=candidate_path,
            dry_run=True,
        )

    error_payload = json.loads(str(exc_info.value))
    details = error_payload["details"]
    runner_result_path = _write_runner_result_from_error_details(root, details=details)
    return (
        root,
        taskpack_dir,
        candidate_path,
        runner_result_path,
        Path(details["provenance_path"]),
        Path(details["rejection_diagnostic_path"]),
        blocked_rel,
        diagnostic_registry_rel,
    )


def _seed_u2_evidence_payloads(root: Path) -> tuple[Path, Path, Path]:
    runtime_path = root / "artifacts" / "stop_gate" / "runtime_observability_comparison_v46.json"
    _write_json(
        runtime_path,
        {
            "schema": "runtime_observability_comparison@1",
            "baseline_arc": "v45",
            "target_arc": "v46",
            "rows": [{"metric": "bytes_hashed_total", "baseline": 204690, "target": 204690}],
        },
    )
    continuity_path = root / "artifacts" / "stop_gate" / "metric_key_continuity_assertion_v46.json"
    _write_json(
        continuity_path,
        {
            "schema": "metric_key_continuity_assertion@1",
            "expected_cardinality": 80,
            "observed_cardinality": 80,
            "exact_set_equal": True,
        },
    )
    handoff_path = (
        root / "artifacts" / "stop_gate" / "v34a_handoff_completion_evidence_v49.json"
    )
    _write_json(
        handoff_path,
        {
            "schema": "v34a_handoff_completion_evidence@1",
            "contract_source": (
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md"
                "#v34a_handoff_completion_contract@1"
            ),
            "preflight_entrypoint": "python -m adeu_agent_harness.verify_taskpack_signature",
            "runner_entrypoint": "python -m adeu_agent_harness.run_taskpack",
            "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
            "evidence_writer_entrypoint": "python -m adeu_agent_harness.write_closeout_evidence",
            "packaging_entrypoints": [
                "python -m adeu_agent_harness.package_ux_integrated",
                "python -m adeu_agent_harness.package_ux_standalone",
            ],
            "shared_binding_validator_used": (
                "packages/adeu_agent_harness.verify_taskpack_signature."
                "validate_signature_verification_result_for_downstream"
            ),
            "binding_fields_verified": [
                "taskpack_manifest_hash",
                "taskpack_bundle_hash",
                "signature_envelope_hash",
                "trust_anchor_registry_hash",
                "verification_reference_time_utc",
                "preflight_invocation_binding_hash",
                "signer_key_id",
                "algorithm",
                "verified",
            ],
            "verified_required": True,
            "signature_result_consumed_by_runner": True,
            "signature_result_consumed_by_verifier": True,
            "signature_result_consumed_by_packaging": True,
            "current_taskpack_snapshot_binding_enforced": True,
            "detached_user_supplied_handoff_forbidden": True,
            "historical_v47_to_v48_continuity_guard_repaired": True,
            "verification_passed": True,
            "metric_key_cardinality": 80,
            "metric_key_exact_set_equal_v48": True,
            "notes": "v49 X4 closeout evidence fixture.",
        },
    )
    return runtime_path, continuity_path, handoff_path


def _add_matrix_parity_slot(taskpack_dir: Path) -> None:
    evidence_slots_path = taskpack_dir / "EVIDENCE_SLOTS.json"
    evidence_slots_payload = _read_json(evidence_slots_path)
    evidence_slots_payload["slots"].append(
        {
            "slot_id": "v34b_matrix_parity_evidence",
            "description": "Matrix parity evidence block.",
            "required": True,
        }
    )
    evidence_slots_payload["slots"] = sorted(
        evidence_slots_payload["slots"], key=lambda row: row["slot_id"]
    )
    evidence_slots_payload["required_count"] = len(
        [slot for slot in evidence_slots_payload["slots"] if slot["required"] is True]
    )
    _write_json(evidence_slots_path, evidence_slots_payload)
    _sync_manifest_component_hash(taskpack_dir, relative_path="EVIDENCE_SLOTS.json")


def _add_policy_recompute_slot(taskpack_dir: Path) -> None:
    evidence_slots_path = taskpack_dir / "EVIDENCE_SLOTS.json"
    evidence_slots_payload = _read_json(evidence_slots_path)
    evidence_slots_payload["slots"].append(
        {
            "slot_id": "v34c_policy_recompute_evidence",
            "description": "Policy recompute evidence block.",
            "required": True,
        }
    )
    evidence_slots_payload["slots"] = sorted(
        evidence_slots_payload["slots"], key=lambda row: row["slot_id"]
    )
    evidence_slots_payload["required_count"] = len(
        [slot for slot in evidence_slots_payload["slots"] if slot["required"] is True]
    )
    _write_json(evidence_slots_path, evidence_slots_payload)
    _sync_manifest_component_hash(taskpack_dir, relative_path="EVIDENCE_SLOTS.json")


def _add_retry_context_slot(taskpack_dir: Path) -> None:
    evidence_slots_path = taskpack_dir / "EVIDENCE_SLOTS.json"
    evidence_slots_payload = _read_json(evidence_slots_path)
    evidence_slots_payload["slots"].append(
        {
            "slot_id": "v34d_retry_context_evidence",
            "description": "Retry-context feeder evidence block.",
            "required": True,
        }
    )
    evidence_slots_payload["slots"] = sorted(
        evidence_slots_payload["slots"], key=lambda row: row["slot_id"]
    )
    evidence_slots_payload["required_count"] = len(
        [slot for slot in evidence_slots_payload["slots"] if slot["required"] is True]
    )
    _write_json(evidence_slots_path, evidence_slots_payload)
    _sync_manifest_component_hash(taskpack_dir, relative_path="EVIDENCE_SLOTS.json")


def _add_attestation_slot(taskpack_dir: Path) -> None:
    evidence_slots_path = taskpack_dir / "EVIDENCE_SLOTS.json"
    evidence_slots_payload = _read_json(evidence_slots_path)
    evidence_slots_payload["slots"].append(
        {
            "slot_id": "v34e_attestation_evidence",
            "description": "Attested verifier equivalence evidence block.",
            "required": True,
        }
    )
    evidence_slots_payload["slots"] = sorted(
        evidence_slots_payload["slots"], key=lambda row: row["slot_id"]
    )
    evidence_slots_payload["required_count"] = len(
        [slot for slot in evidence_slots_payload["slots"] if slot["required"] is True]
    )
    _write_json(evidence_slots_path, evidence_slots_payload)
    _sync_manifest_component_hash(taskpack_dir, relative_path="EVIDENCE_SLOTS.json")


def _seed_v50_matrix_parity_payloads(
    root: Path,
    *,
    verified_result_path: Path,
) -> tuple[Path, Path, Path]:
    adapter_registry_path = (
        root / "artifacts" / "agent_harness" / "v45" / "taskpack_runner_adapter_registry.json"
    )
    adapter_registry_payload = _read_json(adapter_registry_path)
    adapter_registry_hash = sha256_canonical_json(adapter_registry_payload)

    matrix_registry_rel = "artifacts/agent_harness/v50/matrix/adapter_matrix.json"
    matrix_registry_path = root / matrix_registry_rel
    matrix_rows = [
        {
            "deployment_mode": "adeu_integrated",
            "adapter_id": "default",
            "runtime_id": "local_python_cli",
            "adapter_kind": "candidate_plan_passthrough",
        },
        {
            "deployment_mode": "standalone",
            "adapter_id": "default",
            "runtime_id": "local_python_cli",
            "adapter_kind": "candidate_plan_passthrough",
        },
    ]
    matrix_registry_hash_subject = {
        "lane_id_tuple": ["deployment_mode", "adapter_id", "runtime_id"],
        "declared_registry_only": True,
        "enabled_row_policy": "registry_is_enabled_only_disabled_rows_forbidden_non_v50",
        "tuple_order_policy": "lexicographic_over_deployment_mode_adapter_id_runtime_id",
        "deployment_mode_enum": ["adeu_integrated", "standalone"],
        "adapter_id_source_policy": "must_reference_declared_runner_adapter_registry_ids_only",
        "adapter_kind_policy": "candidate_plan_passthrough_only_non_v50_expansion_forbidden",
        "runtime_id_policy": "singleton_only_for_v50",
        "singleton_runtime_id": "local_python_cli",
        "runtime_id_source_policy": "contract_derived_only_no_host_environment_inference",
        "runtime_id_override_policy": (
            "explicit_override_must_equal_singleton_case_sensitive_before_adapter_execution_"
            "else_fail_closed"
        ),
        "lane_pairing_policy": (
            "for_each_declared_adapter_id_exactly_two_deployment_mode_rows_required_under_"
            "singleton_runtime_id"
        ),
        "lane_count_authority": "all_registry_rows_only_because_disabled_rows_are_forbidden",
        "source_runner_adapter_registry_path": _relative(root, adapter_registry_path),
        "source_runner_adapter_registry_hash": adapter_registry_hash,
        "rows": matrix_rows,
    }
    matrix_registry_hash = sha256_canonical_json(matrix_registry_hash_subject)
    _write_json(
        matrix_registry_path,
        {
            "schema": ADAPTER_MATRIX_SCHEMA,
            **matrix_registry_hash_subject,
            "matrix_registry_hash": matrix_registry_hash,
        },
    )

    verified_result_payload = _read_json(verified_result_path)
    matrix_report_rel = "artifacts/agent_harness/v50/matrix/adapter_matrix_parity_report.json"
    matrix_report_path = root / matrix_report_rel
    lane_rows = [
        {
            "deployment_mode": "adeu_integrated",
            "adapter_id": "default",
            "runtime_id": "local_python_cli",
            "taskpack_manifest_hash": verified_result_payload["taskpack_manifest_hash"],
            "candidate_change_plan_hash": verified_result_payload["candidate_change_plan_hash"],
            "runner_provenance_hash": verified_result_payload["runner_provenance_hash"],
            "packaging_manifest_path": (
                "artifacts/agent_harness/v50/matrix/adeu_integrated/packaging_manifest.json"
            ),
            "packaging_provenance_path": (
                "artifacts/agent_harness/v50/matrix/adeu_integrated/packaging_provenance.json"
            ),
            "canonical_subtree_hash": "a" * 64,
            "policy_equivalence_hash": "b" * 64,
        },
        {
            "deployment_mode": "standalone",
            "adapter_id": "default",
            "runtime_id": "local_python_cli",
            "taskpack_manifest_hash": verified_result_payload["taskpack_manifest_hash"],
            "candidate_change_plan_hash": verified_result_payload["candidate_change_plan_hash"],
            "runner_provenance_hash": verified_result_payload["runner_provenance_hash"],
            "packaging_manifest_path": (
                "artifacts/agent_harness/v50/matrix/standalone/packaging_manifest.json"
            ),
            "packaging_provenance_path": (
                "artifacts/agent_harness/v50/matrix/standalone/packaging_provenance.json"
            ),
            "canonical_subtree_hash": "a" * 64,
            "policy_equivalence_hash": "b" * 64,
        },
    ]
    pairwise_parity = [
        {
            "adapter_id": "default",
            "runtime_id": "local_python_cli",
            "deployment_modes": ["adeu_integrated", "standalone"],
            "taskpack_manifest_hash": verified_result_payload["taskpack_manifest_hash"],
            "candidate_change_plan_hash": verified_result_payload["candidate_change_plan_hash"],
            "canonical_subtree_exact_match": True,
            "policy_equivalence_exact_match": True,
        }
    ]
    matrix_report_hash_subject = {
        "matrix_registry_path": matrix_registry_rel,
        "matrix_registry_hash": matrix_registry_hash,
        "lane_id_tuple": ["deployment_mode", "adapter_id", "runtime_id"],
        "enabled_row_policy": "registry_is_enabled_only_disabled_rows_forbidden_non_v50",
        "declared_registry_only": True,
        "lexicographic_lane_order_enforced": True,
        "runtime_id_source_policy": "contract_derived_only_no_host_environment_inference",
        "runtime_id_host_inference_forbidden": True,
        "canonical_subtree_exact_match_required": True,
        "canonical_subtree_source_policy": (
            "existing_frozen_packaging_and_verifier_canonical_artifact_subject_family_only"
        ),
        "policy_equivalence_exact_match_required": True,
        "policy_equivalence_subject_keys_verified": [
            "allowlist_violations",
            "forbidden_effects_detected",
            "issue_code_set",
            "required_evidence_slots_filled",
        ],
        "policy_equivalence_value_shapes_verified": {
            "issue_code_set": "lexicographically_sorted_unique_string_list_canonical_form",
            "required_evidence_slots_filled": "boolean",
            "allowlist_violations": "lexicographically_sorted_unique_normalized_posix_path_list",
            "forbidden_effects_detected": "boolean",
        },
        "report_covers_all_declared_lanes": True,
        "lane_rows": lane_rows,
        "pairwise_parity": pairwise_parity,
    }
    matrix_report_hash = sha256_canonical_json(matrix_report_hash_subject)
    _write_json(
        matrix_report_path,
        {
            "schema": ADAPTER_MATRIX_PARITY_REPORT_SCHEMA,
            **matrix_report_hash_subject,
            "report_hash": matrix_report_hash,
        },
    )

    matrix_evidence_path = (
        root
        / "artifacts"
        / "agent_harness"
        / "v50"
        / "evidence_inputs"
        / "v34b_matrix_parity_evidence_v50.json"
    )
    _write_json(
        matrix_evidence_path,
        {
            "schema": "v34b_matrix_parity_evidence@1",
            "contract_source": (
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md#v34b_matrix_baseline_contract@1"
            ),
            "matrix_registry_path": matrix_registry_rel,
            "matrix_report_path": matrix_report_rel,
            "matrix_report_hash": matrix_report_hash,
            "lane_id_tuple": ["deployment_mode", "adapter_id", "runtime_id"],
            "enabled_row_policy": "registry_is_enabled_only_disabled_rows_forbidden_non_v50",
            "lane_count_authority": "all_registry_rows_only_because_disabled_rows_are_forbidden",
            "lane_count": 2,
            "deployment_modes_covered": ["adeu_integrated", "standalone"],
            "adapter_ids_covered": ["default"],
            "runtime_ids_covered": ["local_python_cli"],
            "singleton_runtime_id_enforced": True,
            "runtime_id_source_policy": "contract_derived_only_no_host_environment_inference",
            "runtime_id_host_inference_forbidden": True,
            "declared_registry_only": True,
            "lexicographic_lane_order_enforced": True,
            "canonical_subtree_exact_match_required": True,
            "canonical_subtree_source_policy": (
                "existing_frozen_packaging_and_verifier_canonical_artifact_subject_family_only"
            ),
            "policy_equivalence_exact_match_required": True,
            "policy_equivalence_subject_keys_verified": [
                "allowlist_violations",
                "forbidden_effects_detected",
                "issue_code_set",
                "required_evidence_slots_filled",
            ],
            "policy_equivalence_value_shapes_verified": {
                "issue_code_set": "lexicographically_sorted_unique_string_list_canonical_form",
                "required_evidence_slots_filled": "boolean",
                "allowlist_violations": (
                    "lexicographically_sorted_unique_normalized_posix_path_list"
                ),
                "forbidden_effects_detected": "boolean",
            },
            "report_covers_all_declared_lanes": True,
            "verification_passed": True,
            "metric_key_cardinality": 80,
            "metric_key_exact_set_equal_v49": True,
            "notes": "v50 Y2 closeout evidence fixture.",
        },
    )
    return matrix_registry_path, matrix_report_path, matrix_evidence_path


def _seed_v51_policy_recompute_evidence_payload(
    root: Path,
    *,
    verified_result_path: Path,
) -> Path:
    verified_result_payload = _read_json(verified_result_path)
    policy_recompute_result_path = (
        root
        / DEFAULT_POLICY_RECOMPUTE_OUTPUT_ROOT
        / (
            f"{verified_result_payload['taskpack_manifest_hash']}_"
            f"{verified_result_payload['candidate_change_plan_hash']}.json"
        )
    )
    policy_recompute_result_payload = _read_json(policy_recompute_result_path)
    evidence_path = (
        root
        / "artifacts"
        / "agent_harness"
        / "v51"
        / "evidence_inputs"
        / "v34c_policy_recompute_evidence_v51.json"
    )
    _write_json(
        evidence_path,
        {
            "schema": "v34c_policy_recompute_evidence@1",
            "contract_source": (
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md#v34c_policy_recompute_contract@1"
            ),
            "recompute_entrypoint": SHARED_RECOMPUTE_ENGINE,
            "shared_recompute_engine_used": SHARED_RECOMPUTE_ENGINE,
            "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
            "policy_recompute_result_path": _relative(root, policy_recompute_result_path),
            "policy_recompute_result_hash": policy_recompute_result_payload["result_hash"],
            "comparison_subject_fields": ["passed", "issues", "exit_status"],
            "exit_status_subject_policy": (
                "runner_policy_verdict_status_under_frozen_validator_scope_"
                "not_verifier_process_exit_code"
            ),
            "issue_tuple_fields": ["issue_code", "target_path", "hunk_index"],
            "issue_tuple_order_policy": "lexicographic_over_issue_code_target_path_hunk_index",
            "issues_representation_policy": (
                "lexicographically_sorted_unique_issue_tuple_list_with_repo_relative_"
                "posix_target_paths"
            ),
            "duplicate_issue_tuples_forbidden": True,
            "allowed_issue_codes": [
                "allowlist_violation",
                "dry_run_subprocess_execution_detected",
                "forbidden_operation_kind",
                "forbidden_path_violation",
                "model_suggested_command_execution_detected",
            ],
            "allowed_issue_codes_closed_exact": True,
            "candidate_change_plan_binding_policy": (
                "recompute_binds_to_runner_recorded_canonical_candidate_change_plan_hash_"
                "runner_result_dry_run_supplies_execution_mode_only"
            ),
            "runner_policy_failure_input_materialization_required": True,
            "runner_reason_line_range_non_authoritative": True,
            "mismatch_fail_closed": True,
            "exact_match_requires_empty_deltas": True,
            "policy_recompute_result_emitted": True,
            "typed_diff_summary_emitted": True,
            "success_class_verification_result_forbidden_on_mismatch": True,
            "verification_passed": True,
            "metric_key_cardinality": 80,
            "metric_key_exact_set_equal_v50": True,
            "notes": "v51 Z2 closeout evidence fixture.",
        },
    )
    return evidence_path


def _seed_v52_retry_context_evidence_payload(
    root: Path,
    *,
    taskpack_dir: Path,
    verified_result_path: Path,
) -> Path:
    adapter_registry_path = (
        root / "artifacts" / "agent_harness" / "v45" / "taskpack_runner_adapter_registry.json"
    )
    blocked_rel = "apps/api/v52_retry_context_fixture.txt"
    candidate_path = _write_candidate_change_plan(
        root,
        operations=[
            {
                "path": blocked_rel,
                "operation_kind": "create",
                "unified_diff": _create_diff(rel_path=blocked_rel, content="blocked"),
            }
        ],
        proposed_commands=[],
        artifact_rel_path="artifacts/agent_harness/v52/candidate_change_plan_retry_context.json",
    )

    with pytest.raises(TaskpackRunnerError) as exc_info:
        _run_taskpack_signed(
            root,
            taskpack_dir=taskpack_dir,
            adapter_registry_path=adapter_registry_path,
            adapter_id="default",
            candidate_change_plan_path=candidate_path,
            dry_run=True,
        )

    details = json.loads(str(exc_info.value))["details"]
    runner_result_path = _write_runner_result_from_error_details(root, details=details)
    retry_context_artifacts = generate_retry_context(
        candidate_change_plan_path=_relative(root, candidate_path),
        runner_result_path=_relative(root, runner_result_path),
        retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
        repo_root_path=root,
    )
    retry_context_payload = _read_json(retry_context_artifacts.result_path)
    sanitization_profile_payload = _read_json(retry_context_artifacts.sanitization_profile_path)
    verified_result_payload = _read_json(verified_result_path)
    assert (
        retry_context_payload["taskpack_manifest_hash"]
        == verified_result_payload["taskpack_manifest_hash"]
    )

    evidence_path = (
        root
        / "artifacts"
        / "agent_harness"
        / "v52"
        / "evidence_inputs"
        / "v34d_retry_context_evidence_v52.json"
    )
    _write_json(
        evidence_path,
        {
            "schema": "v34d_retry_context_evidence@1",
            "contract_source": (
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md#v34d_retry_context_contract@1"
            ),
            "feeder_entrypoint": "python -m adeu_agent_harness.retry_context",
            "shared_feeder_engine_used": SHARED_FEEDER_ENGINE,
            "shared_feeder_engine_identifier": SHARED_FEEDER_ENGINE_IDENTIFIER,
            "retry_context_feeder_result_path": _relative(
                root, retry_context_artifacts.result_path
            ),
            "retry_context_feeder_result_hash": retry_context_payload["result_hash"],
            "sanitization_profile_path": _relative(
                root, retry_context_artifacts.sanitization_profile_path
            ),
            "sanitization_profile_hash": sanitization_profile_payload["profile_hash"],
            "source_rejection_diagnostic_schema": "candidate_change_plan_rejection_diagnostic@1",
            "policy_source_closed_inherited_surface": True,
            "runner_result_semantic_input_forbidden": True,
            "advisory_only_non_authoritative": True,
            "automatic_retry_dispatch_forbidden": True,
            "downstream_diagnostic_aggregation_forbidden": True,
            "policy_success_explicit_request_without_diagnostic_fails_closed": True,
            "raw_repo_file_content_forbidden": True,
            "duplicate_issue_tuples_forbidden": True,
            "excerpt_bounds_enforced": True,
            "overflow_policy": OVERFLOW_POLICY,
            "missing_excerpt_source_policy": MISSING_EXCERPT_SOURCE_POLICY,
            "total_output_bound_enforced": True,
            "control_marker_neutralization_enforced": True,
            "deterministic_issue_order_enforced": True,
            "verification_passed": True,
            "verification_passed_policy": RETRY_CONTEXT_VERIFICATION_PASSED_POLICY,
            "success_path_absence_without_request_allowed": True,
            "metric_key_cardinality": 80,
            "metric_key_exact_set_equal_v51": True,
            "notes": "v52 A2 closeout evidence fixture.",
        },
    )
    return evidence_path


def _seed_v53_attestation_evidence_payload(
    root: Path,
    *,
    taskpack_dir: Path,
    verified_result_path: Path,
    diagnostic_registry_rel: str,
) -> Path:
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)
    verified_result_payload = _read_json(verified_result_path)
    candidate_change_plan_path = root / verified_result_payload["verified_artifacts"][
        "candidate_change_plan_path"
    ]
    runner_result_path = root / verified_result_payload["verified_artifacts"]["runner_result_path"]
    runner_provenance_path = root / verified_result_payload["verified_artifacts"][
        "runner_provenance_path"
    ]
    provider_attestation_input_path = (
        root
        / "artifacts"
        / "agent_harness"
        / "v53"
        / "attested"
        / "provider_attestation_input.json"
    )
    _write_json(
        provider_attestation_input_path,
        {
            "schema": "deterministic_test_enclave_attestation_input@1",
            "provider_id": PROVIDER_ID,
            "attestation_key_id": "key_ed25519_test",
            "algorithm": "ed25519",
            "verification_reference_time_utc": signing.verification_reference_time_utc,
            "taskpack_manifest_hash": verified_result_payload["taskpack_manifest_hash"],
            "candidate_change_plan_hash": verified_result_payload["candidate_change_plan_hash"],
            "runner_provenance_hash": sha256_canonical_json(_read_json(runner_provenance_path)),
            "verified_result_hash": verified_result_payload["verified_result_hash"],
            "attestation_verified": True,
            "opaque_provider_evidence": "raw-provider-proof::deterministic_test_enclave",
        },
    )

    attestation_artifacts = validate_attested_verification(
        taskpack_dir=_relative(root, taskpack_dir),
        candidate_change_plan_path=_relative(root, candidate_change_plan_path),
        runner_result_path=_relative(root, runner_result_path),
        runner_provenance_path=_relative(root, runner_provenance_path),
        attested_verified_result_path=_relative(root, verified_result_path),
        provider_attestation_input_path=_relative(root, provider_attestation_input_path),
        attestation_output_root=DEFAULT_ATTESTATION_OUTPUT_ROOT,
        local_verification_output_root=ATTESTATION_LOCAL_VERIFICATION_OUTPUT_ROOT,
        local_policy_recompute_output_root=ATTESTATION_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT,
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
        **signing.as_kwargs(),
    )
    remote_attestation_payload = _read_json(
        attestation_artifacts.remote_enclave_attestation_path
    )
    assert remote_attestation_payload["schema"] == REMOTE_ENCLAVE_ATTESTATION_SCHEMA
    attestation_verification_payload = _read_json(
        attestation_artifacts.attestation_verification_result_path
    )

    evidence_path = (
        root
        / "artifacts"
        / "agent_harness"
        / "v53"
        / "evidence_inputs"
        / "v34e_attestation_evidence_v53.json"
    )
    _write_json(
        evidence_path,
        {
            "schema": "v34e_attestation_evidence@1",
            "contract_source": (
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS53.md#v34e_attested_verifier_contract@1"
            ),
            "attestation_entrypoint": "python -m adeu_agent_harness.attestation",
            "shared_attestation_validator_used": SHARED_ATTESTATION_VALIDATOR,
            "shared_attestation_validator_identifier": SHARED_ATTESTATION_VALIDATOR_IDENTIFIER,
            "shared_attestation_validator_identifier_policy": (
                SHARED_ATTESTATION_VALIDATOR_IDENTIFIER_POLICY
            ),
            "local_verifier_entrypoint": attestation_verification_payload[
                "local_verifier_entrypoint"
            ],
            "remote_enclave_attestation_path": _relative(
                root, attestation_artifacts.remote_enclave_attestation_path
            ),
            "remote_enclave_attestation_hash": (
                attestation_artifacts.remote_enclave_attestation_hash
            ),
            "attested_verified_result_path": _relative(
                root, attestation_artifacts.attested_verified_result_path
            ),
            "attested_verified_result_hash": attestation_artifacts.attested_verified_result_hash,
            "local_verified_result_path": _relative(
                root, attestation_artifacts.local_verified_result_path
            ),
            "local_verified_result_hash": attestation_artifacts.local_verified_result_hash,
            "attestation_verification_result_path": _relative(
                root, attestation_artifacts.attestation_verification_result_path
            ),
            "attestation_verification_result_hash": (
                attestation_artifacts.attestation_verification_result_hash
            ),
            "provider_id": PROVIDER_ID,
            "provider_id_closed_singleton_enforced": True,
            "provider_id_comparison_policy": PROVIDER_ID_COMPARISON_POLICY,
            "attestation_trust_anchor_registry_reused": True,
            "runner_provenance_hash_policy": ATTESTATION_RUNNER_PROVENANCE_HASH_POLICY,
            "attestation_verified_required": True,
            "input_mode_artifact_ingestion_only": True,
            "attested_verified_result_schema_validated": True,
            "current_local_verification_recomputed": True,
            "current_local_verification_materialization_failure_fails_closed": True,
            "local_equivalence_required": True,
            "local_equivalence_subject_fields_verified": list(
                LOCAL_EQUIVALENCE_SUBJECT_FIELDS
            ),
            "local_equivalence_binding_fields_verified": list(
                LOCAL_EQUIVALENCE_BINDING_FIELDS
            ),
            "local_equivalence_subject_policy": LOCAL_EQUIVALENCE_SUBJECT_POLICY,
            "local_equivalence_verified": True,
            "opaque_provider_evidence_hash_audit_only": True,
            "normalized_claim_conflicts_forbidden": True,
            "remote_transport_or_job_dispatch_forbidden": True,
            "deployment_mode_expansion_forbidden": True,
            "verification_passed": True,
            "verification_passed_policy": ATTESTATION_VERIFICATION_PASSED_POLICY,
            "metric_key_cardinality": 80,
            "metric_key_exact_set_equal_v52": True,
            "notes": "v53 B2 closeout evidence fixture.",
        },
    )
    return evidence_path


def _write_evidence_with_seeded_payloads(
    *,
    root: Path,
    taskpack_dir: Path,
    verified_result_path: Path,
    diagnostic_registry_rel: str,
    matrix_parity_evidence_path: Path | None = None,
    policy_recompute_evidence_path: Path | None = None,
    retry_context_evidence_path: Path | None = None,
    attestation_evidence_path: Path | None = None,
    evidence_output_root: str = "artifacts/agent_harness/v46/evidence",
):
    runtime_path, continuity_path, handoff_path = _seed_u2_evidence_payloads(root)
    return write_closeout_evidence(
        taskpack_dir=_relative(root, taskpack_dir),
        verified_result_path=_relative(root, verified_result_path),
        runtime_observability_comparison_path=_relative(root, runtime_path),
        metric_key_continuity_assertion_path=_relative(root, continuity_path),
        handoff_completion_evidence_path=_relative(root, handoff_path),
        matrix_parity_evidence_path=(
            None
            if matrix_parity_evidence_path is None
            else _relative(root, matrix_parity_evidence_path)
        ),
        policy_recompute_evidence_path=(
            None
            if policy_recompute_evidence_path is None
            else _relative(root, policy_recompute_evidence_path)
        ),
        retry_context_evidence_path=(
            None
            if retry_context_evidence_path is None
            else _relative(root, retry_context_evidence_path)
        ),
        attestation_evidence_path=(
            None
            if attestation_evidence_path is None
            else _relative(root, attestation_evidence_path)
        ),
        evidence_output_root=evidence_output_root,
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
    )


def _reverify_with_current_taskpack(
    *,
    root: Path,
    taskpack_dir: Path,
    diagnostic_registry_rel: str,
) -> Path:
    candidate_path = root / "artifacts/agent_harness/v46/candidate_change_plan.json"
    adapter_registry_path = (
        root / "artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json"
    )
    run_result = _run_taskpack_signed(
        root,
        taskpack_dir=taskpack_dir,
        adapter_registry_path=adapter_registry_path,
        adapter_id="default",
        candidate_change_plan_path=candidate_path,
        dry_run=True,
    )
    runner_result_path = _write_runner_result_artifact(root, run_result=run_result)
    verify_result = _verify_taskpack_run_signed(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=candidate_path,
        runner_result_path=runner_result_path,
        runner_provenance_path=run_result.provenance_path,
        policy_rejection_diagnostics_path=None,
        verification_output_root="artifacts/agent_harness/v46/verification",
        diagnostic_registry_path=diagnostic_registry_rel,
    )
    return verify_result.verification_result_path


def test_verify_taskpack_run_emits_deterministic_verified_result(tmp_path: Path) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    before = verified_result_path.read_bytes()

    verified_payload = _read_json(verified_result_path)
    assert verified_payload["schema"] == VERIFICATION_RESULT_SCHEMA
    assert verified_payload["verification_result"]["cross_checks"] == [
        "taskpack_manifest_hash_match",
        "candidate_change_plan_hash_match",
        "policy_validation_result_consistency",
        "exit_status_consistency",
    ]

    second = _verify_taskpack_run_signed(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
        runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
        runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
        policy_rejection_diagnostics_path=None,
        verification_output_root="artifacts/agent_harness/v46/verification",
        diagnostic_registry_path=diagnostic_registry_rel,
    )

    assert second.verification_result_path == verified_result_path
    assert verified_result_path.read_bytes() == before
    recompute_payload = _read_json(second.policy_recompute_result_path)
    assert recompute_payload["schema"] == POLICY_RECOMPUTE_RESULT_SCHEMA
    assert recompute_payload["shared_recompute_engine"] == SHARED_RECOMPUTE_ENGINE
    assert recompute_payload["typed_diff_summary"] == {
        "exact_match": True,
        "mismatch_fields": [],
        "runner_only_issues": [],
        "recompute_only_issues": [],
    }
    assert second.policy_recompute_result_hash == recompute_payload["result_hash"]

    recompute_before = second.policy_recompute_result_path.read_bytes()
    third = _verify_taskpack_run_signed(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
        runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
        runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
        policy_rejection_diagnostics_path=None,
        verification_output_root="artifacts/agent_harness/v46/verification",
        diagnostic_registry_path=diagnostic_registry_rel,
    )
    assert third.policy_recompute_result_path == second.policy_recompute_result_path
    assert third.policy_recompute_result_path.read_bytes() == recompute_before


def test_verify_taskpack_run_emits_policy_recompute_result_on_runner_policy_failure(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_path,
        runner_result_path,
        runner_provenance_path,
        rejection_diagnostic_path,
        _blocked_rel,
        diagnostic_registry_rel,
    ) = _prepare_runner_policy_failure(tmp_path)

    verify_result = _verify_taskpack_run_signed(
        root,
        taskpack_dir=taskpack_dir,
        candidate_change_plan_path=candidate_path,
        runner_result_path=runner_result_path,
        runner_provenance_path=runner_provenance_path,
        policy_rejection_diagnostics_path=rejection_diagnostic_path,
        verification_output_root="artifacts/agent_harness/v46/verification",
        diagnostic_registry_path=diagnostic_registry_rel,
    )

    recompute_payload = _read_json(verify_result.policy_recompute_result_path)
    assert recompute_payload["schema"] == POLICY_RECOMPUTE_RESULT_SCHEMA
    assert recompute_payload["runner_outcome"]["passed"] is False
    assert recompute_payload["runner_outcome"]["exit_status"] == "policy_validation_failed"
    assert recompute_payload["typed_diff_summary"]["exact_match"] is True


def test_verify_taskpack_run_fails_closed_on_policy_recompute_mismatch_after_emission(
    tmp_path: Path,
) -> None:
    (
        root,
        taskpack_dir,
        candidate_path,
        runner_result_path,
        runner_provenance_path,
        rejection_diagnostic_path,
        blocked_rel,
        diagnostic_registry_rel,
    ) = _prepare_runner_policy_failure(tmp_path)

    runner_provenance_payload = _read_json(runner_provenance_path)
    runner_provenance_payload["policy_validation_result"] = {
        "passed": False,
        "issues": [
            {
                "issue_code": "forbidden_operation_kind",
                "target_path": blocked_rel,
                "hunk_index": 0,
            }
        ],
    }
    runner_provenance_payload["provenance_hash"] = sha256_canonical_json(
        {
            "taskpack_manifest_hash": runner_provenance_payload["taskpack_manifest_hash"],
            "adapter_id": runner_provenance_payload["adapter_id"],
            "candidate_change_plan_hash": runner_provenance_payload["candidate_change_plan_hash"],
            "policy_validation_result": runner_provenance_payload["policy_validation_result"],
            "exit_status": runner_provenance_payload["exit_status"],
        }
    )
    _write_json(runner_provenance_path, runner_provenance_payload)

    runner_result_payload = _read_json(runner_result_path)
    runner_result_payload["provenance_hash"] = runner_provenance_payload["provenance_hash"]
    _write_json(runner_result_path, runner_result_payload)

    verification_output_root = "artifacts/agent_harness/v51/verification_mismatch_case"
    with pytest.raises(TaskpackVerifierError) as exc_info:
        _verify_taskpack_run_signed(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=candidate_path,
            runner_result_path=runner_result_path,
            runner_provenance_path=runner_provenance_path,
            policy_rejection_diagnostics_path=rejection_diagnostic_path,
            verification_output_root=verification_output_root,
            diagnostic_registry_path=diagnostic_registry_rel,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4605"
    recompute_payload = _read_json(Path(payload["details"]["policy_recompute_result_path"]))
    assert recompute_payload["typed_diff_summary"]["exact_match"] is False
    assert recompute_payload["typed_diff_summary"]["mismatch_fields"] == ["issues"]
    assert recompute_payload["typed_diff_summary"]["runner_only_issues"] == [
        {
            "issue_code": "forbidden_operation_kind",
            "target_path": blocked_rel,
            "hunk_index": 0,
        }
    ]
    assert recompute_payload["typed_diff_summary"]["recompute_only_issues"] == [
        {
            "issue_code": "allowlist_violation",
            "target_path": blocked_rel,
            "hunk_index": 0,
        },
        {
            "issue_code": "forbidden_path_violation",
            "target_path": blocked_rel,
            "hunk_index": 0,
        },
    ]
    verification_result_path = (
        root
        / verification_output_root
        / (
            f"{recompute_payload['taskpack_manifest_hash']}_"
            f"{recompute_payload['candidate_change_plan_hash']}.json"
        )
    )
    assert not verification_result_path.exists()


def test_verify_taskpack_run_translates_runner_errors_during_policy_recompute_generation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    verified_payload = _read_json(verified_result_path)

    def _raise_runner_error(*, path: Path, payload_bytes: bytes) -> Any:
        del path, payload_bytes
        raise TaskpackRunnerError(
            code="AHK1004",
            message="forced recompute input failure",
            details={"source": "test"},
        )

    monkeypatch.setattr(
        verifier_mod,
        "_load_allowlist_payload_from_bytes",
        _raise_runner_error,
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _verify_taskpack_run_signed(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
            runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
            runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
            policy_rejection_diagnostics_path=None,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4603"
    assert payload["details"]["runner_error_code"] == "AHK1004"


def test_verify_taskpack_run_fails_closed_on_hash_mismatch(tmp_path: Path) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    verified_payload = _read_json(verified_result_path)
    runner_result_path = root / verified_payload["verified_artifacts"]["runner_result_path"]
    candidate_path = root / verified_payload["verified_artifacts"]["candidate_change_plan_path"]
    runner_provenance_path = root / verified_payload["verified_artifacts"]["runner_provenance_path"]

    runner_result_payload = _read_json(runner_result_path)
    runner_result_payload["candidate_change_plan_hash"] = "f" * 64
    _write_json(runner_result_path, runner_result_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _verify_taskpack_run_signed(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=candidate_path,
            runner_result_path=runner_result_path,
            runner_provenance_path=runner_provenance_path,
            policy_rejection_diagnostics_path=None,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4604"
    rejection_path = Path(payload["details"]["rejection_diagnostic_path"])
    rejection_payload = _read_json(rejection_path)
    assert rejection_payload["schema"] == "v33c_verifier_rejection_diagnostic@1"
    assert rejection_payload["issues"][0]["issue_code"] == "AHK4604"


def test_verify_taskpack_run_fails_closed_on_taskpack_snapshot_drift_after_preflight(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    diagnostic_registry_rel = _seed_diagnostic_registry(root)
    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)

    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/v46_snapshot_drift_fixture.txt"
    fixture_path = root / rel_path
    _write(fixture_path, "before\n")
    candidate_path = _write_candidate_change_plan(root, rel_path=rel_path)
    run_result = _run_taskpack_signed(
        root,
        taskpack_dir=taskpack_dir,
        adapter_registry_path=adapter_registry_path,
        adapter_id="default",
        candidate_change_plan_path=candidate_path,
        dry_run=True,
    )
    assert fixture_path.read_text(encoding="utf-8") == "before\n"
    runner_result_path = _write_runner_result_artifact(root, run_result=run_result)

    taskpack_markdown_path = taskpack_dir / "TASKPACK.md"
    taskpack_markdown_path.write_text(
        taskpack_markdown_path.read_text(encoding="utf-8") + "\npost-preflight drift\n",
        encoding="utf-8",
    )
    _sync_manifest_component_hash(taskpack_dir, relative_path="TASKPACK.md")

    with pytest.raises(TaskpackVerifierError) as exc_info:
        verify_taskpack_run(
            taskpack_dir=_relative(root, taskpack_dir),
            candidate_change_plan_path=_relative(root, candidate_path),
            runner_result_path=_relative(root, runner_result_path),
            runner_provenance_path=_relative(root, run_result.provenance_path),
            policy_rejection_diagnostics_path=None,
            signature_verification_result_path=signing.signature_verification_result_path,
            signature_envelope_path=signing.signature_envelope_path,
            trust_anchor_registry_path=signing.trust_anchor_registry_path,
            verification_reference_time_utc=signing.verification_reference_time_utc,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )
    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4604"
    assert payload["details"]["signing_error_code"] == "AHK4804"


def test_verify_taskpack_run_fails_closed_on_missing_taskpack_component_after_preflight(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    diagnostic_registry_rel = _seed_diagnostic_registry(root)
    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)
    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/v46_compile_drift_fixture.txt"
    fixture_path = root / rel_path
    _write(fixture_path, "before\n")
    candidate_path = _write_candidate_change_plan(root, rel_path=rel_path)
    run_result = run_taskpack(
        taskpack_dir=_relative(root, taskpack_dir),
        adapter_registry_path=_relative(root, adapter_registry_path),
        adapter_id="default",
        candidate_change_plan_path=_relative(root, candidate_path),
        dry_run=True,
        repo_root_path=root,
        **signing.as_kwargs(),
    )
    assert fixture_path.read_text(encoding="utf-8") == "before\n"
    runner_result_path = _write_runner_result_artifact(root, run_result=run_result)
    (taskpack_dir / "ALLOWLIST.json").unlink()

    with pytest.raises(TaskpackVerifierError) as exc_info:
        verify_taskpack_run(
            taskpack_dir=_relative(root, taskpack_dir),
            candidate_change_plan_path=_relative(root, candidate_path),
            runner_result_path=_relative(root, runner_result_path),
            runner_provenance_path=_relative(root, run_result.provenance_path),
            policy_rejection_diagnostics_path=None,
            repo_root_path=root,
            **signing.as_kwargs(),
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
        )
    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4603"
    assert payload["details"]["signing_error_code"] == "AHK0017"


def test_write_closeout_evidence_emits_deterministic_bundle_and_provenance(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    first = _write_evidence_with_seeded_payloads(
        root=root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    second = _write_evidence_with_seeded_payloads(
        root=root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )

    assert first.evidence_bundle_path.read_bytes() == second.evidence_bundle_path.read_bytes()
    assert (
        first.verifier_provenance_path.read_bytes()
        == second.verifier_provenance_path.read_bytes()
    )

    bundle_payload = _read_json(first.evidence_bundle_path)
    assert bundle_payload["schema"] == EVIDENCE_BUNDLE_SCHEMA
    assert [block["slot_id"] for block in bundle_payload["ordered_evidence_blocks"]] == [
        "metric_key_continuity_assertion",
        "runtime_observability_comparison",
        "v34a_handoff_completion_evidence",
    ]
    recomputed_bundle_hash = sha256_canonical_json(
        {
            "taskpack_manifest_hash": bundle_payload["taskpack_manifest_hash"],
            "ordered_evidence_blocks": bundle_payload["ordered_evidence_blocks"],
            "ordered_rejection_diagnostics_optional": bundle_payload[
                "ordered_rejection_diagnostics_optional"
            ],
        }
    )
    assert bundle_payload["evidence_bundle_hash"] == recomputed_bundle_hash

    provenance_payload = _read_json(first.verifier_provenance_path)
    assert provenance_payload["schema"] == VERIFIER_PROVENANCE_SCHEMA
    assert provenance_payload["evidence_bundle_hash"] == bundle_payload["evidence_bundle_hash"]


def test_write_closeout_evidence_emits_matrix_parity_block_when_required(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )

    result = _write_evidence_with_seeded_payloads(
        root=root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
        diagnostic_registry_rel=diagnostic_registry_rel,
        matrix_parity_evidence_path=matrix_evidence_path,
        evidence_output_root="artifacts/agent_harness/v50/evidence",
    )

    bundle_payload = _read_json(result.evidence_bundle_path)
    assert [block["slot_id"] for block in bundle_payload["ordered_evidence_blocks"]] == [
        "metric_key_continuity_assertion",
        "runtime_observability_comparison",
        "v34a_handoff_completion_evidence",
        "v34b_matrix_parity_evidence",
    ]
    matrix_block = next(
        block
        for block in bundle_payload["ordered_evidence_blocks"]
        if block["slot_id"] == "v34b_matrix_parity_evidence"
    )
    assert matrix_block["payload"]["report_covers_all_declared_lanes"] is True
    assert matrix_block["payload"]["matrix_report_hash"] == _read_json(
        root / matrix_block["payload"]["matrix_report_path"]
    )["report_hash"]


def test_write_closeout_evidence_emits_policy_recompute_block_when_required(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )

    result = _write_evidence_with_seeded_payloads(
        root=root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
        diagnostic_registry_rel=diagnostic_registry_rel,
        matrix_parity_evidence_path=matrix_evidence_path,
        policy_recompute_evidence_path=policy_recompute_evidence_path,
        evidence_output_root="artifacts/agent_harness/v51/evidence_matrix_and_recompute",
    )

    bundle_payload = _read_json(result.evidence_bundle_path)
    assert [block["slot_id"] for block in bundle_payload["ordered_evidence_blocks"]] == [
        "metric_key_continuity_assertion",
        "runtime_observability_comparison",
        "v34a_handoff_completion_evidence",
        "v34b_matrix_parity_evidence",
        "v34c_policy_recompute_evidence",
    ]
    recompute_block = next(
        block
        for block in bundle_payload["ordered_evidence_blocks"]
        if block["slot_id"] == "v34c_policy_recompute_evidence"
    )
    assert recompute_block["payload"]["schema"] == "v34c_policy_recompute_evidence@1"


def test_write_closeout_evidence_emits_retry_context_block_when_required(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    _add_retry_context_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )
    retry_context_evidence_path = _seed_v52_retry_context_evidence_payload(
        root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
    )

    result = _write_evidence_with_seeded_payloads(
        root=root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
        diagnostic_registry_rel=diagnostic_registry_rel,
        matrix_parity_evidence_path=matrix_evidence_path,
        policy_recompute_evidence_path=policy_recompute_evidence_path,
        retry_context_evidence_path=retry_context_evidence_path,
        evidence_output_root="artifacts/agent_harness/v52/evidence_full_closeout",
    )

    bundle_payload = _read_json(result.evidence_bundle_path)
    assert [block["slot_id"] for block in bundle_payload["ordered_evidence_blocks"]] == [
        "metric_key_continuity_assertion",
        "runtime_observability_comparison",
        "v34a_handoff_completion_evidence",
        "v34b_matrix_parity_evidence",
        "v34c_policy_recompute_evidence",
        "v34d_retry_context_evidence",
    ]
    retry_context_block = next(
        block
        for block in bundle_payload["ordered_evidence_blocks"]
        if block["slot_id"] == "v34d_retry_context_evidence"
    )
    assert retry_context_block["payload"]["schema"] == "v34d_retry_context_evidence@1"
    assert (
        retry_context_block["payload"]["shared_feeder_engine_identifier"]
        == SHARED_FEEDER_ENGINE_IDENTIFIER
    )
    retry_context_payload = _read_json(
        root / retry_context_block["payload"]["retry_context_feeder_result_path"]
    )
    assert retry_context_payload["schema"] == RETRY_CONTEXT_FEEDER_RESULT_SCHEMA


def test_write_closeout_evidence_emits_attestation_block_when_required(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    _add_retry_context_slot(taskpack_dir)
    _add_attestation_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )
    retry_context_evidence_path = _seed_v52_retry_context_evidence_payload(
        root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
    )
    attestation_evidence_path = _seed_v53_attestation_evidence_payload(
        root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )

    result = _write_evidence_with_seeded_payloads(
        root=root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
        diagnostic_registry_rel=diagnostic_registry_rel,
        matrix_parity_evidence_path=matrix_evidence_path,
        policy_recompute_evidence_path=policy_recompute_evidence_path,
        retry_context_evidence_path=retry_context_evidence_path,
        attestation_evidence_path=attestation_evidence_path,
        evidence_output_root="artifacts/agent_harness/v53/evidence_full_closeout",
    )

    bundle_payload = _read_json(result.evidence_bundle_path)
    assert [block["slot_id"] for block in bundle_payload["ordered_evidence_blocks"]] == [
        "metric_key_continuity_assertion",
        "runtime_observability_comparison",
        "v34a_handoff_completion_evidence",
        "v34b_matrix_parity_evidence",
        "v34c_policy_recompute_evidence",
        "v34d_retry_context_evidence",
        "v34e_attestation_evidence",
    ]
    attestation_block = next(
        block
        for block in bundle_payload["ordered_evidence_blocks"]
        if block["slot_id"] == "v34e_attestation_evidence"
    )
    assert attestation_block["payload"]["schema"] == "v34e_attestation_evidence@1"
    assert (
        attestation_block["payload"]["shared_attestation_validator_identifier"]
        == SHARED_ATTESTATION_VALIDATOR_IDENTIFIER
    )
    remote_attestation_payload = _read_json(
        root / attestation_block["payload"]["remote_enclave_attestation_path"]
    )
    assert remote_attestation_payload["schema"] == REMOTE_ENCLAVE_ATTESTATION_SCHEMA


def test_write_closeout_evidence_fails_closed_with_no_partial_evidence_emission(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    verified_payload = _read_json(verified_result_path)
    verified_payload["verification_result"]["passed"] = False
    verified_payload["verification_result"]["issues"] = ["forced_failure"]
    _write_json(verified_result_path, verified_payload)

    runtime_path = root / "artifacts" / "stop_gate" / "runtime_observability_comparison_v46.json"
    _write_json(runtime_path, {"schema": "runtime_observability_comparison@1"})
    continuity_path = root / "artifacts" / "stop_gate" / "metric_key_continuity_assertion_v46.json"
    _write_json(continuity_path, {"schema": "metric_key_continuity_assertion@1"})
    handoff_path = root / "artifacts" / "stop_gate" / "v34a_handoff_completion_evidence_v49.json"
    _write_json(handoff_path, {"schema": "v34a_handoff_completion_evidence@1"})

    evidence_output_rel = "artifacts/agent_harness/v46/evidence_failure_case"
    evidence_output_path = root / evidence_output_rel

    with pytest.raises(TaskpackVerifierError) as exc_info:
        write_closeout_evidence(
            taskpack_dir=_relative(root, taskpack_dir),
            verified_result_path=_relative(root, verified_result_path),
            runtime_observability_comparison_path=_relative(root, runtime_path),
            metric_key_continuity_assertion_path=_relative(root, continuity_path),
            handoff_completion_evidence_path=_relative(root, handoff_path),
            evidence_output_root=evidence_output_rel,
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4612"
    assert "rejection_diagnostic_path" in payload["details"]
    assert not evidence_output_path.exists() or not list(evidence_output_path.glob("*.json"))


def test_verifier_entrypoints_are_present() -> None:
    assert callable(verifier_mod.verify_taskpack_run)
    assert callable(verifier_mod.main)
    assert callable(evidence_writer_mod.write_closeout_evidence)
    assert callable(evidence_writer_mod.main)


def test_verifier_kernel_has_no_apps_api_imports() -> None:
    module_root = (
        repo_root(anchor=Path(__file__))
        / "packages"
        / "adeu_agent_harness"
        / "src"
        / "adeu_agent_harness"
    )
    targets = [
        module_root / "_v46_verifier_common.py",
        module_root / "verify_taskpack_run.py",
        module_root / "write_closeout_evidence.py",
    ]
    violations: list[str] = []
    for path in targets:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name.startswith("apps.api"):
                        violations.append(f"{path}:{alias.name}")
            if isinstance(node, ast.ImportFrom):
                module = node.module or ""
                if module.startswith("apps.api"):
                    violations.append(f"{path}:{module}")
    assert not violations, f"direct apps/api imports found: {violations}"


def test_verify_taskpack_run_fails_closed_on_deterministic_env_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    verified_payload = _read_json(verified_result_path)
    monkeypatch.setenv("TZ", "Europe/Bucharest")

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _verify_taskpack_run_signed(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
            runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
            runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
            policy_rejection_diagnostics_path=None,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4603"
    assert payload["details"]["required_deterministic_env"]["TZ"] == "UTC"


def test_verify_taskpack_run_fails_closed_on_runner_result_schema_drift(tmp_path: Path) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    verified_payload = _read_json(verified_result_path)
    runner_result_path = root / verified_payload["verified_artifacts"]["runner_result_path"]
    runner_payload = _read_json(runner_result_path)
    runner_payload["schema"] = "taskpack_runner_result@999"
    _write_json(runner_result_path, runner_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _verify_taskpack_run_signed(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
            runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
            runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
            policy_rejection_diagnostics_path=None,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4602"


def test_verify_taskpack_run_fails_closed_on_runner_provenance_schema_drift(tmp_path: Path) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    verified_payload = _read_json(verified_result_path)
    runner_provenance_path = root / verified_payload["verified_artifacts"]["runner_provenance_path"]
    runner_provenance_payload = _read_json(runner_provenance_path)
    runner_provenance_payload["schema"] = "taskpack_runner_provenance@999"
    _write_json(runner_provenance_path, runner_provenance_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _verify_taskpack_run_signed(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
            runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
            runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
            policy_rejection_diagnostics_path=None,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4602"


def test_verify_taskpack_run_fails_closed_on_candidate_plan_schema_drift(tmp_path: Path) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    verified_payload = _read_json(verified_result_path)
    candidate_path = root / verified_payload["verified_artifacts"]["candidate_change_plan_path"]
    candidate_payload = _read_json(candidate_path)
    candidate_payload["schema"] = "candidate_change_plan@999"
    _write_json(candidate_path, candidate_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _verify_taskpack_run_signed(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
            runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
            runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
            policy_rejection_diagnostics_path=None,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4603"


def test_verify_taskpack_run_fails_closed_on_policy_validation_consistency_mismatch(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    verified_payload = _read_json(verified_result_path)
    runner_result_path = root / verified_payload["verified_artifacts"]["runner_result_path"]
    runner_payload = _read_json(runner_result_path)
    runner_payload["rejection_diagnostic_path"] = "artifacts/agent_harness/v46/unexpected.json"
    _write_json(runner_result_path, runner_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _verify_taskpack_run_signed(
            root,
            taskpack_dir=taskpack_dir,
            candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
            runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
            runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
            policy_rejection_diagnostics_path=None,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4605"


def test_write_closeout_evidence_fails_closed_on_required_evidence_slot_missing(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    evidence_slots_path = taskpack_dir / "EVIDENCE_SLOTS.json"
    evidence_slots_payload = _read_json(evidence_slots_path)
    evidence_slots_payload["slots"] = [
        slot
        for slot in evidence_slots_payload["slots"]
        if slot["slot_id"] != "v34a_handoff_completion_evidence"
    ]
    evidence_slots_payload["required_count"] = len(
        [slot for slot in evidence_slots_payload["slots"] if slot["required"] is True]
    )
    _write_json(evidence_slots_path, evidence_slots_payload)
    _sync_manifest_component_hash(taskpack_dir, relative_path="EVIDENCE_SLOTS.json")
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4611"


def test_write_closeout_evidence_fails_closed_when_matrix_slot_required_but_missing(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            evidence_output_root="artifacts/agent_harness/v50/evidence_missing_matrix",
    )
    assert _error_payload(exc_info.value)["code"] == "AHK4611"


def test_write_closeout_evidence_fails_closed_when_policy_recompute_slot_required_but_missing(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            matrix_parity_evidence_path=matrix_evidence_path,
            evidence_output_root="artifacts/agent_harness/v51/evidence_missing_recompute",
    )
    assert _error_payload(exc_info.value)["code"] == "AHK4611"


def test_write_closeout_evidence_fails_closed_when_retry_context_slot_required_but_missing(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    _add_retry_context_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            matrix_parity_evidence_path=matrix_evidence_path,
            policy_recompute_evidence_path=policy_recompute_evidence_path,
            evidence_output_root="artifacts/agent_harness/v52/evidence_missing_retry_context",
    )
    assert _error_payload(exc_info.value)["code"] == "AHK4611"


def test_write_closeout_evidence_fails_closed_when_attestation_slot_required_but_missing(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    _add_retry_context_slot(taskpack_dir)
    _add_attestation_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )
    retry_context_evidence_path = _seed_v52_retry_context_evidence_payload(
        root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            matrix_parity_evidence_path=matrix_evidence_path,
            policy_recompute_evidence_path=policy_recompute_evidence_path,
            retry_context_evidence_path=retry_context_evidence_path,
            evidence_output_root="artifacts/agent_harness/v53/evidence_missing_attestation",
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4611"


def test_write_closeout_evidence_fails_closed_on_malformed_evidence_slot(tmp_path: Path) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    evidence_slots_path = taskpack_dir / "EVIDENCE_SLOTS.json"
    evidence_slots_payload = _read_json(evidence_slots_path)
    evidence_slots_payload["slots"][0]["required"] = "true"
    _write_json(evidence_slots_path, evidence_slots_payload)
    _sync_manifest_component_hash(taskpack_dir, relative_path="EVIDENCE_SLOTS.json")
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4603"


def test_write_closeout_evidence_fails_closed_on_invalid_handoff_completion_evidence(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    runtime_path, continuity_path, handoff_path = _seed_u2_evidence_payloads(root)
    handoff_payload = _read_json(handoff_path)
    handoff_payload["verification_passed"] = False
    _write_json(handoff_path, handoff_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        write_closeout_evidence(
            taskpack_dir=_relative(root, taskpack_dir),
            verified_result_path=_relative(root, verified_result_path),
            runtime_observability_comparison_path=_relative(root, runtime_path),
            metric_key_continuity_assertion_path=_relative(root, continuity_path),
            handoff_completion_evidence_path=_relative(root, handoff_path),
            evidence_output_root="artifacts/agent_harness/v46/evidence_invalid_handoff_case",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4603"


def test_write_closeout_evidence_fails_closed_on_invalid_matrix_parity_evidence(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    matrix_payload = _read_json(matrix_evidence_path)
    matrix_payload["matrix_report_hash"] = "f" * 64
    _write_json(matrix_evidence_path, matrix_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            matrix_parity_evidence_path=matrix_evidence_path,
            evidence_output_root="artifacts/agent_harness/v50/evidence_invalid_matrix",
    )
    assert _error_payload(exc_info.value)["code"] == "AHK4604"


def test_write_closeout_evidence_fails_closed_on_invalid_policy_recompute_evidence(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_payload = _read_json(policy_recompute_evidence_path)
    policy_recompute_payload["verification_passed"] = False
    _write_json(policy_recompute_evidence_path, policy_recompute_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            matrix_parity_evidence_path=matrix_evidence_path,
            policy_recompute_evidence_path=policy_recompute_evidence_path,
            evidence_output_root="artifacts/agent_harness/v51/evidence_invalid_recompute",
    )
    assert _error_payload(exc_info.value)["code"] == "AHK4603"


def test_write_closeout_evidence_fails_closed_on_invalid_retry_context_evidence(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    _add_retry_context_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )
    retry_context_evidence_path = _seed_v52_retry_context_evidence_payload(
        root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
    )
    retry_context_payload = _read_json(retry_context_evidence_path)
    retry_context_payload["shared_feeder_engine_identifier"] = (
        "v34d_retry_context_feeder_engine@1:drift"
    )
    _write_json(retry_context_evidence_path, retry_context_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            matrix_parity_evidence_path=matrix_evidence_path,
            policy_recompute_evidence_path=policy_recompute_evidence_path,
            retry_context_evidence_path=retry_context_evidence_path,
            evidence_output_root="artifacts/agent_harness/v52/evidence_invalid_retry_context",
    )
    assert _error_payload(exc_info.value)["code"] == "AHK4603"


def test_write_closeout_evidence_fails_closed_on_invalid_attestation_evidence(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    _add_retry_context_slot(taskpack_dir)
    _add_attestation_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )
    retry_context_evidence_path = _seed_v52_retry_context_evidence_payload(
        root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
    )
    attestation_evidence_path = _seed_v53_attestation_evidence_payload(
        root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    attestation_payload = _read_json(attestation_evidence_path)
    attestation_verification_result_path = root / attestation_payload[
        "attestation_verification_result_path"
    ]
    attestation_verification_result_payload = _read_json(attestation_verification_result_path)
    attestation_verification_result_payload["provider_id"] = "deterministic_test_enclave_drift"
    _write_json(attestation_verification_result_path, attestation_verification_result_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            matrix_parity_evidence_path=matrix_evidence_path,
            policy_recompute_evidence_path=policy_recompute_evidence_path,
            retry_context_evidence_path=retry_context_evidence_path,
            attestation_evidence_path=attestation_evidence_path,
            evidence_output_root="artifacts/agent_harness/v53/evidence_invalid_attestation",
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4604"


def test_write_closeout_evidence_fails_closed_on_malformed_retry_context_result_item(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, _, diagnostic_registry_rel = _prepare_verified_success(tmp_path)
    _add_matrix_parity_slot(taskpack_dir)
    _add_policy_recompute_slot(taskpack_dir)
    _add_retry_context_slot(taskpack_dir)
    verified_result_path = _reverify_with_current_taskpack(
        root=root,
        taskpack_dir=taskpack_dir,
        diagnostic_registry_rel=diagnostic_registry_rel,
    )
    _, _, matrix_evidence_path = _seed_v50_matrix_parity_payloads(
        root,
        verified_result_path=verified_result_path,
    )
    policy_recompute_evidence_path = _seed_v51_policy_recompute_evidence_payload(
        root,
        verified_result_path=verified_result_path,
    )
    retry_context_evidence_path = _seed_v52_retry_context_evidence_payload(
        root,
        taskpack_dir=taskpack_dir,
        verified_result_path=verified_result_path,
    )
    retry_context_payload = _read_json(retry_context_evidence_path)
    retry_context_result_path = root / retry_context_payload["retry_context_feeder_result_path"]
    retry_context_result_payload = _read_json(retry_context_result_path)
    retry_context_result_payload["items"][0] = {}
    _write_json(retry_context_result_path, retry_context_result_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
            matrix_parity_evidence_path=matrix_evidence_path,
            policy_recompute_evidence_path=policy_recompute_evidence_path,
            retry_context_evidence_path=retry_context_evidence_path,
            evidence_output_root="artifacts/agent_harness/v52/evidence_malformed_retry_context",
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4604"


def test_write_closeout_evidence_fails_closed_on_registry_prefix_drift(tmp_path: Path) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    registry_path = root / diagnostic_registry_rel
    registry_payload = _read_json(registry_path)
    registry_payload["codes"][0]["issue_code"] = "AHK9900"
    _write_json(registry_path, registry_payload)

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4608"


def test_write_closeout_evidence_fails_closed_on_allowlist_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    monkeypatch.setattr(
        evidence_writer_mod,
        "EVIDENCE_SCHEMA_ALLOWLIST",
        evidence_writer_mod.EVIDENCE_SCHEMA_ALLOWLIST + ("extra_schema@1",),
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        _write_evidence_with_seeded_payloads(
            root=root,
            taskpack_dir=taskpack_dir,
            verified_result_path=verified_result_path,
            diagnostic_registry_rel=diagnostic_registry_rel,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4611"


def test_emit_rejection_diagnostic_orders_issues_deterministically(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    diagnostic_registry_rel = _seed_diagnostic_registry(root)
    _, registry_codes = load_diagnostic_registry(
        root=root,
        registry_rel_path=diagnostic_registry_rel,
    )

    issues = [
        VerifierIssue(
            issue_code="AHK4602",
            reason="second",
            artifact_path="b/path.json",
            evidence_slot_id="z",
            policy_source="runner_result",
        ),
        VerifierIssue(
            issue_code="AHK4602",
            reason="first",
            artifact_path="b/path.json",
            evidence_slot_id="a",
            policy_source="runner_result",
        ),
        VerifierIssue(
            issue_code="AHK4601",
            reason="third",
            artifact_path="a/path.json",
            evidence_slot_id="m",
            policy_source="runner_result",
        ),
    ]
    emitted = emit_rejection_diagnostic(
        root=root,
        output_root_rel="artifacts/agent_harness/v46/rejections",
        taskpack_manifest_hash="a" * 64,
        candidate_change_plan_hash="b" * 64,
        issues=issues,
        allowed_codes=registry_codes,
    )
    emitted_payload = _read_json(emitted)
    rows = emitted_payload["issues"]
    assert rows == sorted(
        rows,
        key=lambda row: (row["issue_code"], row["artifact_path"], row["evidence_slot_id"]),
    )


def test_emit_rejection_diagnostic_fails_on_policy_source_outside_closed_enum(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    diagnostic_registry_rel = _seed_diagnostic_registry(root)
    _, registry_codes = load_diagnostic_registry(
        root=root,
        registry_rel_path=diagnostic_registry_rel,
    )

    with pytest.raises(TaskpackVerifierError) as exc_info:
        emit_rejection_diagnostic(
            root=root,
            output_root_rel="artifacts/agent_harness/v46/rejections",
            taskpack_manifest_hash="a" * 64,
            candidate_change_plan_hash="b" * 64,
            issues=[
                VerifierIssue(
                    issue_code="AHK4602",
                    reason="invalid policy source",
                    artifact_path="b/path.json",
                    evidence_slot_id="x",
                    policy_source="free_text",
                )
            ],
            allowed_codes=registry_codes,
        )
    assert _error_payload(exc_info.value)["code"] == "AHK4614"


def test_verifier_cli_returns_non_zero_on_required_violation(tmp_path: Path) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)
    verified_payload = _read_json(verified_result_path)
    runner_result_path = root / verified_payload["verified_artifacts"]["runner_result_path"]
    runner_payload = _read_json(runner_result_path)
    runner_payload["candidate_change_plan_hash"] = "f" * 64
    _write_json(runner_result_path, runner_payload)

    exit_code = verifier_mod.main(
        [
            "--taskpack-dir",
            _relative(root, taskpack_dir),
            "--candidate-change-plan",
            verified_payload["verified_artifacts"]["candidate_change_plan_path"],
            "--runner-result",
            verified_payload["verified_artifacts"]["runner_result_path"],
            "--runner-provenance",
            verified_payload["verified_artifacts"]["runner_provenance_path"],
            "--signature-verification-result",
            signing.signature_verification_result_path,
            "--signature-envelope",
            signing.signature_envelope_path,
            "--trust-anchor-registry",
            signing.trust_anchor_registry_path,
            "--verification-reference-time-utc",
            signing.verification_reference_time_utc,
            "--verification-output-root",
            "artifacts/agent_harness/v46/verification",
            "--diagnostic-registry",
            diagnostic_registry_rel,
            "--repo-root",
            str(root),
        ]
    )
    assert exit_code == 1


def test_stop_gate_keyset_continuity_and_cardinality_v45_to_v46() -> None:
    resolved_repo_root = repo_root(anchor=Path(__file__))
    v45_payload = _read_json(resolved_repo_root / "artifacts/stop_gate/metrics_v45_closeout.json")
    v46_payload = _read_json(resolved_repo_root / "artifacts/stop_gate/metrics_v46_closeout.json")
    assert v45_payload["schema"] == "stop_gate_metrics@1"
    assert v46_payload["schema"] == "stop_gate_metrics@1"

    v45_keys = set(v45_payload["metrics"].keys())
    v46_keys = set(v46_payload["metrics"].keys())
    assert v45_keys == v46_keys
    assert len(v46_keys) == 80
