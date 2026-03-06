from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_agent_harness._test_signing_handoff import seed_signing_handoff_fixture
from adeu_agent_harness.compile import (
    PIPELINE_PROFILE_SCHEMA,
    TASKPACK_PROFILE_REGISTRY_SCHEMA,
    compile_taskpack,
)
from adeu_agent_harness.retry_context import (
    DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
    MAX_TOTAL_OUTPUT_CHARS,
    RETRY_CONTEXT_FEEDER_RESULT_SCHEMA,
    RETRY_CONTEXT_SANITIZATION_PROFILE_SCHEMA,
    SHARED_FEEDER_ENGINE,
    SHARED_FEEDER_ENGINE_IDENTIFIER,
    TaskpackRetryContextError,
    generate_retry_context,
)
from adeu_agent_harness.run_taskpack import (
    RUNNER_RESULT_SCHEMA,
    TaskpackRunnerError,
    TaskpackRunnerResult,
    run_taskpack,
)
from urm_runtime.hashing import canonical_json, sha256_canonical_json

_OUT_DIR = "artifacts/agent_harness/v52/taskpacks/v41/v52_default"


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
        "profile_id": "v52_default",
        "task_scope_title": "V52 A1 Retry Context Feeder",
        "task_scope_summary": "Compile deterministic taskpack for retry-context feeder baseline.",
        "compiled_commitments_ir_path": "artifacts/semantic_compiler/v40/commitments_ir.json",
        "acceptance_criteria": [
            "Emit canonical runner rejection diagnostics on policy failure.",
            "Allow retry-context feeder to reuse canonical candidate plan surface.",
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
    profile_path = root / "artifacts" / "agent_harness" / "v52" / "profiles" / "v52_default.json"
    _write_json(profile_path, profile_payload)
    registry_path = root / "artifacts" / "agent_harness" / "v52" / "taskpack_profile_registry.json"
    _write_json(
        registry_path,
        {
            "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
            "profiles": [
                {
                    "profile_id": "v52_default",
                    "profile_sha256": sha256_canonical_json(profile_payload),
                    "profile_payload_path": "artifacts/agent_harness/v52/profiles/v52_default.json",
                }
            ],
        },
    )
    return registry_path


def _compile_taskpack(root: Path, *, registry_path: Path) -> Path:
    result = compile_taskpack(
        profile_registry_path=registry_path.relative_to(root),
        profile_id="v52_default",
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


def _create_diff(*, rel_path: str, content: str) -> str:
    return (
        "--- /dev/null\n"
        f"+++ b/{rel_path}\n"
        "@@ -0,0 +1,1 @@\n"
        f"+{content}\n"
    )


def _write_candidate_change_plan(
    root: Path,
    *,
    operations: list[dict[str, Any]],
    proposed_commands: list[str] | None = None,
) -> Path:
    path = root / "artifacts" / "agent_harness" / "v52" / "candidate_change_plan.json"
    _write_json(
        path,
        {
            "schema": "candidate_change_plan@1",
            "file_operations": operations,
            "proposed_commands": proposed_commands or [],
        },
    )
    return path


def _run_taskpack_signed(
    root: Path,
    *,
    taskpack_dir: Path,
    adapter_registry_path: Path,
    candidate_change_plan_path: Path,
    dry_run: bool,
) -> TaskpackRunnerResult:
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)
    return run_taskpack(
        taskpack_dir=taskpack_dir.relative_to(root).as_posix(),
        adapter_registry_path=adapter_registry_path.relative_to(root).as_posix(),
        adapter_id="default",
        candidate_change_plan_path=candidate_change_plan_path.relative_to(root).as_posix(),
        dry_run=dry_run,
        repo_root_path=root,
        **signing.as_kwargs(),
    )


def _write_runner_result_from_error_details(root: Path, *, details: dict[str, Any]) -> Path:
    path = root / "artifacts" / "agent_harness" / "v52" / "runner_result_policy_failure.json"
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


def _write_runner_result(root: Path, *, run_result: TaskpackRunnerResult) -> Path:
    path = root / "artifacts" / "agent_harness" / "v52" / "runner_result_success.json"
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


def _prepare_runner_policy_failure_artifacts(
    tmp_path: Path,
) -> tuple[Path, Path, Path, Path]:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)

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
    )

    with pytest.raises(TaskpackRunnerError) as exc_info:
        _run_taskpack_signed(
            root,
            taskpack_dir=taskpack_dir,
            adapter_registry_path=adapter_registry_path,
            candidate_change_plan_path=candidate_path,
            dry_run=True,
        )
    details = json.loads(str(exc_info.value))["details"]
    runner_result_path = _write_runner_result_from_error_details(root, details=details)
    return root, candidate_path, runner_result_path, Path(details["rejection_diagnostic_path"])


def _prepare_runner_policy_success_artifacts(tmp_path: Path) -> tuple[Path, Path, Path]:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)
    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/v52_success_fixture.txt"
    (root / rel_path).parent.mkdir(parents=True, exist_ok=True)
    _write(root / rel_path, "before\n")
    candidate_path = _write_candidate_change_plan(
        root,
        operations=[
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
    )
    run_result = _run_taskpack_signed(
        root,
        taskpack_dir=taskpack_dir,
        adapter_registry_path=adapter_registry_path,
        candidate_change_plan_path=candidate_path,
        dry_run=True,
    )
    runner_result_path = _write_runner_result(root, run_result=run_result)
    return root, candidate_path, runner_result_path


def _error_payload(exc: TaskpackRetryContextError) -> dict[str, Any]:
    payload = json.loads(str(exc))
    assert payload["schema"] == "taskpack_retry_context_error@1"
    return payload


def test_generate_retry_context_emits_deterministic_result_and_profile(tmp_path: Path) -> None:
    root, candidate_path, runner_result_path, rejection_diagnostic_path = (
        _prepare_runner_policy_failure_artifacts(tmp_path)
    )

    first = generate_retry_context(
        candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
        runner_result_path=runner_result_path.relative_to(root).as_posix(),
        retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
        repo_root_path=root,
    )
    second = generate_retry_context(
        candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
        runner_result_path=runner_result_path.relative_to(root).as_posix(),
        retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
        repo_root_path=root,
    )

    assert first.result_path == second.result_path
    assert first.result_path.read_bytes() == second.result_path.read_bytes()
    assert (
        first.sanitization_profile_path.read_bytes()
        == second.sanitization_profile_path.read_bytes()
    )

    result_payload = _read_json(first.result_path)
    profile_payload = _read_json(first.sanitization_profile_path)
    rejection_payload = _read_json(rejection_diagnostic_path)

    assert result_payload["schema"] == RETRY_CONTEXT_FEEDER_RESULT_SCHEMA
    assert result_payload["shared_feeder_engine"] == SHARED_FEEDER_ENGINE
    assert result_payload["shared_feeder_engine_identifier"] == SHARED_FEEDER_ENGINE_IDENTIFIER
    assert result_payload["taskpack_manifest_hash"] == rejection_payload["taskpack_manifest_hash"]
    assert (
        result_payload["candidate_change_plan_hash"]
        == rejection_payload["candidate_change_plan_hash"]
    )
    assert result_payload["items"] == sorted(
        result_payload["items"],
        key=lambda row: (
            row["issue_reference"]["issue_code"],
            row["issue_reference"]["target_path"],
            row["issue_reference"]["hunk_index"],
            row["issue_reference"]["policy_source"],
        ),
    )
    assert result_payload["total_output_chars_used"] <= MAX_TOTAL_OUTPUT_CHARS

    assert profile_payload["schema"] == RETRY_CONTEXT_SANITIZATION_PROFILE_SCHEMA
    assert profile_payload["shared_feeder_engine"] == SHARED_FEEDER_ENGINE
    assert profile_payload["shared_feeder_engine_identifier"] == SHARED_FEEDER_ENGINE_IDENTIFIER


def test_generate_retry_context_fails_closed_without_rejection_diagnostic_on_success_path(
    tmp_path: Path,
) -> None:
    root, candidate_path, runner_result_path = _prepare_runner_policy_success_artifacts(tmp_path)

    with pytest.raises(TaskpackRetryContextError) as exc_info:
        generate_retry_context(
            candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
            runner_result_path=runner_result_path.relative_to(root).as_posix(),
            retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5202"


def test_generate_retry_context_rejects_duplicate_issue_tuples_after_path_normalization(
    tmp_path: Path,
) -> None:
    root, candidate_path, runner_result_path, rejection_diagnostic_path = (
        _prepare_runner_policy_failure_artifacts(tmp_path)
    )
    rejection_payload = _read_json(rejection_diagnostic_path)
    issue = rejection_payload["issues"][0]
    duplicate = dict(issue)
    duplicate["target_path"] = issue["target_path"].replace("/", "//")
    rejection_payload["issues"] = [issue, duplicate]
    _write_json(rejection_diagnostic_path, rejection_payload)

    with pytest.raises(TaskpackRetryContextError) as exc_info:
        generate_retry_context(
            candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
            runner_result_path=runner_result_path.relative_to(root).as_posix(),
            retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5203"


def test_generate_retry_context_neutralizes_control_markers_and_excludes_repo_file_content(
    tmp_path: Path,
) -> None:
    root, candidate_path, runner_result_path, rejection_diagnostic_path = (
        _prepare_runner_policy_failure_artifacts(tmp_path)
    )
    rejection_payload = _read_json(rejection_diagnostic_path)
    rejection_payload["issues"][0]["reason"] = "bad ``` fence <|system|> marker"
    _write_json(rejection_diagnostic_path, rejection_payload)

    secret_path = root / "apps" / "api" / "v52_retry_context_fixture.txt"
    _write(secret_path, "TOP_SECRET_FILE_CONTENT\n")

    result = generate_retry_context(
        candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
        runner_result_path=runner_result_path.relative_to(root).as_posix(),
        retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
        repo_root_path=root,
    )
    payload = _read_json(result.result_path)
    serialized = result.result_path.read_text(encoding="utf-8")
    reason_excerpt = payload["items"][0]["sanitized_reason_excerpt"]["text"]

    assert "```" not in reason_excerpt
    assert "<|" not in reason_excerpt
    assert "TOP_SECRET_FILE_CONTENT" not in serialized


def test_generate_retry_context_uses_missing_excerpt_typed_null_marker(tmp_path: Path) -> None:
    root, candidate_path, runner_result_path, rejection_diagnostic_path = (
        _prepare_runner_policy_failure_artifacts(tmp_path)
    )
    rejection_payload = _read_json(rejection_diagnostic_path)
    rejection_payload["issues"][0]["hunk_index"] = 999
    _write_json(rejection_diagnostic_path, rejection_payload)

    result = generate_retry_context(
        candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
        runner_result_path=runner_result_path.relative_to(root).as_posix(),
        retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
        repo_root_path=root,
    )
    payload = _read_json(result.result_path)
    candidate_excerpt = payload["items"][0]["sanitized_candidate_plan_excerpt"]

    assert candidate_excerpt == {
        "present": False,
        "text": None,
        "truncated": False,
        "source_kind": "missing",
        "original_line_count": 0,
        "original_char_count": 0,
    }


def test_generate_retry_context_explicit_rejection_input_must_match_runner_result(
    tmp_path: Path,
) -> None:
    root, candidate_path, runner_result_path, rejection_diagnostic_path = (
        _prepare_runner_policy_failure_artifacts(tmp_path)
    )
    other_path = root / "artifacts" / "agent_harness" / "v52" / "other_rejection.json"
    _write_json(other_path, _read_json(rejection_diagnostic_path))

    with pytest.raises(TaskpackRetryContextError) as exc_info:
        generate_retry_context(
            candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
            runner_result_path=runner_result_path.relative_to(root).as_posix(),
            rejection_diagnostic_path=other_path.relative_to(root).as_posix(),
            retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5204"


def test_generate_retry_context_rejects_output_root_with_trailing_parent_segment(
    tmp_path: Path,
) -> None:
    root, candidate_path, runner_result_path, _ = _prepare_runner_policy_failure_artifacts(tmp_path)

    with pytest.raises(TaskpackRetryContextError) as exc_info:
        generate_retry_context(
            candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
            runner_result_path=runner_result_path.relative_to(root).as_posix(),
            retry_context_output_root="artifacts/..",
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5201"


def test_generate_retry_context_wraps_directory_inputs_as_structured_errors(
    tmp_path: Path,
) -> None:
    root, candidate_path, _, _ = _prepare_runner_policy_failure_artifacts(tmp_path)
    directory_path = root / "artifacts" / "agent_harness" / "v52" / "not_a_json_payload"
    directory_path.mkdir(parents=True, exist_ok=True)

    with pytest.raises(TaskpackRetryContextError) as exc_info:
        generate_retry_context(
            candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
            runner_result_path=directory_path.relative_to(root).as_posix(),
            retry_context_output_root=DEFAULT_RETRY_CONTEXT_OUTPUT_ROOT,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK5201"
