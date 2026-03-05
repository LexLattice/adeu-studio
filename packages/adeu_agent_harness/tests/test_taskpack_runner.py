from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_agent_harness.compile import (
    PIPELINE_PROFILE_SCHEMA,
    TASKPACK_PROFILE_REGISTRY_SCHEMA,
    compile_taskpack,
)
from adeu_agent_harness.run_taskpack import TaskpackRunnerError, run_taskpack
from urm_runtime.hashing import canonical_json, sha256_canonical_json

_OUT_DIR = "artifacts/agent_harness/v45/taskpacks/v41/v45_default"


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


def _seed_profile_and_registry(
    root: Path,
    *,
    commands: list[dict[str, Any]],
    profile_id: str = "v45_default",
) -> Path:
    profile_payload = {
        "schema": PIPELINE_PROFILE_SCHEMA,
        "profile_id": profile_id,
        "task_scope_title": "V45 T1 TaskPack Runner MVP",
        "task_scope_summary": "Run deterministic constrained runner over canonical candidate plan.",
        "compiled_commitments_ir_path": "artifacts/semantic_compiler/v40/commitments_ir.json",
        "acceptance_criteria": [
            "Enforce allowlist/forbidden policy before workspace writes.",
            "Emit deterministic dry-run and provenance artifacts.",
        ],
        "allowlist_paths": [
            "packages/adeu_agent_harness/src/adeu_agent_harness",
            "packages/adeu_agent_harness/tests",
        ],
        "forbidden_paths": ["apps/api"],
        "forbidden_effects": ["network_calls"],
        "commands": commands,
        "evidence_slots": [
            {
                "slot_id": "runner_provenance_hash",
                "description": "Capture runner provenance hash.",
                "required": True,
            }
        ],
    }
    profile_path = (
        root / "artifacts" / "agent_harness" / "v45" / "profiles" / f"{profile_id}.json"
    )
    _write_json(profile_path, profile_payload)

    registry_path = root / "artifacts" / "agent_harness" / "v45" / "taskpack_profile_registry.json"
    _write_json(
        registry_path,
        {
            "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
            "profiles": [
                {
                    "profile_id": profile_id,
                    "profile_sha256": sha256_canonical_json(profile_payload),
                    "profile_payload_path": (
                        f"artifacts/agent_harness/v45/profiles/{profile_id}.json"
                    ),
                }
            ],
        },
    )
    return registry_path


def _compile_taskpack(root: Path, *, registry_path: Path) -> Path:
    result = compile_taskpack(
        profile_registry_path=registry_path.relative_to(root),
        profile_id="v45_default",
        source_semantic_arc="v41",
        out_dir=_OUT_DIR,
        repo_root_path=root,
    )
    return result.out_dir


def _seed_adapter_registry(root: Path, *, adapter_id: str = "default") -> Path:
    adapter_registry_path = (
        root / "artifacts" / "agent_harness" / "v45" / "taskpack_runner_adapter_registry.json"
    )
    _write_json(
        adapter_registry_path,
        {
            "schema": "taskpack_runner_adapter_registry@1",
            "adapters": [
                {
                    "adapter_id": adapter_id,
                    "adapter_kind": "candidate_plan_passthrough",
                }
            ],
        },
    )
    return adapter_registry_path


def _write_candidate_change_plan(
    root: Path,
    *,
    operations: list[dict[str, Any]],
    proposed_commands: list[str],
    rel_path: str = "artifacts/agent_harness/v45/candidate_change_plan.json",
) -> Path:
    candidate_plan_path = root / rel_path
    _write_json(
        candidate_plan_path,
        {
            "schema": "candidate_change_plan@1",
            "file_operations": operations,
            "proposed_commands": proposed_commands,
        },
    )
    return candidate_plan_path


def _update_diff(*, rel_path: str, before: str, after: str) -> str:
    return (
        f"--- a/{rel_path}\n"
        f"+++ b/{rel_path}\n"
        "@@ -1,1 +1,1 @@\n"
        f"-{before}\n"
        f"+{after}\n"
    )


def _create_diff(*, rel_path: str, content: str) -> str:
    return (
        "--- /dev/null\n"
        f"+++ b/{rel_path}\n"
        "@@ -0,0 +1,1 @@\n"
        f"+{content}\n"
    )


def _default_commands() -> list[dict[str, Any]]:
    return [
        {
            "command_id": "noop",
            "run": "true",
            "working_directory_or_repo_root": "repo_root",
            "env_overrides": {},
        }
    ]


def _error_payload(exc: TaskpackRunnerError) -> dict[str, Any]:
    payload = json.loads(str(exc))
    assert payload["schema"] == "taskpack_runner_error@1"
    return payload


def test_run_taskpack_dry_run_is_deterministic_and_side_effect_free(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    registry_path = _seed_profile_and_registry(root, commands=_default_commands())
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)

    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/runner_fixture.txt"
    fixture_path = root / rel_path
    _write(fixture_path, "before\n")
    candidate_path = _write_candidate_change_plan(
        root,
        operations=[
            {
                "path": rel_path,
                "operation_kind": "update",
                "unified_diff": _update_diff(rel_path=rel_path, before="before", after="after"),
            }
        ],
        proposed_commands=[],
    )

    first = run_taskpack(
        taskpack_dir=taskpack_dir.relative_to(root),
        adapter_registry_path=adapter_registry_path.relative_to(root),
        adapter_id="default",
        candidate_change_plan_path=candidate_path.relative_to(root),
        dry_run=True,
        repo_root_path=root,
    )
    second = run_taskpack(
        taskpack_dir=taskpack_dir.relative_to(root),
        adapter_registry_path=adapter_registry_path.relative_to(root),
        adapter_id="default",
        candidate_change_plan_path=candidate_path.relative_to(root),
        dry_run=True,
        repo_root_path=root,
    )

    assert fixture_path.read_text(encoding="utf-8") == "before\n"
    assert first.rejection_diagnostic_path is None
    assert first.candidate_change_plan_hash == second.candidate_change_plan_hash
    assert first.dry_run_preview_path is not None
    assert second.dry_run_preview_path is not None
    assert first.dry_run_preview_path.read_bytes() == second.dry_run_preview_path.read_bytes()
    assert first.provenance_path.read_bytes() == second.provenance_path.read_bytes()


def test_run_taskpack_apply_and_authorized_command_execution(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    marker_rel = "artifacts/agent_harness/v45/command_ran.txt"
    marker_cmd = f"printf 'ran' > {marker_rel}"
    registry_path = _seed_profile_and_registry(
        root,
        commands=[
            {
                "command_id": "marker",
                "run": marker_cmd,
                "working_directory_or_repo_root": "repo_root",
                "env_overrides": {},
            }
        ],
    )
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)

    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/runner_apply_fixture.txt"
    fixture_path = root / rel_path
    _write(fixture_path, "before\n")
    candidate_path = _write_candidate_change_plan(
        root,
        operations=[
            {
                "path": rel_path,
                "operation_kind": "update",
                "unified_diff": _update_diff(rel_path=rel_path, before="before", after="after"),
            }
        ],
        proposed_commands=[marker_cmd],
    )

    result = run_taskpack(
        taskpack_dir=taskpack_dir.relative_to(root),
        adapter_registry_path=adapter_registry_path.relative_to(root),
        adapter_id="default",
        candidate_change_plan_path=candidate_path.relative_to(root),
        dry_run=False,
        repo_root_path=root,
    )

    assert result.dry_run is False
    assert fixture_path.read_text(encoding="utf-8") == "after\n"
    marker_path = root / marker_rel
    assert marker_path.read_text(encoding="utf-8") == "ran"


def test_run_taskpack_policy_violation_emits_rejection_and_provenance(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    registry_path = _seed_profile_and_registry(root, commands=_default_commands())
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)

    blocked_rel = "apps/api/blocked.txt"
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
        run_taskpack(
            taskpack_dir=taskpack_dir.relative_to(root),
            adapter_registry_path=adapter_registry_path.relative_to(root),
            adapter_id="default",
            candidate_change_plan_path=candidate_path.relative_to(root),
            dry_run=True,
            repo_root_path=root,
        )

    error_payload = _error_payload(exc_info.value)
    assert error_payload["code"] == "AHK1010"
    details = error_payload["details"]
    rejection_path = Path(details["rejection_diagnostic_path"])
    provenance_path = Path(details["provenance_path"])
    assert rejection_path.is_file()
    assert provenance_path.is_file()

    rejection_payload = _read_json(rejection_path)
    assert rejection_payload["schema"] == "candidate_change_plan_rejection_diagnostic@1"
    issue_codes = {issue["issue_code"] for issue in rejection_payload["issues"]}
    assert "allowlist_violation" in issue_codes
    assert "forbidden_path_violation" in issue_codes


def test_run_taskpack_adapter_selection_is_exact_case_sensitive(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    registry_path = _seed_profile_and_registry(root, commands=_default_commands())
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root, adapter_id="Passthrough")

    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/adapter_fixture.txt"
    _write(root / rel_path, "before\n")
    candidate_path = _write_candidate_change_plan(
        root,
        operations=[
            {
                "path": rel_path,
                "operation_kind": "update",
                "unified_diff": _update_diff(rel_path=rel_path, before="before", after="after"),
            }
        ],
        proposed_commands=[],
    )

    with pytest.raises(TaskpackRunnerError) as exc_info:
        run_taskpack(
            taskpack_dir=taskpack_dir.relative_to(root),
            adapter_registry_path=adapter_registry_path.relative_to(root),
            adapter_id="passthrough",
            candidate_change_plan_path=candidate_path.relative_to(root),
            dry_run=True,
            repo_root_path=root,
        )

    error_payload = _error_payload(exc_info.value)
    assert error_payload["code"] == "AHK1006"


def test_run_taskpack_dry_run_forbids_subprocess_execution(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    allowed_cmd = "echo allowed"
    registry_path = _seed_profile_and_registry(
        root,
        commands=[
            {
                "command_id": "allowed",
                "run": allowed_cmd,
                "working_directory_or_repo_root": "repo_root",
                "env_overrides": {},
            }
        ],
    )
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)

    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/dry_run_command_fixture.txt"
    _write(root / rel_path, "before\n")
    candidate_path = _write_candidate_change_plan(
        root,
        operations=[
            {
                "path": rel_path,
                "operation_kind": "update",
                "unified_diff": _update_diff(rel_path=rel_path, before="before", after="after"),
            }
        ],
        proposed_commands=[allowed_cmd],
    )

    with pytest.raises(TaskpackRunnerError) as exc_info:
        run_taskpack(
            taskpack_dir=taskpack_dir.relative_to(root),
            adapter_registry_path=adapter_registry_path.relative_to(root),
            adapter_id="default",
            candidate_change_plan_path=candidate_path.relative_to(root),
            dry_run=True,
            repo_root_path=root,
        )

    error_payload = _error_payload(exc_info.value)
    assert error_payload["code"] == "AHK1010"
    rejection_payload = _read_json(Path(error_payload["details"]["rejection_diagnostic_path"]))
    issue_codes = [issue["issue_code"] for issue in rejection_payload["issues"]]
    assert "dry_run_subprocess_execution_detected" in issue_codes
