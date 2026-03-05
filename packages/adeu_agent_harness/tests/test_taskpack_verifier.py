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
from adeu_agent_harness.run_taskpack import RUNNER_RESULT_SCHEMA, run_taskpack
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
from urm_runtime.hashing import canonical_json, sha256_canonical_json

_OUT_DIR = "artifacts/agent_harness/v46/taskpacks/v41/v46_default"
_DIAGNOSTIC_REGISTRY_REL = "artifacts/agent_harness/v46/diagnostic_registry_v46.json"


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
                "slot_id": "v33c_verifier_wiring_evidence",
                "description": "Verifier wiring evidence block.",
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


def _write_candidate_change_plan(root: Path, *, rel_path: str) -> Path:
    path = root / "artifacts" / "agent_harness" / "v46" / "candidate_change_plan.json"
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
    run_result = run_taskpack(
        taskpack_dir=_relative(root, taskpack_dir),
        adapter_registry_path=_relative(root, adapter_registry_path),
        adapter_id="default",
        candidate_change_plan_path=_relative(root, candidate_path),
        dry_run=True,
        repo_root_path=root,
    )
    assert fixture_path.read_text(encoding="utf-8") == "before\n"

    runner_result_path = _write_runner_result_artifact(root, run_result=run_result)
    verify_result = verify_taskpack_run(
        taskpack_dir=_relative(root, taskpack_dir),
        candidate_change_plan_path=_relative(root, candidate_path),
        runner_result_path=_relative(root, runner_result_path),
        runner_provenance_path=_relative(root, run_result.provenance_path),
        policy_rejection_diagnostics_path=None,
        verification_output_root="artifacts/agent_harness/v46/verification",
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
    )
    return root, taskpack_dir, verify_result.verification_result_path, diagnostic_registry_rel


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

    second = verify_taskpack_run(
        taskpack_dir=_relative(root, taskpack_dir),
        candidate_change_plan_path=verified_payload["verified_artifacts"]["candidate_change_plan_path"],
        runner_result_path=verified_payload["verified_artifacts"]["runner_result_path"],
        runner_provenance_path=verified_payload["verified_artifacts"]["runner_provenance_path"],
        policy_rejection_diagnostics_path=None,
        verification_output_root="artifacts/agent_harness/v46/verification",
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
    )

    assert second.verification_result_path == verified_result_path
    assert verified_result_path.read_bytes() == before


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
        verify_taskpack_run(
            taskpack_dir=_relative(root, taskpack_dir),
            candidate_change_plan_path=_relative(root, candidate_path),
            runner_result_path=_relative(root, runner_result_path),
            runner_provenance_path=_relative(root, runner_provenance_path),
            policy_rejection_diagnostics_path=None,
            verification_output_root="artifacts/agent_harness/v46/verification",
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4604"
    rejection_path = Path(payload["details"]["rejection_diagnostic_path"])
    rejection_payload = _read_json(rejection_path)
    assert rejection_payload["schema"] == "v33c_verifier_rejection_diagnostic@1"
    assert rejection_payload["issues"][0]["issue_code"] == "AHK4604"


def test_write_closeout_evidence_emits_deterministic_bundle_and_provenance(
    tmp_path: Path,
) -> None:
    root, taskpack_dir, verified_result_path, diagnostic_registry_rel = _prepare_verified_success(
        tmp_path
    )

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
    wiring_path = root / "artifacts" / "stop_gate" / "v33c_verifier_wiring_evidence_v46.json"
    _write_json(
        wiring_path,
        {
            "schema": "v33c_verifier_wiring_evidence@1",
            "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
            "evidence_writer_entrypoint": "python -m adeu_agent_harness.write_closeout_evidence",
            "verification_passed": True,
            "required_evidence_slots_filled": True,
        },
    )

    first = write_closeout_evidence(
        taskpack_dir=_relative(root, taskpack_dir),
        verified_result_path=_relative(root, verified_result_path),
        runtime_observability_comparison_path=_relative(root, runtime_path),
        metric_key_continuity_assertion_path=_relative(root, continuity_path),
        verifier_wiring_evidence_path=_relative(root, wiring_path),
        evidence_output_root="artifacts/agent_harness/v46/evidence",
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
    )
    second = write_closeout_evidence(
        taskpack_dir=_relative(root, taskpack_dir),
        verified_result_path=_relative(root, verified_result_path),
        runtime_observability_comparison_path=_relative(root, runtime_path),
        metric_key_continuity_assertion_path=_relative(root, continuity_path),
        verifier_wiring_evidence_path=_relative(root, wiring_path),
        evidence_output_root="artifacts/agent_harness/v46/evidence",
        diagnostic_registry_path=diagnostic_registry_rel,
        repo_root_path=root,
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
        "v33c_verifier_wiring_evidence",
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
    wiring_path = root / "artifacts" / "stop_gate" / "v33c_verifier_wiring_evidence_v46.json"
    _write_json(wiring_path, {"schema": "v33c_verifier_wiring_evidence@1"})

    evidence_output_rel = "artifacts/agent_harness/v46/evidence_failure_case"
    evidence_output_path = root / evidence_output_rel

    with pytest.raises(TaskpackVerifierError) as exc_info:
        write_closeout_evidence(
            taskpack_dir=_relative(root, taskpack_dir),
            verified_result_path=_relative(root, verified_result_path),
            runtime_observability_comparison_path=_relative(root, runtime_path),
            metric_key_continuity_assertion_path=_relative(root, continuity_path),
            verifier_wiring_evidence_path=_relative(root, wiring_path),
            evidence_output_root=evidence_output_rel,
            diagnostic_registry_path=diagnostic_registry_rel,
            repo_root_path=root,
        )

    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4612"
    assert "rejection_diagnostic_path" in payload["details"]
    assert not evidence_output_path.exists() or not list(evidence_output_path.glob("*.json"))
