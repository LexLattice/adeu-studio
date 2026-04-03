from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_agent_harness.compiled_taskpack_binding import CompiledPolicyTaskpackBinding
from adeu_agent_harness.worker_boundary_conformance import (
    WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA,
    WorkerBoundaryConformanceReport,
)
from adeu_agent_harness.worker_delegation_topology import (
    AHK6002_SCHEMA_MISMATCH,
    WORKER_DELEGATION_TOPOLOGY_SCHEMA,
    WorkerDelegationTopology,
    WorkerDelegationTopologyError,
    build_v48e_worker_delegation_topology,
)
from adeu_agent_harness.worker_execution_envelope import TaskRunBoundaryInstance
from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json


@pytest.fixture(autouse=True)
def _enforce_deterministic_env(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TZ", "UTC")
    monkeypatch.setenv("LC_ALL", "C")
    monkeypatch.setenv("PYTHONHASHSEED", "0")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_dir() -> Path:
    return Path(__file__).parent / "fixtures" / "v48e"


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_fixture(name: str) -> dict[str, Any]:
    return _read_json(_fixture_dir() / name)


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _load_repo_fixture(relative_path: str) -> dict[str, Any]:
    return _read_json(_repo_root() / relative_path)


def _seed_v48e_inputs(
    tmp_path: Path,
    *,
    child_worker_subject_ref: str = "worker:repo_internal_single_codex_worker:child",
    child_compiled_boundary_identity_hash: str | None = None,
    child_overall_judgment: str = "conformant",
) -> dict[str, Any]:
    root = tmp_path / "repo"
    root.mkdir()

    parent_compiled_binding_payload = _load_repo_fixture(
        "packages/adeu_agent_harness/tests/fixtures/v48b/reference_compiled_policy_taskpack_binding.json"
    )
    parent_boundary_payload = _load_repo_fixture(
        "packages/adeu_agent_harness/tests/fixtures/v48c/reference_task_run_boundary_instance.json"
    )
    parent_report_payload = _load_repo_fixture(
        "packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report.json"
    )

    parent_compiled_binding_ref = parent_report_payload["compiled_binding_ref"]
    parent_boundary_instance_ref = parent_report_payload["boundary_instance_ref"]
    parent_report_ref = (
        "artifacts/agent_harness/v48e/reference_parent/"
        "worker_boundary_conformance_report.json"
    )

    _write_json(root / parent_compiled_binding_ref, parent_compiled_binding_payload)
    _write_json(root / parent_boundary_instance_ref, parent_boundary_payload)
    _write_json(root / parent_report_ref, parent_report_payload)

    child_compiled_binding_ref = (
        "artifacts/agent_harness/v48e/reference_child/compiled_policy_taskpack_binding.json"
    )
    child_boundary_instance_ref = (
        "artifacts/agent_harness/v48e/reference_child/task_run_boundary_instance.json"
    )
    child_report_ref = (
        "artifacts/agent_harness/v48e/reference_child/"
        "worker_boundary_conformance_report.json"
    )

    child_compiled_binding = CompiledPolicyTaskpackBinding.model_validate(
        {
            **parent_compiled_binding_payload,
            "compiled_binding_id": "compiled-taskpack-binding:child4502a3ff",
            "worker_subject_ref": child_worker_subject_ref,
            "compiled_boundary_identity_hash": (
                child_compiled_boundary_identity_hash
                or parent_compiled_binding_payload["compiled_boundary_identity_hash"]
            ),
            "taskpack_markdown_ref": "artifacts/agent_harness/v48e/reference_child/TASKPACK.md",
            "acceptance_ref": "artifacts/agent_harness/v48e/reference_child/ACCEPTANCE.json",
            "allowlist_ref": "artifacts/agent_harness/v48e/reference_child/ALLOWLIST.json",
            "forbidden_ref": "artifacts/agent_harness/v48e/reference_child/FORBIDDEN.json",
            "commands_ref": "artifacts/agent_harness/v48e/reference_child/COMMANDS.json",
            "evidence_slots_ref": (
                "artifacts/agent_harness/v48e/reference_child/EVIDENCE_SLOTS.json"
            ),
            "taskpack_manifest_ref": (
                "artifacts/agent_harness/v48e/reference_child/taskpack_manifest.json"
            ),
            "pipeline_profile_ref": (
                "artifacts/agent_harness/v48e/reference_child/pipeline_profile.json"
            ),
            "profile_registry_ref": (
                "artifacts/agent_harness/v48e/reference_child/taskpack_profile_registry.json"
            ),
            "semantic_hash": "derived-by-model-validator",
        }
    )
    _write_json(root / child_compiled_binding_ref, child_compiled_binding.model_dump(mode="json"))

    child_boundary = TaskRunBoundaryInstance.model_validate(
        {
            **parent_boundary_payload,
            "boundary_instance_id": (
                "task_run_boundary_instance:childae1bd4dce68ae9f8ff4d230a89f1cfe"
            ),
            "compiled_binding_ref": child_compiled_binding_ref,
            "task_instance_identity": "task:v48e:child_worker_execution",
            "worker_subject_ref": child_worker_subject_ref,
            "semantic_hash": "derived-by-model-validator",
        }
    )
    _write_json(root / child_boundary_instance_ref, child_boundary.model_dump(mode="json"))

    child_report_payload = {
        **parent_report_payload,
        "worker_boundary_conformance_report_id": (
            "worker_boundary_conformance_report:child6e93ef9c5cb1257000d2"
        ),
        "compiled_binding_ref": child_compiled_binding_ref,
        "boundary_instance_ref": child_boundary_instance_ref,
        "task_instance_identity": "task:v48e:child_worker_execution",
        "worker_subject_ref": child_worker_subject_ref,
        "overall_judgment": child_overall_judgment,
        "supporting_diagnostic_ids": (
            ["incomplete_evidence:lineage_mismatch"]
            if child_overall_judgment == "incomplete_evidence"
            else []
        ),
        "semantic_hash": "derived-by-model-validator",
    }
    child_report = WorkerBoundaryConformanceReport.model_validate(child_report_payload)
    _write_json(root / child_report_ref, child_report.model_dump(mode="json"))

    return {
        "root": root,
        "parent_report_ref": parent_report_ref,
        "child_report_ref": child_report_ref,
        "parent_boundary_ref": parent_boundary_instance_ref,
        "child_boundary_ref": child_boundary_instance_ref,
        "parent_compiled_binding_ref": parent_compiled_binding_ref,
        "child_compiled_binding_ref": child_compiled_binding_ref,
    }


def _build_topology(
    seeded: dict[str, Any],
    *,
    out_dir: str,
    parent_role_kind: str = "supervisor",
    child_role_kind: str = "worker",
) -> WorkerDelegationTopology:
    return build_v48e_worker_delegation_topology(
        parent_worker_boundary_conformance_report_refs=[seeded["parent_report_ref"]],
        child_worker_boundary_conformance_report_refs=[seeded["child_report_ref"]],
        parent_role_kinds=[parent_role_kind],
        child_role_kinds=[child_role_kind],
        delegation_edge_ids=["delegation_edge:v48e:reference_handoff"],
        delegated_task_identities=["task:v48e:delegated_patch_slice"],
        out_dir=out_dir,
        repo_root_path=seeded["root"],
    ).topology


def test_v48e_reference_worker_delegation_topology_replays_deterministically(
    tmp_path: Path,
) -> None:
    seeded = _seed_v48e_inputs(tmp_path)
    first = build_v48e_worker_delegation_topology(
        parent_worker_boundary_conformance_report_refs=[seeded["parent_report_ref"]],
        child_worker_boundary_conformance_report_refs=[seeded["child_report_ref"]],
        parent_role_kinds=["supervisor"],
        child_role_kinds=["worker"],
        delegation_edge_ids=["delegation_edge:v48e:reference_handoff"],
        delegated_task_identities=["task:v48e:delegated_patch_slice"],
        out_dir="artifacts/agent_harness/v48e/reference_topology",
        repo_root_path=seeded["root"],
    )
    before = first.topology_path.read_bytes()
    second = build_v48e_worker_delegation_topology(
        parent_worker_boundary_conformance_report_refs=[seeded["parent_report_ref"]],
        child_worker_boundary_conformance_report_refs=[seeded["child_report_ref"]],
        parent_role_kinds=["supervisor"],
        child_role_kinds=["worker"],
        delegation_edge_ids=["delegation_edge:v48e:reference_handoff"],
        delegated_task_identities=["task:v48e:delegated_patch_slice"],
        out_dir="artifacts/agent_harness/v48e/reference_topology",
        repo_root_path=seeded["root"],
    )

    assert first.topology.model_dump(mode="json") == _read_fixture(
        "reference_worker_delegation_topology.json"
    )
    assert before == second.topology_path.read_bytes()


def test_v48e_reference_rejected_compiled_boundary_mismatch_fixture_replays(
    tmp_path: Path,
) -> None:
    seeded = _seed_v48e_inputs(
        tmp_path,
        child_compiled_boundary_identity_hash="f" * 64,
    )
    topology = _build_topology(
        seeded,
        out_dir="artifacts/agent_harness/v48e/rejected_boundary_mismatch",
    )

    assert topology.model_dump(mode="json") == _read_fixture(
        "reference_worker_delegation_topology_rejected_compiled_boundary_mismatch.json"
    )


def test_v48e_reference_incomplete_lineage_fixture_replays(tmp_path: Path) -> None:
    seeded = _seed_v48e_inputs(
        tmp_path,
        child_overall_judgment="incomplete_evidence",
    )
    topology = _build_topology(
        seeded,
        out_dir="artifacts/agent_harness/v48e/incomplete_lineage",
    )

    assert topology.model_dump(mode="json") == _read_fixture(
        "reference_worker_delegation_topology_incomplete_lineage.json"
    )


def test_v48e_models_accept_committed_reference_payloads() -> None:
    topology = WorkerDelegationTopology.model_validate(
        _read_fixture("reference_worker_delegation_topology.json")
    )
    assert topology.schema == WORKER_DELEGATION_TOPOLOGY_SCHEMA


def test_v48e_rejects_raw_v48d_bypass(tmp_path: Path) -> None:
    seeded = _seed_v48e_inputs(tmp_path)
    with pytest.raises(WorkerDelegationTopologyError, match=AHK6002_SCHEMA_MISMATCH):
        build_v48e_worker_delegation_topology(
            parent_worker_boundary_conformance_report_refs=[seeded["parent_boundary_ref"]],
            child_worker_boundary_conformance_report_refs=[seeded["child_report_ref"]],
            parent_role_kinds=["supervisor"],
            child_role_kinds=["worker"],
            delegation_edge_ids=["delegation_edge:v48e:raw_bypass"],
            delegated_task_identities=["task:v48e:delegated_patch_slice"],
            out_dir="artifacts/agent_harness/v48e/reject_raw_bypass",
            repo_root_path=seeded["root"],
        )


def test_v48e_marks_same_worker_subject_as_rejected(tmp_path: Path) -> None:
    seeded = _seed_v48e_inputs(
        tmp_path,
        child_worker_subject_ref="worker:repo_internal_single_codex_worker:default",
    )
    topology = _build_topology(
        seeded,
        out_dir="artifacts/agent_harness/v48e/rejected_same_subject",
    )

    assert topology.handoff_result == "rejected"
    assert topology.supporting_diagnostic_families == ["recursive_topology_forbidden"]


def test_v48e_marks_swapped_roles_as_rejected(tmp_path: Path) -> None:
    seeded = _seed_v48e_inputs(tmp_path)
    topology = _build_topology(
        seeded,
        out_dir="artifacts/agent_harness/v48e/rejected_swapped_roles",
        parent_role_kind="worker",
        child_role_kind="supervisor",
    )

    assert topology.handoff_result == "rejected"
    assert "role_ambiguity" in topology.supporting_diagnostic_families


def test_v48e_parent_and_child_reports_keep_v48d_schema() -> None:
    parent_fixture = _load_repo_fixture(
        "packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report.json"
    )
    assert parent_fixture["schema"] == WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA
