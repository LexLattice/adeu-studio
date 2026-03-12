from __future__ import annotations

import json
import shutil
import sqlite3
import time
from collections.abc import Callable
from dataclasses import replace
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest
import urm_runtime.orchestration_evidence as orchestration_evidence_module
from adeu_api.urm_routes import (
    _get_manager,
    _reset_manager_for_tests,
    urm_agent_cancel_endpoint,
    urm_agent_spawn_endpoint,
    urm_approval_issue_endpoint,
    urm_approval_revoke_endpoint,
    urm_connector_snapshot_create_endpoint,
    urm_connector_snapshot_get_endpoint,
    urm_copilot_events_endpoint,
    urm_copilot_mode_endpoint,
    urm_copilot_send_endpoint,
    urm_copilot_start_endpoint,
    urm_copilot_steer_endpoint,
    urm_copilot_stop_endpoint,
    urm_copilot_topology_endpoint,
    urm_copilot_visibility_endpoint,
    urm_policy_active_endpoint,
    urm_policy_profile_current_endpoint,
    urm_policy_profile_list_endpoint,
    urm_policy_profile_select_endpoint,
    urm_policy_rollback_endpoint,
    urm_policy_rollout_endpoint,
    urm_tool_call_endpoint,
)
from fastapi import HTTPException
from fastapi.responses import StreamingResponse
from jsonschema import Draft202012Validator
from pydantic import ValidationError
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.errors import URMError
from urm_runtime.hashing import canonical_json, sha256_canonical_json
from urm_runtime.instruction_policy import (
    compute_policy_hash,
    load_instruction_policy,
    policy_semantic_form,
)
from urm_runtime.models import (
    AgentCancelRequest,
    AgentSpawnRequest,
    AgentSpawnResponse,
    ApprovalIssueRequest,
    ApprovalRevokeRequest,
    ConnectorSnapshotCreateRequest,
    CopilotModeRequest,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotSteerRequest,
    CopilotStopRequest,
    PolicyProfileSelectRequest,
    PolicyRollbackRequest,
    PolicyRolloutRequest,
    ToolCallRequest,
)
from urm_runtime.orchestration_evidence import (
    OrchestrationEvidenceError,
    materialize_v35a_orchestration_state_evidence,
    materialize_v35b_delegation_handoff_evidence,
    materialize_v35c_transcript_visibility_evidence,
    materialize_v35d_topology_duty_map_evidence,
    materialize_v35e_runtime_enforcement_evidence,
)
from urm_runtime.orchestration_state import (
    ExecutionTopologyState,
    MaterializedOrchestrationArtifacts,
    RoleHandoffEntry,
    RoleHandoffEnvelope,
    WriteLeaseState,
)
from urm_runtime.policy_governance import materialize_policy
from urm_runtime.storage import (
    get_dispatch_token_for_child,
    get_parent_budget_total,
    get_worker_run,
    lease_dispatch_token,
    persist_copilot_session_start,
    persist_worker_run_start,
    set_dispatch_token_phase,
    transaction,
    update_copilot_session_status,
    upsert_dispatch_token_queued,
)
from urm_runtime.topology_duty_map import (
    MaterializedTopologyDutyMapArtifacts,
    TopologyDutyMapSourceArtifacts,
    TopologyDutyMapStateError,
    build_topology_duty_map_state,
)
from urm_runtime.worker_visibility import (
    MaterializedWorkerVisibilityArtifacts,
    WorkerVisibilityState,
)


def _prepare_fake_codex(*, tmp_path: Path) -> Path:
    fixture = Path(__file__).resolve().parent / "fixtures" / "codex_app_server" / "fake_codex.py"
    target = tmp_path / "fake_codex.py"
    shutil.copy2(fixture, target)
    target.chmod(0o755)
    return target


def _write_profile_registry(
    *,
    path: Path,
    default_policy_hash: str,
    allowed_policy_hashes: list[str],
) -> None:
    payload = {
        "schema": "policy.profiles.v1",
        "profiles": [
            {
                "profile_id": "default",
                "profile_version": "profile.v1",
                "default_policy_hash": default_policy_hash,
                "allowed_policy_hashes": sorted(allowed_policy_hashes),
                "policy_ref": "policy/odeu.instructions.v1.json",
            }
        ],
    }
    path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")


def _materialize_policy_file(
    *,
    config: URMRuntimeConfig,
    policy_path: Path,
    materialized_at: str,
) -> str:
    policy = load_instruction_policy(policy_path=policy_path, strict=True)
    policy_hash = compute_policy_hash(policy)
    materialize_policy(
        config=config,
        policy_hash=policy_hash,
        schema_id=policy.schema_id,
        policy_schema_version="odeu.instructions.schema.v1",
        policy_ir_version="odeu.instructions.v1",
        semantic_policy_json=policy_semantic_form(policy),
        source_policy_ref=str(policy_path),
        materialized_at=materialized_at,
    )
    return policy_hash


def _wait_for(
    predicate: Callable[[], bool],
    *,
    timeout_secs: float,
    interval_secs: float = 0.02,
) -> bool:
    deadline = time.monotonic() + timeout_secs
    while time.monotonic() < deadline:
        if predicate():
            return True
        time.sleep(interval_secs)
    return bool(predicate())


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _load_materialized_json(*, config: URMRuntimeConfig, relative_path: str) -> dict[str, object]:
    return json.loads((config.var_root / relative_path).read_text(encoding="utf-8"))


def _delegated_scope_payload(
    *,
    kind: str,
    values: list[str] | None = None,
    artifact_surfaces: list[str] | None = None,
    rationale: str | None = None,
) -> dict[str, object]:
    return {
        "kind": kind,
        "values": values or [],
        "artifact_surfaces": artifact_surfaces or [],
        "rationale": rationale,
    }


def _persisted_child_delegation_payload(
    *,
    requested_role: str = "explorer",
    granted_role: str | None = None,
    delegation_task_kind: str = "analysis_task",
    delegated_scope: dict[str, object] | None = None,
    authoritative_write_lease_granted: bool = False,
) -> dict[str, object]:
    resolved_granted_role = granted_role or requested_role
    resolved_scope = delegated_scope or _delegated_scope_payload(
        kind="artifact_surface_only",
        artifact_surfaces=["none"],
        rationale="persisted support-role recovery scope",
    )
    return {
        "requested_role": requested_role,
        "granted_role": resolved_granted_role,
        "delegation_task_kind": delegation_task_kind,
        "delegated_scope": resolved_scope,
        "authoritative_write_lease_granted": authoritative_write_lease_granted,
    }


def _budget_snapshot_v1(
    *,
    max_solver_calls: int,
    max_duration_secs: int,
    max_token_budget: int,
    remaining_parent_duration_secs: int,
    accounting_model: str = "running_total_v1",
    token_usage_unobserved: bool = True,
) -> dict[str, object]:
    return {
        "budget_version": "budget.v1",
        "accounting_model": accounting_model,
        "max_solver_calls": max_solver_calls,
        "max_duration_secs": max_duration_secs,
        "max_token_budget": max_token_budget,
        "remaining_parent_duration_secs": remaining_parent_duration_secs,
        "token_usage_unobserved": token_usage_unobserved,
    }


def _write_stop_gate_metrics_fixture(
    *,
    repo_root: Path,
    baseline_rel: str = "artifacts/stop_gate/metrics_v55_closeout.json",
    current_rel: str = "artifacts/stop_gate/metrics_v56_closeout.json",
) -> tuple[str, str]:
    metric_keys = [f"metric_{index:02d}" for index in range(80)]
    payload = {
        "schema": "stop_gate_metrics@1",
        "metrics": {key: 100.0 for key in metric_keys},
        "runtime_observability": {
            "elapsed_ms": 80,
            "total_fixtures": 22,
            "total_replays": 78,
            "bytes_hashed_per_replay": 68230,
            "bytes_hashed_total": 204690,
        },
    }
    for relative_path in (baseline_rel, current_rel):
        target = repo_root / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(canonical_json(payload) + "\n", encoding="utf-8")
    return baseline_rel, current_rel


def _materialize_v35a_evidence(
    *,
    repo_root: Path,
    config: URMRuntimeConfig,
    artifacts: MaterializedOrchestrationArtifacts,
) -> dict[str, object]:
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    evidence = materialize_v35a_orchestration_state_evidence(
        repo_root=repo_root,
        var_root=config.var_root,
        artifacts=artifacts,
        output_path="artifacts/agent_harness/v56/evidence_inputs/v35a_orchestration_state_evidence_v56.json",
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v35b_evidence(
    *,
    repo_root: Path,
    config: URMRuntimeConfig,
    artifacts: MaterializedOrchestrationArtifacts,
) -> dict[str, object]:
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel="artifacts/stop_gate/metrics_v56_closeout.json",
        current_rel="artifacts/stop_gate/metrics_v57_closeout.json",
    )
    evidence = materialize_v35b_delegation_handoff_evidence(
        repo_root=repo_root,
        var_root=config.var_root,
        artifacts=artifacts,
        output_path="artifacts/agent_harness/v57/evidence_inputs/v35b_delegation_handoff_evidence_v57.json",
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v35c_evidence(
    *,
    repo_root: Path,
    config: URMRuntimeConfig,
    orchestration_artifacts: MaterializedOrchestrationArtifacts,
    visibility_artifacts: MaterializedWorkerVisibilityArtifacts,
) -> dict[str, object]:
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel="artifacts/stop_gate/metrics_v57_closeout.json",
        current_rel="artifacts/stop_gate/metrics_v58_closeout.json",
    )
    evidence = materialize_v35c_transcript_visibility_evidence(
        repo_root=repo_root,
        var_root=config.var_root,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
        output_path="artifacts/agent_harness/v58/evidence_inputs/v35c_transcript_visibility_evidence_v58.json",
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v35d_evidence(
    *,
    repo_root: Path,
    config: URMRuntimeConfig,
    orchestration_artifacts: MaterializedOrchestrationArtifacts,
    visibility_artifacts: MaterializedWorkerVisibilityArtifacts,
    topology_artifacts: MaterializedTopologyDutyMapArtifacts,
) -> dict[str, object]:
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel="artifacts/stop_gate/metrics_v58_closeout.json",
        current_rel="artifacts/stop_gate/metrics_v59_closeout.json",
    )
    evidence = materialize_v35d_topology_duty_map_evidence(
        repo_root=repo_root,
        var_root=config.var_root,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
        topology_artifacts=topology_artifacts,
        output_path="artifacts/agent_harness/v59/evidence_inputs/v35d_topology_duty_map_evidence_v59.json",
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v35e_evidence(
    *,
    repo_root: Path,
    config: URMRuntimeConfig,
    orchestration_artifacts: MaterializedOrchestrationArtifacts,
    visibility_artifacts: MaterializedWorkerVisibilityArtifacts,
    topology_artifacts: MaterializedTopologyDutyMapArtifacts,
) -> dict[str, object]:
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel="artifacts/stop_gate/metrics_v59_closeout.json",
        current_rel="artifacts/stop_gate/metrics_v60_closeout.json",
    )
    evidence = materialize_v35e_runtime_enforcement_evidence(
        repo_root=repo_root,
        var_root=config.var_root,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
        topology_artifacts=topology_artifacts,
        output_path="artifacts/agent_harness/v60/evidence_inputs/v35e_runtime_enforcement_evidence_v60.json",
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v35b_builder_support_artifacts(
    *,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[URMRuntimeConfig, MaterializedOrchestrationArtifacts]:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.4")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="v35b-evidence-start-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="v35b-evidence-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "v35b-evidence-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    support_spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="v35b-evidence-support-spawn-1",
            prompt="inspect the api lane",
            target_turn_id="turn-v35b-support-1",
        )
    )

    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(support_spawn.child_id)) is not None
            and child.status == "completed"
            and child.persisted
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )

    builder_spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="v35b-evidence-builder-spawn-1",
            prompt="implement the api lane",
            target_turn_id="turn-v35b-builder-1",
            requested_role="builder_worker",
            delegation_task_kind="write_task",
            delegated_scope=_delegated_scope_payload(
                kind="subtree",
                values=["apps/api"],
                artifact_surfaces=["implementation"],
                rationale="scoped implementation write task",
            ),
        )
    )

    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(builder_spawn.child_id)) is not None
            and child.status == "completed"
            and child.persisted
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=session_id)
    return config, artifacts


def _materialize_v35c_builder_support_artifacts(
    *,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[
    URMRuntimeConfig,
    MaterializedOrchestrationArtifacts,
    MaterializedWorkerVisibilityArtifacts,
]:
    config, orchestration_artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    manager = _get_manager()
    visibility_artifacts = manager.materialize_worker_visibility_state(
        session_id=orchestration_artifacts.session_id
    )
    return config, orchestration_artifacts, visibility_artifacts


def _materialize_v35c_bridge_artifacts(
    *,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[
    URMRuntimeConfig,
    MaterializedOrchestrationArtifacts,
    MaterializedWorkerVisibilityArtifacts,
]:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "v35c-bridge-child-1"
    parent_session_id = "v35c-bridge-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-v35c-bridge-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                **_persisted_child_delegation_payload(),
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 9,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=9,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    manager = _get_manager()
    orchestration_artifacts = manager.materialize_orchestration_state(session_id=parent_session_id)
    visibility_artifacts = manager.materialize_worker_visibility_state(session_id=parent_session_id)
    return config, orchestration_artifacts, visibility_artifacts


def _materialize_v35d_builder_support_artifacts(
    *,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[
    URMRuntimeConfig,
    MaterializedOrchestrationArtifacts,
    MaterializedWorkerVisibilityArtifacts,
    MaterializedTopologyDutyMapArtifacts,
]:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    manager = _get_manager()
    topology_artifacts = manager.materialize_topology_duty_map_state(
        session_id=orchestration_artifacts.session_id
    )
    return config, orchestration_artifacts, visibility_artifacts, topology_artifacts


def _materialize_v35d_running_builder_artifacts(
    *,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[URMRuntimeConfig, str, str, MaterializedTopologyDutyMapArtifacts]:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "1.0")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(
            provider="codex",
            client_request_id="v35d-running-builder-start-1",
        )
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="v35d-running-builder-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "v35d-running-builder-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )
    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="v35d-running-builder-spawn-1",
            prompt="implement the api lane",
            target_turn_id="turn-v35d-running-builder-1",
            requested_role="builder_worker",
            delegation_task_kind="write_task",
            delegated_scope=_delegated_scope_payload(
                kind="subtree",
                values=["apps/api"],
                artifact_surfaces=["implementation"],
                rationale="scoped implementation write task",
            ),
        )
    )

    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.status == "running"
            and child.child_thread_id is not None
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    config = URMRuntimeConfig.from_env()
    topology_artifacts = manager.materialize_topology_duty_map_state(session_id=session_id)
    return config, session_id, spawn.child_id, topology_artifacts


def _materialize_v35c_running_artifacts(
    *,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[
    URMRuntimeConfig,
    MaterializedOrchestrationArtifacts,
    MaterializedWorkerVisibilityArtifacts,
]:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "1.0")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="v35c-running-start-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="v35c-running-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "v35c-running-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="v35c-running-spawn-1",
            prompt="inspect the api lane",
            target_turn_id="turn-v35c-running-1",
        )
    )

    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.status == "running"
            and child.child_thread_id is not None
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    config = URMRuntimeConfig.from_env()
    orchestration_artifacts = manager.materialize_orchestration_state(session_id=session_id)
    visibility_artifacts = manager.materialize_worker_visibility_state(session_id=session_id)
    return config, orchestration_artifacts, visibility_artifacts


def _rewrite_orchestration_artifact(
    *,
    config: URMRuntimeConfig,
    artifacts: MaterializedOrchestrationArtifacts,
    field_name: str,
    payload: dict[str, object],
) -> MaterializedOrchestrationArtifacts:
    artifact = getattr(artifacts, field_name)
    path = config.var_root / artifact.path
    path.write_text(canonical_json(payload), encoding="utf-8")
    updated_artifact = replace(
        artifact,
        hash=sha256_canonical_json(payload),
        payload=payload,
    )
    return replace(artifacts, **{field_name: updated_artifact})


def _rewrite_visibility_artifact(
    *,
    config: URMRuntimeConfig,
    artifacts: MaterializedWorkerVisibilityArtifacts,
    payload: dict[str, object],
) -> MaterializedWorkerVisibilityArtifacts:
    artifact = artifacts.worker_visibility_state
    path = config.var_root / artifact.path
    path.write_text(canonical_json(payload), encoding="utf-8")
    return replace(
        artifacts,
        worker_visibility_state=replace(
            artifact,
            hash=sha256_canonical_json(payload),
            payload=payload,
        ),
    )


def _rewrite_topology_artifact(
    *,
    config: URMRuntimeConfig,
    artifacts: MaterializedTopologyDutyMapArtifacts,
    payload: dict[str, object],
) -> MaterializedTopologyDutyMapArtifacts:
    artifact = artifacts.topology_duty_map_state
    path = config.var_root / artifact.path
    path.write_text(canonical_json(payload), encoding="utf-8")
    return replace(
        artifacts,
        topology_duty_map_state=replace(
            artifact,
            hash=sha256_canonical_json(payload),
            payload=payload,
        ),
    )


def _topology_source_artifacts(
    *,
    orchestration_artifacts: MaterializedOrchestrationArtifacts,
    visibility_artifacts: MaterializedWorkerVisibilityArtifacts,
) -> TopologyDutyMapSourceArtifacts:
    return TopologyDutyMapSourceArtifacts(
        execution_topology_state_path=orchestration_artifacts.execution_topology_state.path,
        write_lease_state_path=orchestration_artifacts.write_lease_state.path,
        worker_visibility_state_path=visibility_artifacts.worker_visibility_state.path,
        role_handoff_envelope_path=orchestration_artifacts.role_handoff_envelope.path,
    )


def test_materialize_policy_rejects_conflicting_payload_for_existing_hash(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    config = URMRuntimeConfig.from_env()
    base_policy_path = Path(__file__).resolve().parents[3] / "policy" / "odeu.instructions.v1.json"

    policy = load_instruction_policy(policy_path=base_policy_path, strict=True)
    policy_hash = compute_policy_hash(policy)
    semantic = policy_semantic_form(policy)
    materialize_policy(
        config=config,
        policy_hash=policy_hash,
        schema_id=policy.schema_id,
        policy_schema_version="odeu.instructions.schema.v1",
        policy_ir_version="odeu.instructions.v1",
        semantic_policy_json=semantic,
        source_policy_ref=str(base_policy_path),
        materialized_at="2026-02-13T10:00:00Z",
    )

    conflicting_semantic = dict(semantic)
    conflicting_semantic["rules"] = []
    with pytest.raises(URMError) as exc_info:
        materialize_policy(
            config=config,
            policy_hash=policy_hash,
            schema_id=policy.schema_id,
            policy_schema_version="odeu.instructions.schema.v1",
            policy_ir_version="odeu.instructions.v1",
            semantic_policy_json=conflicting_semantic,
            source_policy_ref=str(tmp_path / "conflicting.policy.json"),
            materialized_at="2026-02-13T10:01:00Z",
        )

    assert exc_info.value.status_code == 409
    assert exc_info.value.detail.code == "URM_POLICY_DENIED"


def test_runtime_config_defaults_child_queue_mode_v2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.delenv("URM_CHILD_QUEUE_MODE", raising=False)
    config = URMRuntimeConfig.from_env()
    assert config.child_queue_mode == "v2"


def test_copilot_start_send_stop_and_sse_replay(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(
            provider="codex",
            client_request_id="start-1",
            profile_id="safe_mode",
        )
    )
    session_id = start.session_id
    assert start.status == "running"
    assert start.profile_id == "safe_mode"
    assert start.profile_version == "profile.v1"
    assert start.idempotent_replay is False

    send = urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-1",
            message={"jsonrpc": "2.0", "id": "req-1", "method": "ping"},
        )
    )
    assert send.status == "running"

    stop = urm_copilot_stop_endpoint(CopilotStopRequest(provider="codex", session_id=session_id))
    assert stop.status in {"stopped", "failed"}

    stream_response = urm_copilot_events_endpoint(
        session_id=session_id,
        after_seq=0,
        provider="codex",
        max_events=10,
    )
    assert isinstance(stream_response, StreamingResponse)

    manager = _get_manager()
    events, status = manager.iter_events(session_id=session_id, after_seq=0)
    assert status in {"stopped", "failed"}
    assert events
    assert any(event.event_kind == "PROFILE_SELECTED" for event in events)
    _reset_manager_for_tests()


def test_copilot_start_rejects_unknown_profile(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_start_endpoint(
            CopilotSessionStartRequest(
                provider="codex",
                client_request_id="start-invalid-profile-1",
                profile_id="unknown_profile",
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_POLICY_PROFILE_NOT_FOUND"
    _reset_manager_for_tests()


def test_policy_profile_list_current_select_surfaces(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-profile-surface-1")
    )
    session_id = start.session_id
    assert start.profile_id == "default"

    listing = urm_policy_profile_list_endpoint(provider="codex")
    listed_profile_ids = [profile.profile_id for profile in listing.profiles]
    assert listed_profile_ids == sorted(listed_profile_ids)
    assert listed_profile_ids == ["default", "experimental", "safe_mode"]

    current = urm_policy_profile_current_endpoint(session_id=session_id, provider="codex")
    assert current.profile_id == "default"
    assert current.profile_version == "profile.v1"
    assert len(current.policy_hash) == 64

    selected = urm_policy_profile_select_endpoint(
        PolicyProfileSelectRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="profile-select-1",
            profile_id="safe_mode",
        )
    )
    assert selected.idempotent_replay is False
    assert selected.profile_id == "safe_mode"
    assert selected.profile_version == "profile.v1"
    assert len(selected.policy_hash) == 64

    selected_replay = urm_policy_profile_select_endpoint(
        PolicyProfileSelectRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="profile-select-1",
            profile_id="safe_mode",
        )
    )
    assert selected_replay.profile_id == "safe_mode"
    assert selected_replay.idempotent_replay is True

    current_after = urm_policy_profile_current_endpoint(session_id=session_id, provider="codex")
    assert current_after.profile_id == "safe_mode"

    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-profile-surface-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-profile-surface-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawned = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-profile-surface-1",
            prompt="profile check",
            target_turn_id="turn-profile-surface-1",
            use_last_turn=False,
        )
    )
    assert spawned.profile_id == "safe_mode"

    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "PROFILE_SELECTED"
        and event.payload.get("scope") == "session"
        and event.payload.get("profile_id") == "safe_mode"
        for event in events
    )
    _reset_manager_for_tests()


def test_policy_profile_select_rejects_unknown_profile_and_emits_denial(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-profile-denied-1")
    )
    session_id = start.session_id

    with pytest.raises(HTTPException) as exc_info:
        urm_policy_profile_select_endpoint(
            PolicyProfileSelectRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="profile-select-denied-1",
                profile_id="unknown_profile",
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_POLICY_PROFILE_NOT_FOUND"

    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "PROFILE_DENIED"
        and event.payload.get("scope") == "session"
        and event.payload.get("profile_id") == "unknown_profile"
        for event in events
    )
    _reset_manager_for_tests()


def test_policy_rollout_rollback_active_and_session_snapshot_behavior(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)

    base_policy_path = Path(__file__).resolve().parents[3] / "policy" / "odeu.instructions.v1.json"
    alt_policy_path = tmp_path / "odeu.instructions.alt.v1.json"
    disallowed_policy_path = tmp_path / "odeu.instructions.disallowed.v1.json"
    base_payload = json.loads(base_policy_path.read_text(encoding="utf-8"))
    assert isinstance(base_payload, dict)
    rules = base_payload.get("rules")
    assert isinstance(rules, list) and rules
    first_rule = rules[0]
    assert isinstance(first_rule, dict)
    first_rule["code"] = "ALLOW_HARD_GATED_ACTION_ALT"
    alt_policy_path.write_text(json.dumps(base_payload, sort_keys=True), encoding="utf-8")
    first_rule["code"] = "ALLOW_HARD_GATED_ACTION_DISALLOWED"
    disallowed_policy_path.write_text(json.dumps(base_payload, sort_keys=True), encoding="utf-8")

    config = URMRuntimeConfig.from_env()
    default_hash = _materialize_policy_file(
        config=config,
        policy_path=base_policy_path,
        materialized_at="2026-02-13T10:00:00Z",
    )
    alt_hash = _materialize_policy_file(
        config=config,
        policy_path=alt_policy_path,
        materialized_at="2026-02-13T10:05:00Z",
    )
    disallowed_hash = _materialize_policy_file(
        config=config,
        policy_path=disallowed_policy_path,
        materialized_at="2026-02-13T10:06:00Z",
    )

    registry_path = tmp_path / "profiles.v1.json"
    _write_profile_registry(
        path=registry_path,
        default_policy_hash=default_hash,
        allowed_policy_hashes=[default_hash, alt_hash],
    )
    monkeypatch.setenv("URM_POLICY_PROFILES_PATH", str(registry_path))
    _reset_manager_for_tests()

    active_before = urm_policy_active_endpoint(profile_id="default", provider="codex")
    assert active_before.policy_hash == default_hash
    assert active_before.source == "profile_default"

    with pytest.raises(HTTPException) as disallowed_exc:
        urm_policy_rollout_endpoint(
            PolicyRolloutRequest(
                provider="codex",
                client_request_id="rollout-disallowed-1",
                profile_id="default",
                target_policy_hash=disallowed_hash,
                activation_ts="2026-02-13T10:09:00Z",
            )
        )
    assert disallowed_exc.value.status_code == 400
    assert disallowed_exc.value.detail["code"] == "URM_POLICY_ROLLOUT_HASH_NOT_ALLOWED"

    first_rollout = urm_policy_rollout_endpoint(
        PolicyRolloutRequest(
            provider="codex",
            client_request_id="rollout-seed-default-1",
            profile_id="default",
            target_policy_hash=default_hash,
            activation_ts="2026-02-13T10:10:00Z",
        )
    )
    assert first_rollout.idempotent_replay is False
    assert first_rollout.target_policy_hash == default_hash

    first_rollout_replay = urm_policy_rollout_endpoint(
        PolicyRolloutRequest(
            provider="codex",
            client_request_id="rollout-seed-default-1",
            profile_id="default",
            target_policy_hash=default_hash,
            activation_ts="2026-02-13T10:11:00Z",
        )
    )
    assert first_rollout_replay.idempotent_replay is True
    assert first_rollout_replay.activation_seq == first_rollout.activation_seq
    assert first_rollout_replay.activation_ts == first_rollout.activation_ts

    rollout_alt = urm_policy_rollout_endpoint(
        PolicyRolloutRequest(
            provider="codex",
            client_request_id="rollout-alt-1",
            profile_id="default",
            target_policy_hash=alt_hash,
            activation_ts="2026-02-13T10:12:00Z",
        )
    )
    assert rollout_alt.target_policy_hash == alt_hash

    start_after_rollout = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-after-rollout-a4-1")
    )
    session_id = start_after_rollout.session_id
    current_after_rollout = urm_policy_profile_current_endpoint(
        session_id=session_id,
        provider="codex",
    )
    assert current_after_rollout.policy_hash == alt_hash

    with pytest.raises(HTTPException) as conflict_exc:
        urm_policy_rollout_endpoint(
            PolicyRolloutRequest(
                provider="codex",
                client_request_id="rollout-alt-conflict-1",
                profile_id="default",
                target_policy_hash=alt_hash,
                activation_ts="2026-02-13T10:13:00Z",
            )
        )
    assert conflict_exc.value.status_code == 409
    assert conflict_exc.value.detail["code"] == "URM_POLICY_ROLLOUT_CONFLICT"

    with pytest.raises(HTTPException) as rollback_missing_exc:
        urm_policy_rollback_endpoint(
            PolicyRollbackRequest(
                provider="codex",
                client_request_id="rollback-missing-1",
                profile_id="default",
                target_policy_hash="f" * 64,
                activation_ts="2026-02-13T10:14:00Z",
            )
        )
    assert rollback_missing_exc.value.status_code == 400
    assert rollback_missing_exc.value.detail["code"] == "URM_POLICY_ROLLBACK_TARGET_NOT_FOUND"

    rollback_default = urm_policy_rollback_endpoint(
        PolicyRollbackRequest(
            provider="codex",
            client_request_id="rollback-default-1",
            profile_id="default",
            target_policy_hash=default_hash,
            activation_ts="2026-02-13T10:15:00Z",
        )
    )
    assert rollback_default.action == "rollback"
    assert rollback_default.target_policy_hash == default_hash

    active_after_rollback = urm_policy_active_endpoint(profile_id="default", provider="codex")
    assert active_after_rollback.policy_hash == default_hash
    assert active_after_rollback.source == "activation_log"
    assert active_after_rollback.action == "rollback"

    current_existing_session = urm_policy_profile_current_endpoint(
        session_id=session_id,
        provider="codex",
    )
    assert current_existing_session.policy_hash == alt_hash

    with pytest.raises(HTTPException) as idem_conflict_exc:
        urm_policy_rollout_endpoint(
            PolicyRolloutRequest(
                provider="codex",
                client_request_id="rollout-alt-1",
                profile_id="default",
                target_policy_hash=default_hash,
                activation_ts="2026-02-13T10:16:00Z",
            )
        )
    assert idem_conflict_exc.value.status_code == 409
    assert idem_conflict_exc.value.detail["code"] == "URM_POLICY_IDEMPOTENCY_CONFLICT"

    _reset_manager_for_tests()


def test_copilot_user_message_bootstraps_protocol_and_emits_agent_delta(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-user-msg-1")
    )
    session_id = start.session_id
    assert start.status == "running"

    send = urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-user-msg-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-user-msg-1",
                "method": "copilot.user_message",
                "params": {"text": "hello world"},
            },
        )
    )
    assert send.status == "running"

    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(event.event_kind == "SESSION_READY" for event in events)

    db_path = tmp_path / "adeu.sqlite3"
    with sqlite3.connect(db_path) as con:
        row = con.execute(
            """
            SELECT raw_jsonl_path
            FROM urm_copilot_session
            WHERE copilot_session_id = ?
            """,
            (session_id,),
        ).fetchone()
    assert row is not None
    raw_path = tmp_path / row[0]
    deadline = time.monotonic() + 2.0
    text = ""
    while True:
        text = raw_path.read_text(encoding="utf-8", errors="replace")
        if "agent_message_delta" in text:
            break
        if time.monotonic() >= deadline:
            break
        time.sleep(0.05)

    assert '"method":"turn/start"' in text
    assert "agent_message_delta" in text
    _reset_manager_for_tests()


def test_copilot_steer_endpoint_is_idempotent_and_rate_limited(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-steer-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-steer-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-steer-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (runtime := manager._sessions.get(session_id)) is not None
            and isinstance(runtime.last_turn_id, str)
            and bool(runtime.last_turn_id)
        ),
        timeout_secs=2.0,
        interval_secs=0.02,
    )
    runtime = manager._sessions.get(session_id)  # type: ignore[attr-defined]
    assert runtime is not None
    target_turn_id = runtime.last_turn_id
    assert isinstance(target_turn_id, str) and target_turn_id

    steer = urm_copilot_steer_endpoint(
        CopilotSteerRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="steer-1",
            text="focus on tests first",
            steer_intent_class="reprioritize",
            target_turn_id=target_turn_id,
        )
    )
    assert steer.target_turn_id == target_turn_id
    assert steer.accepted_turn_id == target_turn_id
    assert steer.resolved_against_seq >= 0
    assert steer.idempotent_replay is False

    replay = urm_copilot_steer_endpoint(
        CopilotSteerRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="steer-1",
            text="focus on tests first",
            steer_intent_class="reprioritize",
            target_turn_id=target_turn_id,
        )
    )
    assert replay.accepted_turn_id == steer.accepted_turn_id
    assert replay.resolved_against_seq == steer.resolved_against_seq
    assert replay.idempotent_replay is True

    for idx in range(2, 7):
        if idx < 6:
            response = urm_copilot_steer_endpoint(
                CopilotSteerRequest(
                    provider="codex",
                    session_id=session_id,
                    client_request_id=f"steer-{idx}",
                    text=f"steer-{idx}",
                    target_turn_id=target_turn_id,
                )
            )
            assert response.accepted_turn_id == target_turn_id
            continue
        with pytest.raises(HTTPException) as exc_info:
            urm_copilot_steer_endpoint(
                CopilotSteerRequest(
                    provider="codex",
                    session_id=session_id,
                    client_request_id=f"steer-{idx}",
                    text=f"steer-{idx}",
                    target_turn_id=target_turn_id,
                )
            )
        assert exc_info.value.status_code == 400
        assert exc_info.value.detail["code"] == "URM_STEER_DENIED"
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "STEER_APPLIED"
        and event.payload.get("accepted_turn_id") == target_turn_id
        and isinstance(event.payload.get("resolved_against_seq"), int)
        for event in events
    )
    assert any(
        event.event_kind == "STEER_DENIED"
        and event.payload.get("error_code") == "URM_STEER_DENIED"
        and event.payload.get("target_turn_id") == target_turn_id
        for event in events
    )
    _reset_manager_for_tests()


def test_copilot_steer_last_turn_after_seq_unresolved_emits_denied_event(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-steer-after-seq-1")
    )
    session_id = start.session_id

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_steer_endpoint(
            CopilotSteerRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="steer-after-seq-unresolved-1",
                text="reprioritize work",
                steer_intent_class="reprioritize",
                use_last_turn=True,
                after_seq=0,
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_STEER_TARGET_UNRESOLVED"
    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    denied = [event for event in events if event.event_kind == "STEER_DENIED"]
    assert denied
    latest_denied = denied[-1]
    assert latest_denied.payload.get("error_code") == "URM_STEER_TARGET_UNRESOLVED"
    assert latest_denied.payload.get("resolved_against_seq") == 0
    assert latest_denied.payload.get("target_turn_id") is None
    _reset_manager_for_tests()


def test_agent_spawn_and_cancel_terminal_idempotent(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v1")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-1",
            prompt="summarize this module",
            target_turn_id="turn-bootstrap-1",
            use_last_turn=False,
            profile_id="experimental",
        )
    )
    assert spawn.parent_session_id == session_id
    assert spawn.status in {"completed", "failed"}
    assert spawn.child_id
    assert spawn.parent_stream_id == f"copilot:{session_id}"
    assert spawn.child_stream_id.startswith("child:")
    assert spawn.profile_id == "experimental"
    assert spawn.profile_version == "profile.v1"
    assert spawn.queue_seq == 0
    spawn_replay = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-1",
            prompt="summarize this module",
            target_turn_id="turn-bootstrap-1",
            use_last_turn=False,
            profile_id="experimental",
        )
    )
    assert spawn_replay.child_id == spawn.child_id
    assert spawn_replay.queue_seq == spawn.queue_seq
    assert spawn_replay.idempotent_replay is True

    cancel = urm_agent_cancel_endpoint(
        spawn.child_id,
        AgentCancelRequest(
            provider="codex",
            client_request_id="cancel-child-1",
        ),
    )
    assert cancel.child_id == spawn.child_id
    assert cancel.status in {"completed", "failed", "cancelled"}
    assert cancel.idempotent_replay is False
    assert cancel.error is not None
    assert cancel.error["code"] == "URM_CHILD_CANCEL_ALREADY_TERMINAL"

    cancel_replay = urm_agent_cancel_endpoint(
        spawn.child_id,
        AgentCancelRequest(
            provider="codex",
            client_request_id="cancel-child-1",
        ),
    )
    assert cancel_replay.child_id == spawn.child_id
    assert cancel_replay.idempotent_replay is True
    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert not any(
        event.event_kind == "WORKER_CANCEL"
        and isinstance(event.payload, dict)
        and event.payload.get("worker_id") == spawn.child_id
        for event in events
    )
    assert any(
        event.event_kind == "PROFILE_SELECTED"
        and event.payload.get("scope") == "run"
        and event.payload.get("profile_id") == "experimental"
        for event in events
    )
    with pytest.raises(HTTPException) as bad_profile_exc:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-child-2-bad-profile",
                prompt="summarize this module",
                target_turn_id="turn-bootstrap-1",
                use_last_turn=False,
                profile_id="unknown_profile",
            )
        )
    assert bad_profile_exc.value.status_code == 400
    assert bad_profile_exc.value.detail["code"] == "URM_POLICY_PROFILE_NOT_FOUND"
    events_after_denial, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "PROFILE_DENIED"
        and event.payload.get("profile_id") == "unknown_profile"
        for event in events_after_denial
    )
    _reset_manager_for_tests()


def test_connector_snapshot_create_get_and_idempotency(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv(
        "FAKE_APP_SERVER_APPS_JSON",
        '[{"id":"zeta","name":"Zeta"},{"id":"alpha","name":"Alpha"}]',
    )
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-connector-1")
    )
    session_id = start.session_id
    first = urm_connector_snapshot_create_endpoint(
        ConnectorSnapshotCreateRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="connector-snapshot-1",
        )
    )
    assert first.snapshot_id
    assert first.session_id == session_id
    assert len(first.connector_snapshot_hash) == 64
    assert [item.get("id") for item in first.connectors] == ["alpha", "zeta"]
    assert [item.get("id") for item in first.exposed_connectors] == ["alpha", "zeta"]
    assert [item.connector_id for item in first.connector_exposure] == ["alpha", "zeta"]
    assert all(item.exposed for item in first.connector_exposure)
    assert all(item.deny_reason_code is None for item in first.connector_exposure)

    replay = urm_connector_snapshot_create_endpoint(
        ConnectorSnapshotCreateRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="connector-snapshot-1",
        )
    )
    assert replay.snapshot_id == first.snapshot_id
    assert replay.idempotent_replay is True
    assert replay.exposed_connectors == first.exposed_connectors
    assert replay.connector_exposure == first.connector_exposure

    fetched = urm_connector_snapshot_get_endpoint(
        first.snapshot_id,
        session_id=session_id,
        provider="codex",
    )
    assert fetched.snapshot_id == first.snapshot_id
    assert fetched.connector_snapshot_hash == first.connector_snapshot_hash
    assert fetched.connectors == first.connectors
    assert fetched.exposed_connectors == first.exposed_connectors
    assert fetched.connector_exposure == first.connector_exposure
    snapshot_artifact = tmp_path / "evidence" / "codex" / "connectors" / f"{first.snapshot_id}.json"
    artifact_payload = json.loads(snapshot_artifact.read_text(encoding="utf-8"))
    schema_payload = json.loads(
        (_repo_root() / "spec" / "connector_snapshot.schema.json").read_text(encoding="utf-8")
    )
    schema_errors = sorted(
        Draft202012Validator(schema_payload).iter_errors(artifact_payload),
        key=lambda err: str(err.path),
    )
    assert schema_errors == []
    _reset_manager_for_tests()


def test_connector_snapshot_get_stale_and_not_found(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-connector-2")
    )
    session_id = start.session_id
    created = urm_connector_snapshot_create_endpoint(
        ConnectorSnapshotCreateRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="connector-snapshot-2",
        )
    )

    with pytest.raises(HTTPException) as stale_cap_exc:
        urm_connector_snapshot_get_endpoint(
            created.snapshot_id,
            session_id=session_id,
            provider="codex",
            requested_capability_snapshot_id="different-capability-snapshot-id",
        )
    assert stale_cap_exc.value.status_code == 400
    assert stale_cap_exc.value.detail["code"] == "URM_CONNECTOR_SNAPSHOT_STALE"

    with pytest.raises(HTTPException) as stale_ts_exc:
        urm_connector_snapshot_get_endpoint(
            created.snapshot_id,
            session_id=session_id,
            provider="codex",
            min_acceptable_ts=datetime.now(tz=timezone.utc) + timedelta(minutes=1),
        )
    assert stale_ts_exc.value.status_code == 400
    assert stale_ts_exc.value.detail["code"] == "URM_CONNECTOR_SNAPSHOT_STALE"

    with pytest.raises(HTTPException) as missing_exc:
        urm_connector_snapshot_get_endpoint(
            "missing-snapshot-id",
            session_id=session_id,
            provider="codex",
        )
    assert missing_exc.value.status_code == 404
    assert missing_exc.value.detail["code"] == "URM_CONNECTOR_SNAPSHOT_NOT_FOUND"
    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    connector_fail_codes = [
        event.payload.get("error_code")
        for event in events
        if event.event_kind == "TOOL_CALL_FAIL"
        and isinstance(event.payload, dict)
        and event.payload.get("tool_name") == "urm.connectors.snapshot.get"
    ]
    assert connector_fail_codes[-3:] == [
        "URM_CONNECTOR_SNAPSHOT_STALE",
        "URM_CONNECTOR_SNAPSHOT_STALE",
        "URM_CONNECTOR_SNAPSHOT_NOT_FOUND",
    ]
    replay_fetch = urm_connector_snapshot_get_endpoint(
        created.snapshot_id,
        session_id=session_id,
        provider="codex",
        execution_mode="replay",
        requested_capability_snapshot_id="different-capability-snapshot-id",
        min_acceptable_ts=datetime.now(tz=timezone.utc) + timedelta(minutes=1),
    )
    assert replay_fetch.snapshot_id == created.snapshot_id
    assert replay_fetch.connectors == created.connectors
    assert replay_fetch.exposed_connectors == created.exposed_connectors
    assert replay_fetch.connector_exposure == created.connector_exposure
    assert [item.connector_id for item in replay_fetch.connector_exposure] == [
        item.connector_id for item in created.connector_exposure
    ]
    _reset_manager_for_tests()


def test_connector_snapshot_create_replay_mode_blocks_live_discovery(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-connector-3")
    )
    session_id = start.session_id
    with pytest.raises(HTTPException) as replay_exc:
        urm_connector_snapshot_create_endpoint(
            ConnectorSnapshotCreateRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="connector-snapshot-replay-1",
                execution_mode="replay",
            )
        )
    assert replay_exc.value.status_code == 400
    assert replay_exc.value.detail["code"] == "URM_CONNECTOR_REPLAY_LIVE_READ_BLOCKED"
    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    fail_events = [
        event
        for event in events
        if event.event_kind == "TOOL_CALL_FAIL"
        and isinstance(event.payload, dict)
        and event.payload.get("tool_name") == "urm.connectors.snapshot.create"
    ]
    assert fail_events
    detail = fail_events[-1].payload
    assert detail.get("error_code") == "URM_CONNECTOR_REPLAY_LIVE_READ_BLOCKED"
    assert detail.get("execution_mode") == "replay"
    _reset_manager_for_tests()


def test_agent_spawn_queue_mode_v2_enforces_fifo_and_queue_limit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.6")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-v2-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-v2-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-v2-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn1 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-1",
            prompt="first child",
            target_turn_id="turn-bootstrap-1",
        )
    )
    spawn2 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-2",
            prompt="second child",
            target_turn_id="turn-bootstrap-1",
        )
    )
    assert spawn1.status == "running"
    assert spawn2.status in {"queued", "running"}
    assert spawn1.queue_seq == 1
    assert spawn2.queue_seq == 2
    spawn2_replay = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-2",
            prompt="second child",
            target_turn_id="turn-bootstrap-1",
        )
    )
    assert spawn2_replay.child_id == spawn2.child_id
    assert spawn2_replay.queue_seq == spawn2.queue_seq
    assert spawn2_replay.idempotent_replay is True
    with pytest.raises(HTTPException) as exc_info:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-child-v2-3",
                prompt="third child",
                target_turn_id="turn-bootstrap-1",
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_CHILD_QUEUE_LIMIT_EXCEEDED"

    manager = _get_manager()
    _wait_for(
        lambda: (
            (child1 := manager._child_runs.get(spawn1.child_id)) is not None
            and (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child1.status in {"completed", "failed", "cancelled"}
            and child2.status in {"completed", "failed", "cancelled"}
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )
    child1 = manager._child_runs.get(spawn1.child_id)  # type: ignore[attr-defined]
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child1 is not None and child2 is not None
    assert child1.queue_seq == 1
    assert child2.queue_seq == 2

    child2_events_path = (
        tmp_path / "evidence" / "codex" / "agent" / spawn2.child_id / "urm_events.ndjson"
    )
    child2_payload = child2_events_path.read_text(encoding="utf-8", errors="replace")
    assert '"status":"queued"' in child2_payload
    assert '"status":"running"' in child2_payload
    _reset_manager_for_tests()


def test_agent_spawn_queue_mode_v2_persists_dispatch_tokens_and_worker_start_anchors(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.6")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-v2-r1-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-v2-r1-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-v2-r1-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn1 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-r1-1",
            prompt="first child",
            target_turn_id="turn-bootstrap-r1-1",
        )
    )
    spawn2 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-r1-2",
            prompt="second child",
            target_turn_id="turn-bootstrap-r1-1",
        )
    )
    assert spawn1.queue_seq == 1
    assert spawn2.queue_seq == 2

    manager = _get_manager()
    _wait_for(
        lambda: (
            (child1 := manager._child_runs.get(spawn1.child_id)) is not None
            and (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child1.dispatch_seq is not None
            and child2.dispatch_seq is not None
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )
    child1 = manager._child_runs.get(spawn1.child_id)  # type: ignore[attr-defined]
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child1 is not None and child2 is not None
    assert child1.lease_id == spawn1.child_id
    assert child2.lease_id == spawn2.child_id
    assert child1.dispatch_seq is not None and child2.dispatch_seq is not None
    assert sorted([child1.dispatch_seq, child2.dispatch_seq]) == [1, 2]

    config = URMRuntimeConfig.from_env()
    with transaction(db_path=config.db_path) as con:
        token1 = get_dispatch_token_for_child(con=con, child_id=spawn1.child_id)
        token2 = get_dispatch_token_for_child(con=con, child_id=spawn2.child_id)
    assert token1 is not None and token2 is not None
    assert token1.parent_session_id == session_id
    assert token2.parent_session_id == session_id
    assert token1.queue_seq == 1
    assert token2.queue_seq == 2
    assert token1.worker_run_id == spawn1.child_id
    assert token2.worker_run_id == spawn2.child_id
    assert token1.dispatch_seq is not None
    assert token2.dispatch_seq is not None
    assert sorted([token1.dispatch_seq, token2.dispatch_seq]) == [1, 2]
    assert token1.phase in {"started", "terminal"}
    assert token2.phase in {"started", "terminal"}

    child1_events = (
        tmp_path / "evidence" / "codex" / "agent" / spawn1.child_id / "urm_events.ndjson"
    ).read_text(encoding="utf-8", errors="replace")
    child2_events = (
        tmp_path / "evidence" / "codex" / "agent" / spawn2.child_id / "urm_events.ndjson"
    ).read_text(encoding="utf-8", errors="replace")
    child1_records = [json.loads(line) for line in child1_events.splitlines() if line.strip()]
    child2_records = [json.loads(line) for line in child2_events.splitlines() if line.strip()]
    child1_running = [
        event
        for event in child1_records
        if event.get("event") == "WORKER_START"
        and isinstance(event.get("detail"), dict)
        and event["detail"].get("status") == "running"
    ]
    child2_running = [
        event
        for event in child2_records
        if event.get("event") == "WORKER_START"
        and isinstance(event.get("detail"), dict)
        and event["detail"].get("status") == "running"
    ]
    assert child1_running and child2_running
    child1_detail = child1_running[-1]["detail"]
    child2_detail = child2_running[-1]["detail"]
    assert child1_detail.get("dispatch_seq") == token1.dispatch_seq
    assert child2_detail.get("dispatch_seq") == token2.dispatch_seq
    assert child1_detail.get("lease_id") == token1.worker_run_id
    assert child2_detail.get("lease_id") == token2.worker_run_id
    assert child1_detail.get("parent_stream_id") == f"copilot:{session_id}"
    assert child2_detail.get("parent_stream_id") == f"copilot:{session_id}"
    assert child1_detail.get("child_id") == spawn1.child_id
    assert child2_detail.get("child_id") == spawn2.child_id
    _reset_manager_for_tests()


def test_agent_spawn_queue_mode_v2_cancel_running_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.8")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-v2-cancel-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-v2-cancel-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-v2-cancel-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn1 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-cancel-1",
            prompt="first child",
            target_turn_id="turn-bootstrap-cancel-1",
        )
    )
    spawn2 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-cancel-2",
            prompt="second child",
            target_turn_id="turn-bootstrap-cancel-1",
        )
    )
    assert spawn1.queue_seq == 1
    assert spawn2.queue_seq == 2

    manager = _get_manager()
    _wait_for(
        lambda: (
            (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child2.status in {"queued", "running"}
        ),
        timeout_secs=3.0,
    )
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child2 is not None
    child2_status_before_cancel = child2.status
    assert child2_status_before_cancel in {"queued", "running"}

    cancel = urm_agent_cancel_endpoint(
        spawn1.child_id,
        AgentCancelRequest(
            provider="codex",
            client_request_id="cancel-child-v2-cancel-1",
        ),
    )
    assert cancel.status == "cancelled"
    assert cancel.idempotent_replay is False

    _wait_for(
        lambda: (
            (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child2.status in {"running", "completed", "failed", "cancelled"}
        ),
        timeout_secs=5.0,
    )
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child2 is not None
    assert child2.status != "queued"

    child1_events = (
        tmp_path / "evidence" / "codex" / "agent" / spawn1.child_id / "urm_events.ndjson"
    ).read_text(encoding="utf-8", errors="replace")
    child2_events = (
        tmp_path / "evidence" / "codex" / "agent" / spawn2.child_id / "urm_events.ndjson"
    ).read_text(encoding="utf-8", errors="replace")
    child1_records = [json.loads(line) for line in child1_events.splitlines() if line.strip()]
    child2_records = [json.loads(line) for line in child2_events.splitlines() if line.strip()]
    cancel_events = [event for event in child1_records if event.get("event") == "WORKER_CANCEL"]
    running_events = [
        event
        for event in child2_records
        if event.get("event") == "WORKER_START"
        and isinstance(event.get("detail"), dict)
        and event["detail"].get("status") == "running"
    ]
    assert cancel_events
    cancel_detail = cancel_events[-1].get("detail", {})
    assert isinstance(cancel_detail, dict)
    assert cancel_detail.get("cancel_request_id") == "cancel-child-v2-cancel-1"
    assert running_events
    parent_events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    parent_cancel_events = [
        event
        for event in parent_events
        if event.event_kind == "WORKER_CANCEL"
        and isinstance(event.payload, dict)
        and event.payload.get("worker_id") == spawn1.child_id
    ]
    assert parent_cancel_events
    assert parent_cancel_events[-1].payload.get("cancel_request_id") == "cancel-child-v2-cancel-1"
    if child2_status_before_cancel == "queued":
        cancel_ts = datetime.fromisoformat(str(cancel_events[0]["ts"]))
        running_ts = datetime.fromisoformat(str(running_events[0]["ts"]))
        assert cancel_ts <= running_ts
    _reset_manager_for_tests()


def test_agent_spawn_queue_mode_v2_idempotency_conflict_includes_payload_hashes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-v2-idem-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-v2-idem-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-v2-idem-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    first = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-idem-1",
            prompt="first payload",
            target_turn_id="turn-bootstrap-idem-1",
        )
    )
    replay = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-idem-1",
            prompt="first payload",
            target_turn_id="turn-bootstrap-idem-1",
        )
    )
    assert replay.child_id == first.child_id
    assert replay.queue_seq == first.queue_seq
    assert replay.idempotent_replay is True

    with pytest.raises(HTTPException) as exc_info:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-child-v2-idem-1",
                prompt="different payload",
                target_turn_id="turn-bootstrap-idem-1",
            )
        )
    detail = exc_info.value.detail
    assert exc_info.value.status_code == 409
    assert detail["code"] == "URM_IDEMPOTENCY_KEY_CONFLICT"
    assert detail["context"]["client_request_id"] == "spawn-child-v2-idem-1"
    assert detail["context"]["stored_payload_hash"] != detail["context"]["incoming_payload_hash"]
    _reset_manager_for_tests()


def test_agent_spawn_budget_snapshot_v1_immutable_after_profile_switch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.8")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-b2-immut-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-b2-immut-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-b2-immut-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-b2-immut-1",
            prompt="budget snapshot immutability",
            target_turn_id="turn-b2-immut-1",
        )
    )
    manager = _get_manager()
    child = manager._child_runs.get(spawn.child_id)  # type: ignore[attr-defined]
    assert child is not None
    snapshot_before = dict(child.budget_snapshot)
    assert snapshot_before["budget_version"] == "budget.v1"
    assert snapshot_before["max_solver_calls"] == 40
    assert snapshot_before["max_duration_secs"] <= 300
    assert snapshot_before["max_token_budget"] == 20_000
    assert snapshot_before["token_usage_unobserved"] is True

    selected = urm_policy_profile_select_endpoint(
        PolicyProfileSelectRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="profile-select-b2-immut-1",
            profile_id="safe_mode",
        )
    )
    assert selected.profile_id == "safe_mode"

    child_after = manager._child_runs.get(spawn.child_id)  # type: ignore[attr-defined]
    assert child_after is not None
    assert child_after.budget_snapshot == snapshot_before
    _reset_manager_for_tests()


def test_agent_spawn_budget_breach_solver_calls_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.1")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()
    manager = _get_manager()

    def _tight_budget_snapshot(self: object, *, runtime: object) -> dict[str, object]:
        del self, runtime
        return _budget_snapshot_v1(
            max_solver_calls=1,
            max_duration_secs=300,
            max_token_budget=20_000,
            remaining_parent_duration_secs=300,
            token_usage_unobserved=True,
        )

    monkeypatch.setattr(type(manager), "_child_budget_snapshot", _tight_budget_snapshot)

    failure_signatures: list[tuple[str, int, int, bool]] = []
    for run_idx in range(2):
        start = urm_copilot_start_endpoint(
            CopilotSessionStartRequest(
                provider="codex",
                client_request_id=f"start-b2-budget-{run_idx}",
            )
        )
        session_id = start.session_id
        urm_copilot_send_endpoint(
            CopilotSessionSendRequest(
                provider="codex",
                session_id=session_id,
                client_request_id=f"send-b2-budget-bootstrap-{run_idx}",
                message={
                    "jsonrpc": "2.0",
                    "id": f"req-b2-budget-bootstrap-{run_idx}",
                    "method": "copilot.user_message",
                    "params": {"text": "bootstrap turn"},
                },
            )
        )
        spawn = urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id=f"spawn-b2-budget-{run_idx}",
                prompt="trigger solver-call budget breach",
                target_turn_id=f"turn-b2-budget-{run_idx}",
            )
        )
        assert _wait_for(
            lambda: (
                (child := manager._child_runs.get(spawn.child_id)) is not None
                and child.status in {"completed", "failed", "cancelled"}
                and child.persisted
            ),
            timeout_secs=5.0,
        )
        child = manager._child_runs.get(spawn.child_id)  # type: ignore[attr-defined]
        assert child is not None
        assert child.status == "failed"
        assert child.error_code == "URM_CHILD_BUDGET_EXCEEDED"
        assert child.token_usage_unobserved is True

        child_events_path = (
            tmp_path / "evidence" / "codex" / "agent" / spawn.child_id / "urm_events.ndjson"
        )
        events = [
            json.loads(line)
            for line in child_events_path.read_text(encoding="utf-8", errors="replace").splitlines()
            if line.strip()
        ]
        fail_events = [
            event
            for event in events
            if event.get("event") == "WORKER_FAIL"
            and isinstance(event.get("detail"), dict)
            and event["detail"].get("error_code") == "URM_CHILD_BUDGET_EXCEEDED"
        ]
        assert fail_events
        fail_detail = fail_events[-1]["detail"]
        signature = (
            str(fail_detail.get("budget_dimension")),
            int(fail_detail.get("budget_limit")),
            int(fail_detail.get("budget_observed")),
            bool(fail_detail.get("token_usage_unobserved")),
        )
        failure_signatures.append(signature)
        assert signature == ("solver_calls", 1, 1, True)

        with transaction(db_path=URMRuntimeConfig.from_env().db_path) as con:
            row = get_worker_run(con=con, worker_id=spawn.child_id)
        assert row is not None
        assert row.error_code == "URM_CHILD_BUDGET_EXCEEDED"
        assert isinstance(row.result_json, dict)
        budget_runtime = row.result_json.get("budget_runtime")
        assert isinstance(budget_runtime, dict)
        assert budget_runtime.get("solver_calls_observed") == 1

        urm_copilot_stop_endpoint(CopilotStopRequest(provider="codex", session_id=session_id))

    assert failure_signatures[0] == failure_signatures[1]
    _reset_manager_for_tests()


def test_agent_spawn_budget_invalid_accounting_mode_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.1")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()
    manager = _get_manager()

    def _invalid_budget_snapshot(self: object, *, runtime: object) -> dict[str, object]:
        del self, runtime
        return _budget_snapshot_v1(
            max_solver_calls=40,
            max_duration_secs=300,
            max_token_budget=20_000,
            remaining_parent_duration_secs=300,
            accounting_model="reservation_v0",
            token_usage_unobserved=True,
        )

    monkeypatch.setattr(type(manager), "_child_budget_snapshot", _invalid_budget_snapshot)

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-b2-accounting-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-b2-accounting-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-b2-accounting-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-b2-accounting-1",
            prompt="trigger invalid accounting model",
            target_turn_id="turn-b2-accounting-1",
        )
    )
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.status in {"completed", "failed", "cancelled"}
            and child.persisted
        ),
        timeout_secs=5.0,
    )
    child = manager._child_runs.get(spawn.child_id)  # type: ignore[attr-defined]
    assert child is not None
    assert child.status == "failed"
    assert child.error_code == "URM_DISPATCH_ACCOUNTING_MODE_INVALID"

    events_path = tmp_path / "evidence" / "codex" / "agent" / spawn.child_id / "urm_events.ndjson"
    events = [
        json.loads(line)
        for line in events_path.read_text(encoding="utf-8", errors="replace").splitlines()
        if line.strip()
    ]
    fail_events = [
        event
        for event in events
        if event.get("event") == "WORKER_FAIL"
        and isinstance(event.get("detail"), dict)
        and event["detail"].get("error_code") == "URM_DISPATCH_ACCOUNTING_MODE_INVALID"
    ]
    assert fail_events
    _reset_manager_for_tests()


def test_agent_spawn_budget_running_total_shared_parent_lane_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()
    manager = _get_manager()

    def _shared_budget_snapshot(self: object, *, runtime: object) -> dict[str, object]:
        del self, runtime
        return _budget_snapshot_v1(
            max_solver_calls=2,
            max_duration_secs=300,
            max_token_budget=20_000,
            remaining_parent_duration_secs=300,
            accounting_model="running_total_v1",
            token_usage_unobserved=True,
        )

    monkeypatch.setattr(type(manager), "_child_budget_snapshot", _shared_budget_snapshot)

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-b2-running-total-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-b2-running-total-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-b2-running-total-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn1 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-b2-running-total-1",
            prompt="first child",
            target_turn_id="turn-b2-running-total-1",
        )
    )
    spawn2 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-b2-running-total-2",
            prompt="second child",
            target_turn_id="turn-b2-running-total-1",
        )
    )
    assert _wait_for(
        lambda: (
            (child1 := manager._child_runs.get(spawn1.child_id)) is not None
            and (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child1.status in {"completed", "failed", "cancelled"}
            and child2.status in {"completed", "failed", "cancelled"}
            and child1.persisted
            and child2.persisted
        ),
        timeout_secs=8.0,
        interval_secs=0.05,
    )
    child1 = manager._child_runs.get(spawn1.child_id)  # type: ignore[attr-defined]
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child1 is not None and child2 is not None
    assert any(child.error_code == "URM_CHILD_BUDGET_EXCEEDED" for child in (child1, child2))

    with transaction(db_path=URMRuntimeConfig.from_env().db_path) as con:
        solver_total = get_parent_budget_total(
            con=con,
            parent_session_id=session_id,
            budget_lane="solver_calls",
        )
    assert solver_total is not None
    assert solver_total.max_total == 2
    # With >= enforcement and shared running totals, only the first debit is accepted.
    assert solver_total.current_total == 1
    _reset_manager_for_tests()


def test_manager_marks_stale_running_child_runs_on_startup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "stale-child-run-1"
    parent_session_id = "stale-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-stale-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                **_persisted_child_delegation_payload(),
                "budget_snapshot": {
                    "budget_version": "budget.v1",
                    "max_solver_calls": 10,
                    "max_token_budget": 20_000,
                    "max_duration_secs": 300,
                },
                "inherited_policy_hash": "policy-hash-stale-1",
                "capabilities_allowed": ["urm.agent.spawn"],
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 7,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=7,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    _get_manager()

    with transaction(db_path=config.db_path) as con:
        row = get_worker_run(con=con, worker_id=child_id)
    assert row is not None
    assert row.status == "failed"
    assert row.error_code == "URM_CHILD_TERMINATED_ON_RESTART"

    child_events_payload = events_path.read_text(encoding="utf-8", errors="replace")
    assert "WORKER_FAIL" in child_events_payload
    assert "URM_CHILD_TERMINATED_ON_RESTART" in child_events_payload
    assert '"dispatch_seq":1' in child_events_payload
    assert '"lease_id":"stale-child-run-1"' in child_events_payload

    audit_path = config.evidence_root / "audit" / parent_session_id / "urm_events.ndjson"
    assert audit_path.is_file()
    audit_payload = audit_path.read_text(encoding="utf-8", errors="replace")
    assert "WORKER_FAIL" in audit_payload
    assert "URM_CHILD_TERMINATED_ON_RESTART" in audit_payload
    assert '"dispatch_seq":1' in audit_payload
    _reset_manager_for_tests()


def test_manager_marks_orphaned_dispatch_tokens_on_startup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "stale-child-orphan-1"
    parent_session_id = "stale-parent-orphan-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    # Simulate crash-truncated NDJSON.
    events_path.write_text('{"schema":"urm-events@1"', encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-stale-orphan-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                **_persisted_child_delegation_payload(),
                "budget_snapshot": {
                    "budget_version": "budget.v1",
                    "max_solver_calls": 10,
                    "max_token_budget": 20_000,
                    "max_duration_secs": 300,
                },
                "inherited_policy_hash": "policy-hash-stale-orphan-1",
                "capabilities_allowed": ["urm.agent.spawn"],
                "queue_seq": 1,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=11,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)

    _get_manager()

    with transaction(db_path=config.db_path) as con:
        row = get_worker_run(con=con, worker_id=child_id)
        token = get_dispatch_token_for_child(con=con, child_id=child_id)
    assert row is not None
    assert row.status == "failed"
    assert row.error_code == "URM_SCHEDULER_LEASE_ORPHANED"
    assert token is not None
    assert token.phase == "terminal"

    child_records = [
        json.loads(line)
        for line in events_path.read_text(encoding="utf-8", errors="replace").splitlines()
        if line.strip()
    ]
    fail_events = [
        event
        for event in child_records
        if event.get("event") == "WORKER_FAIL" and isinstance(event.get("detail"), dict)
    ]
    assert fail_events
    fail_detail = fail_events[-1]["detail"]
    assert fail_detail.get("error_code") == "URM_SCHEDULER_LEASE_ORPHANED"
    assert fail_detail.get("reason") == "lease_orphaned"
    assert fail_detail.get("lease_id") == child_id
    assert fail_detail.get("dispatch_seq") == 1
    assert fail_detail.get("parent_stream_id") == f"copilot:{parent_session_id}"
    assert fail_detail.get("parent_seq") == 11

    audit_path = config.evidence_root / "audit" / parent_session_id / "urm_events.ndjson"
    assert audit_path.is_file()
    audit_payload = audit_path.read_text(encoding="utf-8", errors="replace")
    assert "URM_SCHEDULER_LEASE_ORPHANED" in audit_payload
    assert "lease_orphaned" in audit_payload
    _reset_manager_for_tests()


def test_copilot_start_idempotency_conflict_and_replay(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    first = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-idem")
    )
    replay = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-idem")
    )
    assert replay.session_id == first.session_id
    assert replay.idempotent_replay is True

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_start_endpoint(
            CopilotSessionStartRequest(
                provider="codex",
                client_request_id="start-idem",
                cwd="/tmp",
            )
        )
    detail = exc_info.value.detail
    assert exc_info.value.status_code == 409
    assert detail["code"] == "URM_IDEMPOTENCY_KEY_CONFLICT"
    _reset_manager_for_tests()


def test_copilot_start_worker_only_mode_when_app_server_unavailable(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("FAKE_APP_SERVER_DISABLE_READY", "1")
    _reset_manager_for_tests()

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_start_endpoint(
            CopilotSessionStartRequest(provider="codex", client_request_id="start-disabled")
        )
    detail = exc_info.value.detail
    assert exc_info.value.status_code == 400
    assert detail["code"] == "URM_CODEX_APP_SERVER_UNAVAILABLE"
    _reset_manager_for_tests()


def test_copilot_start_accepts_silent_app_server(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("FAKE_APP_SERVER_SILENT_READY", "1")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-silent-ready")
    )
    assert start.status == "running"
    assert start.app_server_unavailable is False
    _reset_manager_for_tests()


def test_copilot_mode_enable_requires_approval_and_consumes_single_use(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="mode-start-1")
    )
    session_id = start.session_id

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_mode_endpoint(
            CopilotModeRequest(
                provider="codex",
                session_id=session_id,
                writes_allowed=True,
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_APPROVAL_REQUIRED"

    issued = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    enabled = urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=issued.approval_id,
        )
    )
    assert enabled.status == "running"

    with pytest.raises(HTTPException) as reuse_exc:
        urm_copilot_mode_endpoint(
            CopilotModeRequest(
                provider="codex",
                session_id=session_id,
                writes_allowed=True,
                approval_id=issued.approval_id,
            )
        )
    assert reuse_exc.value.status_code == 400
    assert reuse_exc.value.detail["code"] == "URM_APPROVAL_INVALID"

    disabled = urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=False,
        )
    )
    assert disabled.status == "running"
    _reset_manager_for_tests()


def test_approval_revoke_is_idempotent(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="revoke-start-1")
    )
    issued = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=start.session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )

    first = urm_approval_revoke_endpoint(
        ApprovalRevokeRequest(provider="codex", approval_id=issued.approval_id)
    )
    second = urm_approval_revoke_endpoint(
        ApprovalRevokeRequest(provider="codex", approval_id=issued.approval_id)
    )

    assert first.revoked is True
    assert first.idempotent_replay is False
    assert second.revoked is True
    assert second.idempotent_replay is True
    _reset_manager_for_tests()


def test_manager_marks_stale_running_sessions_on_startup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    with transaction(db_path=config.db_path) as con:
        persist_copilot_session_start(
            con=con,
            copilot_session_id="stale-session-1",
            role="copilot",
            status="running",
            codex_version="codex-fake",
            capability_probe_id=None,
            pid=1234,
            bin_path=str(codex_bin),
            raw_jsonl_path="evidence/codex/copilot/stale-session-1.jsonl",
            profile_id="default",
            profile_version="profile.v1",
            profile_policy_hash=None,
        )
        update_copilot_session_status(
            con=con,
            copilot_session_id="stale-session-1",
            status="running",
        )

    _get_manager()

    with sqlite3.connect(db_path) as con:
        row = con.execute(
            """
            SELECT status, error_code
            FROM urm_copilot_session
            WHERE copilot_session_id = ?
            """,
            ("stale-session-1",),
        ).fetchone()
    assert row is not None
    assert row[0] == "stopped"
    assert row[1] == "URM_CODEX_SESSION_TERMINATED"
    _reset_manager_for_tests()


def test_tool_call_emits_policy_eval_events_on_allow(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeManager:
        def __init__(self) -> None:
            self.events: list[tuple[str, dict[str, object]]] = []

        def record_policy_eval_event(
            self,
            *,
            session_id: str | None,
            event_kind: str,
            detail: dict[str, object],
        ) -> None:
            self.events.append((event_kind, detail))

    class _FakeRegistry:
        def call_tool(
            self,
            *,
            tool_name: str,
            arguments: dict[str, object],
        ) -> tuple[dict[str, object], str]:
            assert tool_name == "adeu.get_app_state"
            assert arguments == {}
            return ({"ok": True}, "observed")

    fake_manager = _FakeManager()
    monkeypatch.setattr("adeu_api.urm_routes._get_manager", lambda: fake_manager)
    monkeypatch.setattr("adeu_api.urm_routes._get_domain_registry", lambda: _FakeRegistry())
    monkeypatch.setattr(
        "adeu_api.urm_routes._load_session_access_state",
        lambda _sid: (False, False),
    )

    response = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            session_id="session-1",
            tool_name="adeu.get_app_state",
            arguments={},
        )
    )
    assert response.tool_name == "adeu.get_app_state"
    assert response.result == {"ok": True}
    assert response.policy_trace is not None
    assert any(ref.get("kind") == "proof" for ref in response.policy_trace.get("evidence_refs", []))
    assert [event for event, _detail in fake_manager.events] == [
        "POLICY_EVAL_START",
        "PROOF_RUN_PASS",
        "PROOF_RUN_PASS",
        "POLICY_EVAL_PASS",
    ]


def test_tool_call_emits_policy_denied_event_on_instruction_deny(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    class _FakeManager:
        def __init__(self) -> None:
            self.events: list[tuple[str, dict[str, object]]] = []

        def record_policy_eval_event(
            self,
            *,
            session_id: str | None,
            event_kind: str,
            detail: dict[str, object],
        ) -> None:
            self.events.append((event_kind, detail))

    class _FakeRegistry:
        def call_tool(
            self,
            *,
            tool_name: str,
            arguments: dict[str, object],
        ) -> tuple[dict[str, object], str]:
            return ({}, "observed")

    deny_policy_path = tmp_path / "deny.instructions.json"
    deny_policy_path.write_text(
        """
{
  "schema":"odeu.instructions.v1",
  "rules":[
    {
      "rule_id":"deny_copilot",
      "rule_version":1,
      "priority":1,
      "kind":"deny",
      "when":{"atom":"role_is","args":["copilot"]},
      "then":{"effect":"deny_action","params":{}},
      "message":"deny copilot in route test",
      "code":"DENY_COPILOT_ROUTE_TEST"
    }
  ]
}
""".strip(),
        encoding="utf-8",
    )
    fake_manager = _FakeManager()
    monkeypatch.setenv("URM_INSTRUCTION_POLICY_PATH", str(deny_policy_path))
    monkeypatch.setattr("adeu_api.urm_routes._get_manager", lambda: fake_manager)
    monkeypatch.setattr("adeu_api.urm_routes._get_domain_registry", lambda: _FakeRegistry())
    monkeypatch.setattr(
        "adeu_api.urm_routes._load_session_access_state",
        lambda _sid: (False, False),
    )

    with pytest.raises(HTTPException) as exc_info:
        urm_tool_call_endpoint(
            ToolCallRequest(
                provider="codex",
                role="copilot",
                session_id="session-1",
                tool_name="adeu.get_app_state",
                arguments={},
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "DENY_COPILOT_ROUTE_TEST"
    assert any(
        ref.get("kind") == "proof"
        for ref in exc_info.value.detail.get("context", {}).get("evidence_refs", [])
    )
    assert [event for event, _detail in fake_manager.events] == [
        "POLICY_EVAL_START",
        "PROOF_RUN_PASS",
        "PROOF_RUN_PASS",
        "POLICY_DENIED",
    ]


def test_agent_spawn_route_passes_delegation_payload_to_authorize_action(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import adeu_api.urm_routes as urm_routes_module

    class _FakeManager:
        def __init__(self) -> None:
            self.events: list[tuple[str, dict[str, object]]] = []

        def record_policy_eval_event(
            self,
            *,
            session_id: str | None,
            event_kind: str,
            detail: dict[str, object],
        ) -> None:
            self.events.append((event_kind, detail))

        def spawn_child(
            self,
            request: AgentSpawnRequest,
            *,
            inherited_policy_hash: str | None,
            capabilities_allowed: list[str],
        ) -> AgentSpawnResponse:
            assert inherited_policy_hash is not None
            assert "spawn_worker" in capabilities_allowed
            return AgentSpawnResponse(
                child_id="child-policy-spawn-1",
                parent_session_id=request.session_id,
                status="queued",
                parent_stream_id=f"copilot:{request.session_id}",
                child_stream_id="child:child-policy-spawn-1",
                target_turn_id=request.target_turn_id or "turn-policy-spawn-1",
                queue_seq=0,
                profile_id="default",
                profile_version="profile.v1",
                budget_snapshot={},
                inherited_policy_hash=inherited_policy_hash,
                requested_role=request.requested_role,
                granted_role=request.granted_role or request.requested_role,
                delegation_task_kind=request.delegation_task_kind,
                delegated_scope=request.delegated_scope,
                authoritative_write_lease_granted=True,
            )

    fake_manager = _FakeManager()
    authorize_calls: list[dict[str, object]] = []
    original_authorize_action = urm_routes_module.authorize_action

    def _spy_authorize_action(**kwargs: object) -> object:
        authorize_calls.append(dict(kwargs))
        return original_authorize_action(**kwargs)

    monkeypatch.setattr(urm_routes_module, "authorize_action", _spy_authorize_action)
    monkeypatch.setattr("adeu_api.urm_routes._get_manager", lambda: fake_manager)
    monkeypatch.setattr("adeu_api.urm_routes._load_session_access_state", lambda _sid: (True, True))

    response = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id="session-policy-spawn-1",
            client_request_id="client-policy-spawn-1",
            prompt="implement the api lane",
            target_turn_id="turn-policy-spawn-1",
            requested_role="builder_worker",
            delegation_task_kind="write_task",
            delegated_scope=_delegated_scope_payload(
                kind="subtree",
                values=["apps/api"],
                artifact_surfaces=["implementation"],
                rationale="policy trace should include delegation metadata",
            ),
        )
    )

    assert response.child_id == "child-policy-spawn-1"
    assert len(authorize_calls) == 1
    assert authorize_calls[0]["role"] == "copilot"
    assert authorize_calls[0]["action"] == "urm.agent.spawn"
    assert authorize_calls[0]["writes_allowed"] is True
    assert authorize_calls[0]["session_active"] is True
    assert authorize_calls[0]["action_payload"] == {
        "target_turn_id": "turn-policy-spawn-1",
        "use_last_turn": False,
        "prompt": "implement the api lane",
        "requested_role": "builder_worker",
        "granted_role": "builder_worker",
        "delegation_task_kind": "write_task",
        "delegated_scope": {
            "kind": "subtree",
            "values": ["apps/api"],
            "artifact_surfaces": ["implementation"],
            "rationale": "policy trace should include delegation metadata",
        },
    }


def test_materialize_orchestration_state_is_deterministic_for_running_session(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-state-start-1")
    )
    session_id = start.session_id
    manager = _get_manager()
    config = URMRuntimeConfig.from_env()

    first = manager.materialize_orchestration_state(session_id=session_id)
    second = manager.materialize_orchestration_state(session_id=session_id)

    assert first.orchestration_state_snapshot.hash == second.orchestration_state_snapshot.hash
    assert first.execution_topology_state.hash == second.execution_topology_state.hash
    assert first.write_lease_state.hash == second.write_lease_state.hash
    assert first.role_transition_record.hash == second.role_transition_record.hash
    assert first.role_handoff_envelope.hash == second.role_handoff_envelope.hash

    snapshot = _load_materialized_json(
        config=config,
        relative_path=first.orchestration_state_snapshot.path,
    )
    write_lease = _load_materialized_json(
        config=config,
        relative_path=first.write_lease_state.path,
    )
    transitions = _load_materialized_json(
        config=config,
        relative_path=first.role_transition_record.path,
    )
    handoffs = _load_materialized_json(
        config=config,
        relative_path=first.role_handoff_envelope.path,
    )

    assert snapshot["schema"] == "orchestration_state_snapshot@1"
    assert snapshot["orchestrator_session_id"] == session_id
    assert snapshot["worker_session_id"] is None
    assert snapshot["parent_session_id"] == session_id
    assert snapshot["single_writer_default_enforced"] is True
    assert snapshot["last_reconciled_event"] is not None
    assert isinstance(snapshot["event_cursor"], dict)
    assert snapshot["event_cursor"]["streams"]
    assert len(snapshot["current_roles"]) == 1
    assert snapshot["current_roles"][0]["actor_id"] == session_id
    assert snapshot["current_roles"][0]["role"] == "main_orchestrator"
    assert snapshot["current_roles"][0]["user_facing_boundary"] is True
    assert write_lease["active_authoritative_writer_count"] == 0
    assert write_lease["current_authoritative_holder"] is None
    assert transitions["entries"] == []
    assert handoffs["entries"] == []
    _reset_manager_for_tests()


def test_materialize_orchestration_state_tracks_child_dispatch_and_identity(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.4")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-child-start-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="orch-child-send-1",
            message={
                "jsonrpc": "2.0",
                "id": "orch-child-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="orch-child-spawn-1",
            prompt="child orchestration state",
            target_turn_id="1",
        )
    )

    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.dispatch_seq is not None
            and child.child_thread_id is not None
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=session_id)
    snapshot = _load_materialized_json(
        config=config,
        relative_path=artifacts.orchestration_state_snapshot.path,
    )
    topology = _load_materialized_json(
        config=config,
        relative_path=artifacts.execution_topology_state.path,
    )
    write_lease = _load_materialized_json(
        config=config,
        relative_path=artifacts.write_lease_state.path,
    )

    worker_roles = [
        role for role in snapshot["current_roles"] if role["actor_id"] == spawn.child_id
    ]
    assert snapshot["worker_session_id"] is not None
    assert len(worker_roles) == 1
    assert worker_roles[0]["role"] == "explorer"
    assert worker_roles[0]["requested_role"] == "explorer"
    assert worker_roles[0]["granted_role"] == "explorer"
    assert worker_roles[0]["delegation_task_kind"] == "analysis_task"
    assert worker_roles[0]["scope_owned"]["kind"] == "artifact_surface_only"
    assert worker_roles[0]["user_facing_boundary"] is False
    edge = next(edge for edge in topology["edges"] if edge["target_actor_id"] == spawn.child_id)
    assert edge["queue_seq"] == spawn.queue_seq
    assert edge["dispatch_seq"] is not None
    assert edge["requested_role"] == "explorer"
    assert edge["granted_role"] == "explorer"
    assert edge["delegation_task_kind"] == "analysis_task"
    dispatch = next(
        observation
        for observation in write_lease["dispatch_lease_observations"]
        if observation["child_id"] == spawn.child_id
    )
    assert dispatch["lease_id"] == spawn.child_id
    assert dispatch["authoritative_write_access"] is False
    assert dispatch["requested_role"] == "explorer"
    assert dispatch["granted_role"] == "explorer"
    assert dispatch["delegation_task_kind"] == "analysis_task"
    assert dispatch["phase"] in {"queued", "leased", "started", "terminal"}
    _reset_manager_for_tests()


def test_agent_spawn_rejects_write_task_without_builder_role(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="spawn-write-role-start-1")
    )
    session_id = start.session_id
    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-write-role-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "spawn-write-role-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    with pytest.raises(HTTPException) as exc_info:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-write-role-denied-1",
                prompt="attempt support write task",
                target_turn_id="turn-write-role-denied-1",
                requested_role="explorer",
                delegation_task_kind="write_task",
                delegated_scope=_delegated_scope_payload(
                    kind="subtree",
                    values=["apps/api"],
                    artifact_surfaces=["implementation"],
                    rationale="invalid support write attempt",
                ),
            )
    )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_RUNTIME_ENFORCEMENT_INVALID_ROLE_TASK_COMBINATION"
    _reset_manager_for_tests()


def test_agent_spawn_rejects_support_scope_that_implies_proxy_authority(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(
            provider="codex",
            client_request_id="spawn-support-scope-start-1",
        )
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-support-scope-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "spawn-support-scope-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    with pytest.raises(HTTPException) as exc_info:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-support-scope-denied-1",
                prompt="inspect implementation files directly",
                target_turn_id="turn-support-scope-denied-1",
                requested_role="explorer",
                delegated_scope=_delegated_scope_payload(
                    kind="subtree",
                    values=["apps/api"],
                    artifact_surfaces=["implementation"],
                    rationale="invalid support-role proxy authority attempt",
                ),
            )
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_RUNTIME_ENFORCEMENT_SUPPORT_PROXY_AUTHORITY"
    _reset_manager_for_tests()


def test_agent_spawn_rejects_second_active_builder_under_single_builder_default(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "1.0")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(
            provider="codex",
            client_request_id="spawn-builder-limit-start-1",
        )
    )
    session_id = start.session_id
    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-builder-limit-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "spawn-builder-limit-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    first_spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-builder-limit-first-1",
            prompt="implement the api lane",
            target_turn_id="turn-builder-limit-1",
            requested_role="builder_worker",
            delegation_task_kind="write_task",
            delegated_scope=_delegated_scope_payload(
                kind="subtree",
                values=["apps/api"],
                artifact_surfaces=["implementation"],
                rationale="first authoritative builder lease",
            ),
        )
    )

    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(first_spawn.child_id)) is not None
            and child.status == "running"
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    with pytest.raises(HTTPException) as exc_info:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-builder-limit-second-1",
                prompt="attempt second writer",
                target_turn_id="turn-builder-limit-2",
                requested_role="builder_worker",
                delegation_task_kind="write_task",
                delegated_scope=_delegated_scope_payload(
                    kind="subtree",
                    values=["packages/urm_runtime"],
                    artifact_surfaces=["implementation"],
                    rationale="invalid second authoritative builder lease",
                ),
            )
        )

    assert exc_info.value.status_code == 400
    assert (
        exc_info.value.detail["code"]
        == "URM_RUNTIME_ENFORCEMENT_SINGLE_BUILDER_DEFAULT_VIOLATION"
    )
    _reset_manager_for_tests()


def test_materialize_orchestration_state_records_builder_write_lease_and_handoff(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "1.0")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-builder-start-1")
    )
    session_id = start.session_id
    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="orch-builder-send-1",
            message={
                "jsonrpc": "2.0",
                "id": "orch-builder-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="orch-builder-spawn-1",
            prompt="implement the api lane",
            target_turn_id="turn-builder-1",
            requested_role="builder_worker",
            delegation_task_kind="write_task",
            delegated_scope=_delegated_scope_payload(
                kind="subtree",
                values=["apps/api"],
                artifact_surfaces=["implementation"],
                rationale="scoped implementation write task",
            ),
        )
    )
    assert spawn.requested_role == "builder_worker"
    assert spawn.granted_role == "builder_worker"
    assert spawn.delegation_task_kind == "write_task"
    assert spawn.authoritative_write_lease_granted is True
    assert spawn.delegated_scope.kind == "subtree"

    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.status in {"running", "completed"}
            and child.dispatch_seq is not None
            and child.child_thread_id is not None
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    config = URMRuntimeConfig.from_env()
    artifacts_running = manager.materialize_orchestration_state(session_id=session_id)
    snapshot_running = _load_materialized_json(
        config=config,
        relative_path=artifacts_running.orchestration_state_snapshot.path,
    )
    write_lease_running = _load_materialized_json(
        config=config,
        relative_path=artifacts_running.write_lease_state.path,
    )
    transitions_running = _load_materialized_json(
        config=config,
        relative_path=artifacts_running.role_transition_record.path,
    )

    builder_role = next(
        role for role in snapshot_running["current_roles"] if role["actor_id"] == spawn.child_id
    )
    assert snapshot_running["current_authoritative_holder_actor_id"] == spawn.child_id
    assert builder_role["role"] == "builder_worker"
    assert builder_role["requested_role"] == "builder_worker"
    assert builder_role["granted_role"] == "builder_worker"
    assert builder_role["delegation_task_kind"] == "write_task"
    assert builder_role["authority_domain"] == "implementation"
    assert builder_role["authoritative_write_access"] is True
    assert builder_role["scope_owned"]["kind"] == "subtree"
    assert builder_role["scope_owned"]["values"] == ["apps/api"]
    assert write_lease_running["current_authoritative_holder"]["actor_id"] == spawn.child_id
    assert write_lease_running["current_authoritative_holder"]["role"] == "builder_worker"
    assert write_lease_running["current_authoritative_holder"]["requested_role"] == "builder_worker"
    assert (
        write_lease_running["current_authoritative_holder"]["delegation_task_kind"] == "write_task"
    )
    dispatch_running = next(
        observation
        for observation in write_lease_running["dispatch_lease_observations"]
        if observation["child_id"] == spawn.child_id
    )
    assert dispatch_running["authoritative_write_access"] is True
    assert dispatch_running["granted_role"] == "builder_worker"
    assert dispatch_running["scope_owned"]["kind"] == "subtree"
    assert transitions_running["entries"][-1]["to_role"] == "builder_worker"

    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.status == "completed"
            and child.persisted
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    artifacts_completed = manager.materialize_orchestration_state(session_id=session_id)
    write_lease_completed = _load_materialized_json(
        config=config,
        relative_path=artifacts_completed.write_lease_state.path,
    )
    transitions_completed = _load_materialized_json(
        config=config,
        relative_path=artifacts_completed.role_transition_record.path,
    )
    handoff_completed = _load_materialized_json(
        config=config,
        relative_path=artifacts_completed.role_handoff_envelope.path,
    )

    assert write_lease_completed["current_authoritative_holder"]["actor_id"] == session_id
    assert transitions_completed["entries"][-1]["to_role"] == "main_orchestrator"
    builder_handoff = next(
        entry for entry in handoff_completed["entries"] if entry["role"] == "builder_worker"
    )
    assert builder_handoff["artifacts_produced"]
    assert builder_handoff["evidence_refs"]
    assert builder_handoff["recommended_next_action"] == (
        "explicit_orchestrator_reconciliation_required"
    )
    assert builder_handoff["scope_owned"][0]["kind"] == "subtree"

    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "WORKER_RECONCILIATION_REQUIRED"
        and event.payload.get("child_id") == spawn.child_id
        for event in events
    )
    _reset_manager_for_tests()


def test_materialize_orchestration_state_records_write_authority_transition(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-mode-start-1")
    )
    session_id = start.session_id
    manager = _get_manager()
    manager.materialize_orchestration_state(session_id=session_id)

    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )

    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=session_id)
    write_lease = _load_materialized_json(
        config=config,
        relative_path=artifacts.write_lease_state.path,
    )
    transitions = _load_materialized_json(
        config=config,
        relative_path=artifacts.role_transition_record.path,
    )

    assert write_lease["active_authoritative_writer_count"] == 1
    assert write_lease["current_authoritative_holder"]["actor_id"] == session_id
    assert len(transitions["entries"]) == 1
    assert transitions["entries"][0]["authority_level_before"] == (
        "governance_authority_without_write_lease"
    )
    assert transitions["entries"][0]["authority_level_after"] == "governance_authority"
    assert transitions["entries"][0]["granted_by"] == "main_orchestrator"
    _reset_manager_for_tests()


def test_materialize_orchestration_state_records_sequential_builder_transitions(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "1.0")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-builder-seq-start-1")
    )
    session_id = start.session_id
    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="orch-builder-seq-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "orch-builder-seq-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    manager = _get_manager()
    for index, subtree in enumerate(("apps/api", "packages/urm_runtime"), start=1):
        spawn = urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id=f"orch-builder-seq-spawn-{index}",
                prompt=f"implement {subtree}",
                target_turn_id=f"turn-builder-seq-{index}",
                requested_role="builder_worker",
                delegation_task_kind="write_task",
                delegated_scope=_delegated_scope_payload(
                    kind="subtree",
                    values=[subtree],
                    artifact_surfaces=["implementation"],
                    rationale=f"scoped implementation write task {index}",
                ),
            )
        )
        assert spawn.authoritative_write_lease_granted is True
        assert _wait_for(
            lambda: (
                (child := manager._child_runs.get(spawn.child_id)) is not None
                and child.status == "completed"
                and child.persisted
            ),
            timeout_secs=5.0,
            interval_secs=0.05,
        )

    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=session_id)
    transitions = _load_materialized_json(
        config=config,
        relative_path=artifacts.role_transition_record.path,
    )

    assert [entry["to_role"] for entry in transitions["entries"]] == [
        "builder_worker",
        "main_orchestrator",
        "builder_worker",
        "main_orchestrator",
    ]
    assert transitions["entries"][0]["scope_owned"][0]["values"] == ["apps/api"]
    assert transitions["entries"][2]["scope_owned"][0]["values"] == ["packages/urm_runtime"]
    _reset_manager_for_tests()


def test_materialize_orchestration_state_records_audit_bridge_for_restart_recovery(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "orch-recovery-child-1"
    parent_session_id = "orch-recovery-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-orch-recovery-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                **_persisted_child_delegation_payload(),
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 9,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=9,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    manager = _get_manager()
    artifacts = manager.materialize_orchestration_state(session_id=parent_session_id)
    snapshot = _load_materialized_json(
        config=config,
        relative_path=artifacts.orchestration_state_snapshot.path,
    )
    topology = _load_materialized_json(
        config=config,
        relative_path=artifacts.execution_topology_state.path,
    )

    assert snapshot["continuation_bridge_ref"] is not None
    assert snapshot["continuation_bridge_ref"]["target_stream_id"] == (
        f"urm_audit:{parent_session_id}"
    )
    assert any(
        stream["stream_id"] == f"urm_audit:{parent_session_id}"
        for stream in snapshot["event_cursor"]["streams"]
    )
    assert topology["compaction_seams"]
    assert topology["compaction_seams"][0]["target_stream_id"] == (f"urm_audit:{parent_session_id}")
    _reset_manager_for_tests()


def test_materialize_worker_visibility_state_is_deterministic_and_route_visible(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    manager = _get_manager()

    first = manager.materialize_worker_visibility_state(session_id=artifacts.session_id)
    second = manager.materialize_worker_visibility_state(session_id=artifacts.session_id)

    assert first.worker_visibility_state.hash == second.worker_visibility_state.hash

    payload = _load_materialized_json(
        config=config,
        relative_path=first.worker_visibility_state.path,
    )
    assert payload["schema"] == "worker_visibility_state@1"
    assert payload["parent_session_id"] == artifacts.session_id
    assert payload["worker_visibility_foundation_package"] == "packages/urm_runtime"
    assert payload["read_only_visibility_required"] is True
    assert payload["worker_direct_user_boundary_forbidden"] is True
    assert payload["epistemic_lane_enum"] == [
        "raw_transcript",
        "worker_self_report",
        "reconciled_handoff",
        "orchestrator_judgment",
    ]
    assert payload["epistemic_lane_status_enum"] == [
        "available",
        "pending_parse",
        "pending_reconciliation",
        "not_available",
        "parsing_failure",
        "reconciliation_aborted",
    ]
    assert [worker["role"] for worker in payload["workers"]] == [
        "explorer",
        "builder_worker",
    ]
    for worker in payload["workers"]:
        assert [lane["lane"] for lane in worker["epistemic_lanes"]] == [
            "raw_transcript",
            "worker_self_report",
            "reconciled_handoff",
            "orchestrator_judgment",
        ]
        assert worker["raw_transcript_non_authoritative"] is True
        assert worker["worker_self_report_non_authoritative_until_reconciled"] is True
        assert worker["direct_user_boundary_established"] is False
        assert worker["divergence_state"] == "aligned"

    builder_worker = next(
        worker for worker in payload["workers"] if worker["role"] == "builder_worker"
    )
    assert builder_worker["reconciliation_status"] == "pending_reconciliation"
    assert builder_worker["scope_owned"][0]["values"] == ["apps/api"]
    assert builder_worker["scope_remaining"] == []
    assert [lane["status"] for lane in builder_worker["epistemic_lanes"]] == [
        "available",
        "available",
        "pending_reconciliation",
        "not_available",
    ]

    route_payload = urm_copilot_visibility_endpoint(
        session_id=artifacts.session_id,
        provider="codex",
    )
    assert route_payload.parent_session_id == artifacts.session_id
    assert route_payload.model_dump(mode="json", by_alias=True) == payload
    _reset_manager_for_tests()


def test_materialize_worker_visibility_state_marks_running_child_as_raw_only(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "1.0")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="visibility-running-start-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="visibility-running-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "visibility-running-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="visibility-running-spawn-1",
            prompt="inspect the api lane",
            target_turn_id="turn-visibility-running-1",
        )
    )

    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.status == "running"
            and child.child_thread_id is not None
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    config = URMRuntimeConfig.from_env()
    visibility = manager.materialize_worker_visibility_state(session_id=session_id)
    payload = _load_materialized_json(
        config=config,
        relative_path=visibility.worker_visibility_state.path,
    )
    assert len(payload["workers"]) == 1
    worker = payload["workers"][0]
    assert worker["worker_id"] == spawn.child_id
    assert worker["status"] == "running"
    assert worker["divergence_state"] == "raw_only"
    assert worker["scope_owned"][0]["kind"] == "artifact_surface_only"
    assert worker["scope_remaining"] == worker["scope_owned"]
    assert worker["reconciliation_status"] == "not_applicable"
    assert [lane["status"] for lane in worker["epistemic_lanes"]] == [
        "available",
        "pending_parse",
        "not_available",
        "not_available",
    ]
    assert worker["latest_visible_event"] is not None
    assert worker["last_action"] in {"TOOL_CALL_PASS", "WORKER_START"}
    _reset_manager_for_tests()


def test_materialize_worker_visibility_state_preserves_bridge_and_compaction_visibility(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "visibility-recovery-child-1"
    parent_session_id = "visibility-recovery-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-visibility-recovery-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                **_persisted_child_delegation_payload(),
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 9,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=9,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    manager = _get_manager()
    visibility = manager.materialize_worker_visibility_state(session_id=parent_session_id)
    payload = _load_materialized_json(
        config=config,
        relative_path=visibility.worker_visibility_state.path,
    )

    assert payload["continuation_bridge_ref"] is not None
    assert payload["continuation_bridge_ref"]["target_stream_id"] == (
        f"urm_audit:{parent_session_id}"
    )
    assert payload["compaction_seams"]
    assert payload["compaction_seams"][0]["target_stream_id"] == f"urm_audit:{parent_session_id}"
    assert payload["workers"][0]["divergence_state"] == "raw_only"
    _reset_manager_for_tests()


def test_materialize_topology_duty_map_state_is_deterministic_and_route_visible(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, _visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    manager = _get_manager()

    first = manager.materialize_topology_duty_map_state(
        session_id=orchestration_artifacts.session_id
    )
    second = manager.materialize_topology_duty_map_state(
        session_id=orchestration_artifacts.session_id
    )

    assert first.topology_duty_map_state.hash == second.topology_duty_map_state.hash

    payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    assert payload["schema"] == "topology_duty_map_state@1"
    assert payload["orchestrator_session_id"] == orchestration_artifacts.session_id
    assert payload["parent_session_id"] == orchestration_artifacts.session_id
    assert payload["topology_duty_map_foundation_package"] == "packages/urm_runtime"
    assert payload["read_only_topology_required"] is True
    assert payload["topology_surface_authority_policy"] == (
        "derived_from_canonical_execution_state_only_non_authoritative_visualization"
    )
    assert payload["event_stream_drilldown_policy"] == (
        "event_streams_are_provenance_targets_only_not_topology_projection_truth_inputs"
    )
    assert payload["current_authoritative_holder_actor_id"] == orchestration_artifacts.session_id
    assert [node["role"] for node in payload["nodes"]] == [
        "main_orchestrator",
        "explorer",
        "builder_worker",
    ]
    assert payload["nodes"][0]["user_facing_boundary"] is True
    assert all(node["user_facing_boundary"] is False for node in payload["nodes"][1:])

    builder_node = next(node for node in payload["nodes"] if node["role"] == "builder_worker")
    assert builder_node["current_duty"] == "implementation_completed_pending_reconciliation"
    assert builder_node["authoritative_write_access"] is False

    assert payload["edges"]
    for item in [*payload["nodes"], *payload["edges"]]:
        assert item["provenance_refs"]
        assert any(ref["ref_kind"] == "artifact" for ref in item["provenance_refs"])
        for ref in item["provenance_refs"]:
            assert (config.var_root / ref["path"]).exists()

    assert any(
        ref["ref_kind"] == "event_stream"
        for item in [*payload["nodes"], *payload["edges"]]
        for ref in item["provenance_refs"]
    )

    route_payload = urm_copilot_topology_endpoint(
        session_id=orchestration_artifacts.session_id,
        provider="codex",
    )
    assert route_payload.orchestrator_session_id == orchestration_artifacts.session_id
    assert route_payload.model_dump(mode="json", by_alias=True) == payload
    _reset_manager_for_tests()


def test_materialize_topology_duty_map_state_projects_running_builder_write_lease_holder(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, session_id, builder_child_id, topology_artifacts = (
        _materialize_v35d_running_builder_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )

    payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    assert payload["orchestrator_session_id"] == session_id
    assert payload["current_authoritative_holder_actor_id"] == builder_child_id

    builder_node = next(node for node in payload["nodes"] if node["actor_id"] == builder_child_id)
    assert builder_node["role"] == "builder_worker"
    assert builder_node["authoritative_write_access"] is True
    assert builder_node["current_duty"] == "implementing_with_active_write_lease"

    builder_edge = next(
        edge for edge in payload["edges"] if edge["target_actor_id"] == builder_child_id
    )
    assert builder_edge["authoritative_write_access"] is True
    assert builder_edge["blocking_state"] == "non_blocking"
    _reset_manager_for_tests()


def test_build_topology_duty_map_state_renders_support_blocker_as_advisory(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _config, orchestration_artifacts, visibility_artifacts, _topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )

    visibility_payload = json.loads(
        canonical_json(visibility_artifacts.worker_visibility_state.payload)
    )
    support_worker = next(
        worker for worker in visibility_payload["workers"] if worker["role"] == "explorer"
    )
    support_worker["blocking_state"] = "blocking"
    support_worker["blockers"] = ["needs_orchestrator_decision"]
    support_worker["status"] = "failed"

    topology_state = build_topology_duty_map_state(
        execution_topology_state=ExecutionTopologyState.model_validate(
            orchestration_artifacts.execution_topology_state.payload
        ),
        write_lease_state=WriteLeaseState.model_validate(
            orchestration_artifacts.write_lease_state.payload
        ),
        worker_visibility_state=WorkerVisibilityState.model_validate(visibility_payload),
        role_handoff_envelope=RoleHandoffEnvelope.model_validate(
            orchestration_artifacts.role_handoff_envelope.payload
        ),
        source_artifacts=_topology_source_artifacts(
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        ),
    )

    support_node = next(node for node in topology_state.nodes if node.role == "explorer")
    assert support_node.authority_domain == "advisory"
    assert support_node.blocking_state == "non_blocking"
    assert support_node.blockers == ["needs_orchestrator_decision"]
    assert support_node.current_duty == "advisory_issue_raised_for_orchestrator_attention"
    assert support_node.authoritative_write_access is False
    _reset_manager_for_tests()


def test_build_topology_duty_map_state_rejects_invented_visibility_worker(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _config, orchestration_artifacts, visibility_artifacts, _topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )

    visibility_payload = json.loads(
        canonical_json(visibility_artifacts.worker_visibility_state.payload)
    )
    ghost_worker = dict(visibility_payload["workers"][0])
    ghost_worker["worker_id"] = "ghost-worker-1"
    ghost_worker["worker_session_id"] = "ghost-worker-1"
    visibility_payload["workers"].append(ghost_worker)

    with pytest.raises(TopologyDutyMapStateError, match="visibility workers do not match"):
        build_topology_duty_map_state(
            execution_topology_state=ExecutionTopologyState.model_validate(
                orchestration_artifacts.execution_topology_state.payload
            ),
            write_lease_state=WriteLeaseState.model_validate(
                orchestration_artifacts.write_lease_state.payload
            ),
            worker_visibility_state=WorkerVisibilityState.model_validate(visibility_payload),
            role_handoff_envelope=RoleHandoffEnvelope.model_validate(
                orchestration_artifacts.role_handoff_envelope.payload
            ),
            source_artifacts=_topology_source_artifacts(
                orchestration_artifacts=orchestration_artifacts,
                visibility_artifacts=visibility_artifacts,
            ),
        )
    _reset_manager_for_tests()


def test_materialize_topology_duty_map_state_preserves_bridge_and_compaction_visibility(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, _visibility_artifacts = _materialize_v35c_bridge_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )

    manager = _get_manager()
    topology_artifacts = manager.materialize_topology_duty_map_state(
        session_id=orchestration_artifacts.session_id
    )
    payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )

    assert payload["continuation_bridge_ref"] is not None
    assert payload["continuation_bridge_ref"]["target_stream_id"] == (
        f"urm_audit:{orchestration_artifacts.session_id}"
    )
    assert payload["compaction_seams"]
    assert payload["compaction_seams"][0]["target_stream_id"] == (
        f"urm_audit:{orchestration_artifacts.session_id}"
    )
    _reset_manager_for_tests()


def test_v60_runtime_enforcement_preserves_released_builder_support_happy_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    manager = _get_manager()

    visibility_artifacts = manager.materialize_worker_visibility_state(
        session_id=orchestration_artifacts.session_id
    )
    topology_artifacts = manager.materialize_topology_duty_map_state(
        session_id=orchestration_artifacts.session_id
    )

    snapshot_payload = _load_materialized_json(
        config=config,
        relative_path=orchestration_artifacts.orchestration_state_snapshot.path,
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )

    assert any(role["role"] == "builder_worker" for role in snapshot_payload["current_roles"])
    assert any(worker["role"] == "explorer" for worker in visibility_payload["workers"])
    assert any(node["role"] == "builder_worker" for node in topology_payload["nodes"])
    _reset_manager_for_tests()


def test_materialize_orchestration_state_rejects_invalid_persisted_scope_kind_under_v60_enforcement(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "v60-orch-scope-child-1"
    parent_session_id = "v60-orch-scope-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-v60-orch-scope-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                "requested_role": "explorer",
                "granted_role": "explorer",
                "delegation_task_kind": "analysis_task",
                "delegated_scope": _delegated_scope_payload(
                    kind="invalid_scope_kind",
                    values=["apps/api"],
                    artifact_surfaces=["none"],
                    rationale="invalid persisted scope kind",
                ),
                "authoritative_write_lease_granted": False,
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 9,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=9,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    manager = _get_manager()
    with pytest.raises(URMError) as exc_info:
        manager.materialize_orchestration_state(session_id=parent_session_id)

    assert exc_info.value.detail.code == "URM_RUNTIME_ENFORCEMENT_SCOPE_KIND_INVALID"
    assert (
        exc_info.value.detail.context["boundary"]
        == "orchestration_state_materialization_boundary"
    )
    _reset_manager_for_tests()


def test_materialize_worker_visibility_state_rejects_persisted_support_proxy_authority(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "v60-visibility-support-child-1"
    parent_session_id = "v60-visibility-support-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-v60-visibility-support-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                **_persisted_child_delegation_payload(
                    delegated_scope=_delegated_scope_payload(
                        kind="subtree",
                        values=["apps/api"],
                        artifact_surfaces=["implementation"],
                        rationale="invalid persisted support proxy authority",
                    )
                ),
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 9,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=9,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    manager = _get_manager()
    with pytest.raises(URMError) as exc_info:
        manager.materialize_worker_visibility_state(session_id=parent_session_id)

    assert exc_info.value.detail.code == "URM_RUNTIME_ENFORCEMENT_SUPPORT_PROXY_AUTHORITY"
    assert (
        exc_info.value.detail.context["boundary"]
        == "worker_visibility_materialization_boundary"
    )
    _reset_manager_for_tests()


def test_materialize_topology_duty_map_state_rejects_missing_claimed_work_handoff_inputs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "v60-topology-handoff-child-1"
    parent_session_id = "v60-topology-handoff-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="completed",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-v60-topology-handoff-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                "requested_role": "explorer",
                "granted_role": "explorer",
                "delegated_scope": _delegated_scope_payload(
                    kind="artifact_surface_only",
                    artifact_surfaces=["none"],
                    rationale="completed support worker with claimed outputs",
                ),
                "authoritative_write_lease_granted": False,
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "terminal",
                "parent_seq": 9,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=9,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="terminal")

    manager = _get_manager()
    with pytest.raises(URMError) as exc_info:
        manager.materialize_topology_duty_map_state(session_id=parent_session_id)

    assert exc_info.value.detail.code == "URM_RUNTIME_ENFORCEMENT_CLAIMED_WORK_HANDOFF_INVALID"
    assert (
        exc_info.value.detail.context["boundary"]
        == "topology_duty_map_materialization_boundary"
    )
    _reset_manager_for_tests()


def test_materialize_v35a_orchestration_state_evidence_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-evidence-start-1")
    )
    manager = _get_manager()
    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=start.session_id)

    first = _materialize_v35a_evidence(
        repo_root=tmp_path,
        config=config,
        artifacts=artifacts,
    )
    second = _materialize_v35a_evidence(
        repo_root=tmp_path,
        config=config,
        artifacts=artifacts,
    )

    assert first["artifact"].hash == second["artifact"].hash
    payload = first["payload"]
    assert payload["schema"] == "v35a_orchestration_state_evidence@1"
    assert payload["single_writer_default_enforced"] is True
    assert payload["worker_direct_user_boundary_forbidden"] is True
    assert payload["canonical_identity_fields_recorded"] is True
    assert payload["last_reconciled_event_recorded"] is True
    assert payload["continuation_bridge_ref_recorded"] is False
    assert payload["zero_occurrence_empty_artifacts_materialized"] is True
    assert payload["scope_granularity_enum_frozen"] is True
    assert payload["handoff_reconciliation_required"] is True
    assert payload["verification_passed"] is True
    assert payload["metric_key_cardinality"] == 80
    assert payload["metric_key_exact_set_equal_v55"] is True
    _reset_manager_for_tests()


def test_materialize_v35a_orchestration_state_evidence_records_bridge_when_present(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "orch-evidence-bridge-child-1"
    parent_session_id = "orch-evidence-bridge-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-orch-evidence-bridge-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                **_persisted_child_delegation_payload(),
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 9,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=9,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    manager = _get_manager()
    artifacts = manager.materialize_orchestration_state(session_id=parent_session_id)
    evidence = _materialize_v35a_evidence(
        repo_root=tmp_path,
        config=config,
        artifacts=artifacts,
    )

    assert evidence["payload"]["continuation_bridge_ref_recorded"] is True
    _reset_manager_for_tests()


def test_materialize_v35a_orchestration_state_evidence_fails_closed_on_missing_artifact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-evidence-missing-1")
    )
    manager = _get_manager()
    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=start.session_id)
    (config.var_root / artifacts.role_handoff_envelope.path).unlink()

    with pytest.raises(OrchestrationEvidenceError, match="not found"):
        _materialize_v35a_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35a_orchestration_state_evidence_fails_closed_on_malformed_handoff(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-evidence-handoff-1")
    )
    manager = _get_manager()
    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=start.session_id)
    handoff_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.role_handoff_envelope.path,
    )
    handoff_payload["entries"] = [
        {
            "role": "support_worker",
            "authority_level": "advisory_information_only",
            "authority_domain": "advisory",
            "artifact_class": "advisory",
            "artifact_surface": "none",
            "repo_root": "/tmp/repo",
            "branch_or_head": "HEAD",
            "scope_owned": [],
            "scope_remaining": [],
            "files_changed": [],
            "commands_run": [],
            "artifacts_produced": [],
            "evidence_refs": [],
            "status": "completed",
            "blocking_state": "non_blocking",
            "blockers": [],
            "open_risks": [],
            "escalation_reason": None,
        }
    ]
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="role_handoff_envelope",
        payload=handoff_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError, match="role_handoff_envelope payload is invalid"
    ):
        _materialize_v35a_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35a_evidence_fails_without_transition_on_authority_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-evidence-transition-1")
    )
    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=start.session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=start.session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )

    manager = _get_manager()
    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=start.session_id)
    transition_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.role_transition_record.path,
    )
    transition_payload["entries"] = []
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="role_transition_record",
        payload=transition_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="role transition record is required"):
        _materialize_v35a_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35a_orchestration_state_evidence_fails_closed_without_compaction_linkage(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "orch-evidence-linkage-child-1"
    parent_session_id = "orch-evidence-linkage-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-orch-evidence-linkage-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                **_persisted_child_delegation_payload(),
                "queue_seq": 1,
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 9,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=9,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    manager = _get_manager()
    artifacts = manager.materialize_orchestration_state(session_id=parent_session_id)
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.execution_topology_state.path,
    )
    topology_payload["compaction_seams"] = []
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="execution_topology_state",
        payload=topology_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="exactly one compaction seam"):
        _materialize_v35a_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35a_orchestration_state_evidence_fails_closed_on_multiple_writer_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-evidence-writers-1")
    )
    approval = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=start.session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=start.session_id,
            writes_allowed=True,
            approval_id=approval.approval_id,
        )
    )

    manager = _get_manager()
    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=start.session_id)
    write_lease_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.write_lease_state.path,
    )
    write_lease_payload["single_writer_default_enforced"] = False
    write_lease_payload["active_authoritative_writer_count"] = 2
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="write_lease_state",
        payload=write_lease_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="single-writer default must be enforced"):
        _materialize_v35a_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35a_orchestration_state_evidence_fails_closed_on_worker_user_boundary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.4")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="orch-evidence-boundary-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="orch-evidence-boundary-send-1",
            message={
                "jsonrpc": "2.0",
                "id": "orch-evidence-boundary-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="orch-evidence-boundary-spawn-1",
            prompt="child orchestration evidence",
            target_turn_id="1",
        )
    )

    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.dispatch_seq is not None
            and child.child_thread_id is not None
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )

    config = URMRuntimeConfig.from_env()
    artifacts = manager.materialize_orchestration_state(session_id=session_id)
    snapshot_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.orchestration_state_snapshot.path,
    )
    child_role = next(
        role for role in snapshot_payload["current_roles"] if role["actor_id"] == spawn.child_id
    )
    child_role["user_facing_boundary"] = True
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="orchestration_state_snapshot",
        payload=snapshot_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="direct user boundary"):
        _materialize_v35a_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )

    first = _materialize_v35b_evidence(
        repo_root=tmp_path,
        config=config,
        artifacts=artifacts,
    )
    second = _materialize_v35b_evidence(
        repo_root=tmp_path,
        config=config,
        artifacts=artifacts,
    )

    assert first["artifact"].hash == second["artifact"].hash
    payload = first["payload"]
    assert payload["schema"] == "v35b_delegation_handoff_evidence@1"
    assert payload["builder_role_materialized"] is True
    assert payload["support_roles_materialized"] is True
    assert payload["delegated_scope_kind_recorded"] is True
    assert payload["single_builder_default_enforced"] is True
    assert payload["support_workers_non_authoritative"] is True
    assert payload["handoff_artifact_materialized"] is True
    assert payload["handoff_reconciliation_required"] is True
    assert payload["unreconciled_worker_output_non_authoritative"] is True
    assert payload["worker_direct_user_boundary_forbidden"] is True
    assert payload["verification_passed"] is True
    assert payload["metric_key_cardinality"] == 80
    assert payload["metric_key_exact_set_equal_v56"] is True
    assert payload["zero_occurrence_empty_artifacts_materialized"] is True
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_fails_closed_on_missing_requested_role(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    snapshot_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.orchestration_state_snapshot.path,
    )
    builder_role = next(
        role for role in snapshot_payload["current_roles"] if role["role"] == "builder_worker"
    )
    builder_role["requested_role"] = None
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="orchestration_state_snapshot",
        payload=snapshot_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="requested_role must be recorded"):
        _materialize_v35b_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_fails_closed_without_builder_write_lease(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    write_lease_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.write_lease_state.path,
    )
    builder_observation = next(
        observation
        for observation in write_lease_payload["dispatch_lease_observations"]
        if observation["granted_role"] == "builder_worker"
    )
    builder_observation["authoritative_write_access"] = False
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="write_lease_state",
        payload=write_lease_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="authoritative write lease"):
        _materialize_v35b_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_fails_closed_on_missing_handoff_entry(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    handoff_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.role_handoff_envelope.path,
    )
    handoff_payload["entries"] = [
        entry for entry in handoff_payload["entries"] if entry["role"] != "builder_worker"
    ]
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="role_handoff_envelope",
        payload=handoff_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError, match="completed child handoff entry is required"
    ):
        _materialize_v35b_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_fails_closed_on_extra_handoff_entry(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    handoff_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.role_handoff_envelope.path,
    )
    extra_entry = dict(handoff_payload["entries"][0])
    extra_entry["role"] = "docs_helper"
    handoff_payload["entries"].append(extra_entry)
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="role_handoff_envelope",
        payload=handoff_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="handoff entries must exactly match completed delegated work",
    ):
        _materialize_v35b_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_fails_closed_on_support_authority_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    snapshot_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.orchestration_state_snapshot.path,
    )
    support_role = next(
        role for role in snapshot_payload["current_roles"] if role["role"] == "explorer"
    )
    support_role["authority_domain"] = "implementation"
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="orchestration_state_snapshot",
        payload=snapshot_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="support-worker authority"):
        _materialize_v35b_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_fails_closed_on_unreconciled_truth_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    handoff_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.role_handoff_envelope.path,
    )
    handoff_payload["trust_model"] = "accepted_without_reconciliation"
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="role_handoff_envelope",
        payload=handoff_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="handoff trust model drift detected"):
        _materialize_v35b_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_fails_closed_on_multiple_builder_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    write_lease_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.write_lease_state.path,
    )
    write_lease_payload["active_authoritative_writer_count"] = 2
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="write_lease_state",
        payload=write_lease_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError, match="multiple authoritative builders active by default"
    ):
        _materialize_v35b_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35b_delegation_handoff_evidence_fails_closed_on_worker_user_boundary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, artifacts = _materialize_v35b_builder_support_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    snapshot_payload = _load_materialized_json(
        config=config,
        relative_path=artifacts.orchestration_state_snapshot.path,
    )
    support_role = next(
        role for role in snapshot_payload["current_roles"] if role["role"] == "explorer"
    )
    support_role["user_facing_boundary"] = True
    artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=artifacts,
        field_name="orchestration_state_snapshot",
        payload=snapshot_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="direct user boundary"):
        _materialize_v35b_evidence(
            repo_root=tmp_path,
            config=config,
            artifacts=artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )

    first = _materialize_v35c_evidence(
        repo_root=tmp_path,
        config=config,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
    )
    second = _materialize_v35c_evidence(
        repo_root=tmp_path,
        config=config,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
    )

    assert first["artifact"].hash == second["artifact"].hash
    payload = first["payload"]
    assert payload["schema"] == "v35c_transcript_visibility_evidence@1"
    assert payload["read_only_visibility_preserved"] is True
    assert payload["epistemic_lane_labels_present"] is True
    assert payload["explicit_lane_absence_materialized"] is True
    assert payload["explicit_divergence_state_materialized"] is True
    assert payload["continuation_bridge_visibility_present_when_available"] is False
    assert payload["no_ad_hoc_progress_summary_bypass"] is True
    assert payload["raw_transcript_non_authoritative"] is True
    assert payload["worker_self_report_non_authoritative_until_reconciled"] is True
    assert payload["worker_direct_user_boundary_forbidden"] is True
    assert payload["verification_passed"] is True
    assert payload["metric_key_cardinality"] == 80
    assert payload["metric_key_exact_set_equal_v57"] is True
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_records_bridge_when_present(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = _materialize_v35c_bridge_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )

    evidence = _materialize_v35c_evidence(
        repo_root=tmp_path,
        config=config,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
    )

    assert evidence["payload"]["continuation_bridge_visibility_present_when_available"] is True
    _reset_manager_for_tests()


def test_materialize_v35c_visibility_evidence_fails_closed_on_missing_visibility_artifact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    (config.var_root / visibility_artifacts.worker_visibility_state.path).unlink()

    with pytest.raises(OrchestrationEvidenceError, match="worker_visibility_state.json"):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_fails_closed_on_missing_lane_label(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    visibility_payload["epistemic_lane_enum"][0] = "worker_self_report"
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError, match="epistemic lane labels must remain frozen"
    ):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_fails_closed_on_omitted_absent_lane(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    visibility_payload["workers"][0]["epistemic_lanes"] = [
        lane
        for lane in visibility_payload["workers"][0]["epistemic_lanes"]
        if lane["lane"] != "orchestrator_judgment"
    ]
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError, match="lane absence may not be silently omitted"
    ):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_fails_closed_on_missing_divergence_state(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = _materialize_v35c_running_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    visibility_payload["workers"][0]["divergence_state"] = "aligned"
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="divergence state must be explicit when lanes do not align",
    ):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_fails_closed_on_flattened_continuity(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = _materialize_v35c_bridge_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    visibility_payload["compaction_seams"] = []
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="compaction or continuation bridge continuity silently flattened",
    ):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_fails_closed_on_progress_bypass(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    builder_worker = next(
        worker for worker in visibility_payload["workers"] if worker["role"] == "builder_worker"
    )
    builder_worker["requested_role"] = "docs_helper"
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="progress fields must be derived from canonical state and child role",
    ):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_fails_closed_on_raw_authority_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    visibility_payload["workers"][0]["raw_transcript_non_authoritative"] = False
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="raw transcript rendered as authoritative",
    ):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_visibility_evidence_fails_closed_on_self_report_authority_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    builder_worker = next(
        worker for worker in visibility_payload["workers"] if worker["role"] == "builder_worker"
    )
    builder_worker["worker_self_report_non_authoritative_until_reconciled"] = False
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="worker self-report rendered as reconciled without explicit reconciliation",
    ):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35c_transcript_visibility_evidence_fails_closed_on_worker_user_boundary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = (
        _materialize_v35c_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    visibility_payload["workers"][0]["direct_user_boundary_established"] = True
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(OrchestrationEvidenceError, match="worker direct user boundary established"):
        _materialize_v35c_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )

    first = _materialize_v35d_evidence(
        repo_root=tmp_path,
        config=config,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
        topology_artifacts=topology_artifacts,
    )
    second = _materialize_v35d_evidence(
        repo_root=tmp_path,
        config=config,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
        topology_artifacts=topology_artifacts,
    )

    assert first["artifact"].hash == second["artifact"].hash
    payload = first["payload"]
    assert payload["schema"] == "v35d_topology_duty_map_evidence@1"
    assert payload["derived_from_canonical_execution_state_only"] is True
    assert payload["current_write_lease_holder_projected"] is True
    assert payload["current_duty_not_authority_inflating"] is True
    assert payload["provenance_markers_materialized"] is True
    assert payload["artifact_and_event_stream_provenance_refs_resolve"] is True
    assert payload["advisory_blockers_not_rendered_as_governance_blockers"] is True
    assert payload["continuation_bridge_and_compaction_visibility_preserved"] is True
    assert payload["non_authoritative_topology_surface_preserved"] is True
    assert payload["verification_passed"] is True
    assert payload["metric_key_cardinality"] == 80
    assert payload["metric_key_exact_set_equal_v58"] is True
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_records_bridge_when_present(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = _materialize_v35c_bridge_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    manager = _get_manager()
    topology_artifacts = manager.materialize_topology_duty_map_state(
        session_id=orchestration_artifacts.session_id
    )

    evidence = _materialize_v35d_evidence(
        repo_root=tmp_path,
        config=config,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
        topology_artifacts=topology_artifacts,
    )

    assert evidence["payload"]["continuation_bridge_and_compaction_visibility_preserved"] is True
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_fails_closed_on_missing_topology_artifact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    (config.var_root / topology_artifacts.topology_duty_map_state.path).unlink()

    with pytest.raises(OrchestrationEvidenceError, match="topology_duty_map_state.json"):
        _materialize_v35d_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_fails_closed_on_invented_topology_state(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    builder_node = next(
        node for node in topology_payload["nodes"] if node["role"] == "builder_worker"
    )
    builder_node["scope_owned"]["values"] = ["apps/api", "ghost-scope"]
    topology_artifacts = _rewrite_topology_artifact(
        config=config,
        artifacts=topology_artifacts,
        payload=topology_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="topology view invents state not present in canonical artifacts",
    ):
        _materialize_v35d_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_fails_closed_on_incorrect_write_holder(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, session_id, builder_child_id, topology_artifacts = (
        _materialize_v35d_running_builder_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    manager = _get_manager()
    orchestration_artifacts = manager.materialize_orchestration_state(session_id=session_id)
    visibility_artifacts = manager.materialize_worker_visibility_state(session_id=session_id)
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    assert topology_payload["current_authoritative_holder_actor_id"] == builder_child_id
    topology_payload["current_authoritative_holder_actor_id"] = session_id
    topology_artifacts = _rewrite_topology_artifact(
        config=config,
        artifacts=topology_artifacts,
        payload=topology_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="current write lease holder rendered incorrectly",
    ):
        _materialize_v35d_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_fails_closed_on_current_duty_inflation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    builder_node = next(
        node for node in topology_payload["nodes"] if node["role"] == "builder_worker"
    )
    builder_node["current_duty"] = "implementation_write_lease_holder_pending_reconciliation"
    topology_artifacts = _rewrite_topology_artifact(
        config=config,
        artifacts=topology_artifacts,
        payload=topology_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="current_duty rendered as authority surface",
    ):
        _materialize_v35d_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_fails_closed_on_unresolved_provenance_ref(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    topology_payload["nodes"][0]["provenance_refs"][0]["path"] = "evidence/codex/missing.json"
    topology_artifacts = _rewrite_topology_artifact(
        config=config,
        artifacts=topology_artifacts,
        payload=topology_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="provenance ref missing or unresolvable",
    ):
        _materialize_v35d_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_fails_closed_on_advisory_blocker_inflation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    support_node = next(
        node for node in topology_payload["nodes"] if node["role"] == "explorer"
    )
    support_edge = next(
        edge
        for edge in topology_payload["edges"]
        if edge["target_actor_id"] == support_node["actor_id"]
    )
    support_node["blocking_state"] = "blocking"
    support_edge["blocking_state"] = "blocking"
    topology_artifacts = _rewrite_topology_artifact(
        config=config,
        artifacts=topology_artifacts,
        payload=topology_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="advisory blocker rendered as governance equivalent",
    ):
        _materialize_v35d_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_fails_closed_on_flattened_continuity(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts = _materialize_v35c_bridge_artifacts(
        tmp_path=tmp_path,
        monkeypatch=monkeypatch,
    )
    manager = _get_manager()
    topology_artifacts = manager.materialize_topology_duty_map_state(
        session_id=orchestration_artifacts.session_id
    )
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    topology_payload["compaction_seams"] = []
    topology_artifacts = _rewrite_topology_artifact(
        config=config,
        artifacts=topology_artifacts,
        payload=topology_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="compaction or continuation bridge visibility silently flattened",
    ):
        _materialize_v35d_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35d_topology_duty_map_evidence_fails_closed_on_authoritative_surface_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    topology_payload = _load_materialized_json(
        config=config,
        relative_path=topology_artifacts.topology_duty_map_state.path,
    )
    topology_payload["read_only_topology_required"] = False
    topology_artifacts = _rewrite_topology_artifact(
        config=config,
        artifacts=topology_artifacts,
        payload=topology_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="topology surface treated as authoritative",
    ):
        _materialize_v35d_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35e_runtime_enforcement_evidence_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )

    first = _materialize_v35e_evidence(
        repo_root=tmp_path,
        config=config,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
        topology_artifacts=topology_artifacts,
    )
    second = _materialize_v35e_evidence(
        repo_root=tmp_path,
        config=config,
        orchestration_artifacts=orchestration_artifacts,
        visibility_artifacts=visibility_artifacts,
        topology_artifacts=topology_artifacts,
    )

    assert first["artifact"].hash == second["artifact"].hash
    payload = first["payload"]
    assert payload["schema"] == "v35e_runtime_enforcement_evidence@1"
    assert payload["required_enforcement_surfaces_active"] is True
    assert payload["single_builder_default_enforced_at_runtime"] is True
    assert payload["support_role_proxy_authority_blocked"] is True
    assert payload["claimed_work_handoff_validation_enforced"] is True
    assert payload["scope_kind_validation_enforced"] is True
    assert payload["deterministic_denial_surfaces_recorded"] is True
    assert payload["released_happy_path_preserved_under_runtime_enforcement"] is True
    assert payload["observability_surfaces_remain_read_only"] is True
    assert payload["acceptance_and_closeout_authority_preserved"] is True
    assert payload["worker_direct_user_boundary_forbidden"] is True
    assert payload["verification_passed"] is True
    assert payload["metric_key_cardinality"] == 80
    assert payload["metric_key_exact_set_equal_v59"] is True
    _reset_manager_for_tests()


def test_materialize_v35e_runtime_enforcement_evidence_fails_closed_on_missing_surface(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    monkeypatch.setattr(
        orchestration_evidence_module,
        "REQUIRED_ENFORCEMENT_SURFACES",
        ("spawn_request_boundary",),
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="required runtime enforcement surfaces drift detected",
    ):
        _materialize_v35e_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35e_runtime_enforcement_evidence_fails_closed_on_single_builder_bypass(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )

    monkeypatch.setattr(
        orchestration_evidence_module,
        "validate_single_builder_default",
        lambda *, boundary, candidates: None,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="single-builder default violation accepted",
    ):
        _materialize_v35e_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35e_runtime_enforcement_evidence_fails_closed_on_support_proxy_bypass(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    original = orchestration_evidence_module.validate_runtime_enforcement_candidate

    def _allow_support_proxy(
        *,
        boundary: str,
        candidate: object,
        parent_writes_allowed: bool | None,
    ):
        subject_id = getattr(candidate, "subject_id", None)
        if subject_id == "support-proxy-child":
            return None
        return original(
            boundary=boundary,
            candidate=candidate,
            parent_writes_allowed=parent_writes_allowed,
        )

    monkeypatch.setattr(
        orchestration_evidence_module,
        "validate_runtime_enforcement_candidate",
        _allow_support_proxy,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="support-role proxy authority violation accepted",
    ):
        _materialize_v35e_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35e_runtime_enforcement_evidence_fails_closed_on_claimed_work_bypass(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )

    monkeypatch.setattr(
        orchestration_evidence_module,
        "validate_claimed_work_handoff_field",
        lambda *, boundary, subject_id, field_name, value, claimed_work_present, context: (
            str(value) if isinstance(value, str) else field_name
        ),
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="claimed-work handoff missing required fields accepted",
    ):
        _materialize_v35e_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35e_runtime_enforcement_evidence_fails_closed_on_scope_bypass(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    original = orchestration_evidence_module.validate_runtime_enforcement_candidate

    def _allow_invalid_scope(
        *,
        boundary: str,
        candidate: object,
        parent_writes_allowed: bool | None,
    ):
        subject_id = getattr(candidate, "subject_id", None)
        if subject_id == "invalid-scope-kind-child":
            return None
        return original(
            boundary=boundary,
            candidate=candidate,
            parent_writes_allowed=parent_writes_allowed,
        )

    monkeypatch.setattr(
        orchestration_evidence_module,
        "validate_runtime_enforcement_candidate",
        _allow_invalid_scope,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="scope kind missing or malformed accepted",
    ):
        _materialize_v35e_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35e_runtime_enforcement_evidence_fails_closed_on_authority_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    handoff_payload = _load_materialized_json(
        config=config,
        relative_path=orchestration_artifacts.role_handoff_envelope.path,
    )
    handoff_payload["entries"][0]["artifact_class"] = "authoritative"
    orchestration_artifacts = _rewrite_orchestration_artifact(
        config=config,
        artifacts=orchestration_artifacts,
        field_name="role_handoff_envelope",
        payload=handoff_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="worker output may not become authoritative pre-closeout",
    ):
        _materialize_v35e_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_v35e_runtime_enforcement_evidence_fails_closed_on_worker_user_boundary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config, orchestration_artifacts, visibility_artifacts, topology_artifacts = (
        _materialize_v35d_builder_support_artifacts(
            tmp_path=tmp_path,
            monkeypatch=monkeypatch,
        )
    )
    visibility_payload = _load_materialized_json(
        config=config,
        relative_path=visibility_artifacts.worker_visibility_state.path,
    )
    visibility_payload["workers"][0]["direct_user_boundary_established"] = True
    visibility_artifacts = _rewrite_visibility_artifact(
        config=config,
        artifacts=visibility_artifacts,
        payload=visibility_payload,
    )

    with pytest.raises(
        OrchestrationEvidenceError,
        match="worker direct user boundary established",
    ):
        _materialize_v35e_evidence(
            repo_root=tmp_path,
            config=config,
            orchestration_artifacts=orchestration_artifacts,
            visibility_artifacts=visibility_artifacts,
            topology_artifacts=topology_artifacts,
        )
    _reset_manager_for_tests()


def test_materialize_orchestration_state_rejects_invalid_session_id_path_component(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    manager = _get_manager()
    with pytest.raises(URMError) as exc_info:
        manager.materialize_orchestration_state(session_id="../escape")

    assert exc_info.value.detail.code == "URM_ORCHESTRATION_STATE_INVALID"
    _reset_manager_for_tests()


def test_materialize_topology_duty_map_state_rejects_invalid_session_id_path_component(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    manager = _get_manager()
    with pytest.raises(URMError) as exc_info:
        manager.materialize_topology_duty_map_state(session_id="../escape")

    assert exc_info.value.detail.code == "URM_TOPOLOGY_DUTY_MAP_STATE_INVALID"
    _reset_manager_for_tests()


def test_role_handoff_entry_rejects_missing_required_fields() -> None:
    with pytest.raises(ValidationError):
        RoleHandoffEntry.model_validate(
            {
                "role": "builder",
                "authority_level": "implementation_authority_scoped",
                "authority_domain": "implementation",
                "artifact_class": "authoritative",
                "artifact_surface": "implementation",
                "repo_root": "/tmp/repo",
                "branch_or_head": "HEAD",
                "scope_owned": [],
                "scope_remaining": [],
                "files_changed": [],
                "commands_run": [],
                "artifacts_produced": [],
                "evidence_refs": [],
                "status": "completed",
                "blocking_state": "non_blocking",
                "blockers": [],
                "open_risks": [],
                "escalation_reason": None,
            }
        )
