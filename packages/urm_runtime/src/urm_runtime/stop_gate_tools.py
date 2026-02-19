from __future__ import annotations

import argparse
import json
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any

from adeu_kernel import strip_nonsemantic_proof_fields, strip_nonsemantic_validator_fields
from adeu_semantic_depth import SemanticDepthError, validate_semantic_depth_report
from pydantic import ValidationError

from .events_tools import replay_events, validate_events
from .hashing import canonical_json, sha256_canonical_json
from .models import NormalizedEvent

STOP_GATE_SCHEMA = "stop_gate_metrics@1"
POLICY_INCIDENT_SCHEMA = "incident_packet@1"
CONNECTOR_SNAPSHOT_SCHEMA = "connector_snapshot@1"
VALIDATOR_EVIDENCE_PACKET_SCHEMA = "validator_evidence_packet@1"
SEMANTICS_DIAGNOSTICS_SCHEMA = "semantics_diagnostics@1"
POLICY_LINEAGE_SCHEMA = "policy_lineage@1"
PROOF_EVIDENCE_SCHEMA = "proof_evidence@1"
EXPLAIN_DIFF_SCHEMA = "explain_diff@1"
DOMAIN_CONFORMANCE_SCHEMA = "domain_conformance@1"
QUALITY_DASHBOARD_SCHEMA = "quality.dashboard.v1"
SEMANTICS_DETERMINISM_REPLAY_COUNT = 3
VNEXT_PLUS7_REPLAY_COUNT = 3
VNEXT_PLUS7_MANIFEST_SCHEMA = "stop_gate.vnext_plus7_manifest@1"
VNEXT_PLUS7_DEFAULT_METRICS = {
    "policy_lint_determinism_pct": 0.0,
    "proof_replay_determinism_pct": 0.0,
    "policy_proof_packet_hash_stability_pct": 0.0,
}
VNEXT_PLUS8_REPLAY_COUNT = 3
VNEXT_PLUS8_MANIFEST_SCHEMA = "stop_gate.vnext_plus8_manifest@1"
VNEXT_PLUS8_DEFAULT_METRICS = {
    "explain_diff_determinism_pct": 0.0,
    "explain_api_cli_parity_pct": 0.0,
    "explain_hash_stability_pct": 0.0,
}
VNEXT_PLUS9_REPLAY_COUNT = 3
VNEXT_PLUS9_MANIFEST_SCHEMA = "stop_gate.vnext_plus9_manifest@1"
VNEXT_PLUS9_DEFAULT_METRICS = {
    "scheduler_dispatch_replay_determinism_pct": 0.0,
    "orphan_lease_recovery_determinism_pct": 0.0,
    "concurrent_budget_cancel_stability_pct": 0.0,
}
VNEXT_PLUS10_REPLAY_COUNT = 3
VNEXT_PLUS10_MANIFEST_SCHEMA = "stop_gate.vnext_plus10_manifest@1"
SEMANTIC_DEPTH_EXPECTED_CONFLICTS_SCHEMA = "semantic_depth.expected_conflicts@1"
VNEXT_PLUS10_DEFAULT_METRICS = {
    "concept_conflict_precision_pct": 0.0,
    "concept_conflict_recall_pct": 0.0,
    "coherence_permutation_stability_pct": 0.0,
    # Macro precision/recall are non-gating diagnostics in this arc.
    "concept_conflict_precision_macro_pct": 0.0,
    "concept_conflict_recall_macro_pct": 0.0,
}
VNEXT_PLUS10_MAX_PLATEAU_EPSILON_PCT = 0.1
VNEXT_PLUS11_REPLAY_COUNT = 3
VNEXT_PLUS11_MANIFEST_SCHEMA = "stop_gate.vnext_plus11_manifest@1"
DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELDS = frozenset(
    {
        "domain_conformance_hash",
        "hash_excluded_fields",
        "generated_at",
        "runtime_root_path",
        "missing_runtime_root_path",
        "operator_note",
    }
)
VNEXT_PLUS11_DEFAULT_METRICS = {
    "domain_conformance_replay_determinism_pct": 0.0,
    "cross_domain_artifact_parity_pct": 0.0,
    "runtime_domain_coupling_guard_pct": 0.0,
}
ADEU_CORE_IR_SCHEMA = "adeu_core_ir@0.1"
ADEU_LANE_PROJECTION_SCHEMA = "adeu_lane_projection@0.1"
VNEXT_PLUS13_REPLAY_COUNT = 3
VNEXT_PLUS13_MANIFEST_SCHEMA = "stop_gate.vnext_plus13_manifest@1"
VNEXT_PLUS13_DEFAULT_METRICS = {
    "adeu_core_ir_replay_determinism_pct": 0.0,
    "adeu_claim_ledger_recompute_match_pct": 0.0,
    "adeu_lane_projection_determinism_pct": 0.0,
}
FROZEN_QUALITY_METRIC_RULES: dict[str, str] = {
    "redundancy_rate": "non_increasing",
    "top_k_stability@10": "non_decreasing",
    "evidence_coverage_rate": "non_decreasing",
    "bridge_loss_utilization_rate": "non_decreasing",
    "coherence_alert_count": "non_increasing",
}
LEGACY_QUALITY_METRIC_RULES: dict[str, str] = {
    "question_stability_pct": "non_decreasing",
}

THRESHOLDS = {
    "policy_incident_reproducibility_pct": 99.0,
    "child_lifecycle_replay_determinism_pct": 100.0,
    "runtime_failure_code_stability_pct": 100.0,
    "connector_snapshot_replay_stability_pct": 100.0,
    "validator_packet_determinism_pct": 100.0,
    "witness_reconstruction_determinism_pct": 100.0,
    "semantics_diagnostics_determinism_pct": 100.0,
    "policy_lint_determinism_pct": 100.0,
    "proof_replay_determinism_pct": 100.0,
    "policy_proof_packet_hash_stability_pct": 100.0,
    "explain_diff_determinism_pct": 100.0,
    "explain_api_cli_parity_pct": 100.0,
    "explain_hash_stability_pct": 100.0,
    "scheduler_dispatch_replay_determinism_pct": 100.0,
    "orphan_lease_recovery_determinism_pct": 100.0,
    "concurrent_budget_cancel_stability_pct": 100.0,
    "concept_conflict_precision_pct": 95.0,
    "concept_conflict_recall_pct": 95.0,
    "coherence_permutation_stability_pct": 100.0,
    "domain_conformance_replay_determinism_pct": 100.0,
    "cross_domain_artifact_parity_pct": 100.0,
    "runtime_domain_coupling_guard_pct": 100.0,
    "adeu_core_ir_replay_determinism_pct": 100.0,
    "adeu_claim_ledger_recompute_match_pct": 100.0,
    "adeu_lane_projection_determinism_pct": 100.0,
    "semantic_depth_improvement_lock": True,
    "quality_delta_non_negative": True,
}

_CHILD_LIFECYCLE_EVENTS = {"WORKER_START", "WORKER_PASS", "WORKER_FAIL", "WORKER_CANCEL"}
_TERMINAL_CODE_EVENTS = {
    "SESSION_FAIL",
    "WORKER_FAIL",
    "WORKER_CANCEL",
    "POLICY_DENIED",
    "STEER_DENIED",
}


def _discover_repo_root(anchor: Path) -> Path | None:
    resolved = anchor.resolve()
    for parent in [resolved, *resolved.parents]:
        if (parent / ".git").exists():
            return parent
    return None


def _default_manifest_path(filename: str) -> Path:
    module_path = Path(__file__).resolve()
    repo_root = _discover_repo_root(module_path)
    if repo_root is not None:
        return repo_root / "apps" / "api" / "fixtures" / "stop_gate" / filename
    return module_path.parent / filename


def _default_vnext_plus7_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus7_manifest.json")


def _default_vnext_plus8_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus8_manifest.json")


def _default_vnext_plus9_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus9_manifest.json")


def _default_vnext_plus10_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus10_manifest.json")


def _default_vnext_plus11_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus11_manifest.json")


def _default_vnext_plus13_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus13_manifest.json")


VNEXT_PLUS7_MANIFEST_PATH = _default_vnext_plus7_manifest_path()
VNEXT_PLUS8_MANIFEST_PATH = _default_vnext_plus8_manifest_path()
VNEXT_PLUS9_MANIFEST_PATH = _default_vnext_plus9_manifest_path()
VNEXT_PLUS10_MANIFEST_PATH = _default_vnext_plus10_manifest_path()
VNEXT_PLUS11_MANIFEST_PATH = _default_vnext_plus11_manifest_path()
VNEXT_PLUS13_MANIFEST_PATH = _default_vnext_plus13_manifest_path()


def _validator_packet_hash(payload: Mapping[str, Any]) -> str:
    return sha256_canonical_json(strip_nonsemantic_validator_fields(payload))


def _normalize_witness_trace(raw_trace: Any) -> list[dict[str, str | None]]:
    if not isinstance(raw_trace, list):
        return []
    normalized: list[dict[str, str | None]] = []
    for item in raw_trace:
        if not isinstance(item, Mapping):
            continue
        raw_assertion_name = item.get("assertion_name")
        if not isinstance(raw_assertion_name, str) or not raw_assertion_name:
            continue
        raw_object_id = item.get("object_id")
        raw_json_path = item.get("json_path")
        normalized.append(
            {
                "assertion_name": raw_assertion_name,
                "object_id": None if raw_object_id is None else str(raw_object_id),
                "json_path": None if raw_json_path is None else str(raw_json_path),
            }
        )
    return sorted(
        normalized,
        key=lambda ref: (
            ref["assertion_name"],
            ref["object_id"] or "",
            ref["json_path"] or "",
        ),
    )


def _witness_reconstruction_hash(payload: Mapping[str, Any]) -> str:
    evidence = payload.get("evidence")
    evidence_mapping = evidence if isinstance(evidence, Mapping) else {}
    unsat_core = evidence_mapping.get("unsat_core")
    normalized_unsat_core = (
        sorted(str(item) for item in unsat_core)
        if isinstance(unsat_core, list)
        else []
    )
    witness_payload = {
        "status": str(payload.get("status", "")),
        "formula_hash": str(payload.get("formula_hash", "")),
        "request_hash": str(payload.get("request_hash", "")),
        "unsat_core": normalized_unsat_core,
        "core_trace": _normalize_witness_trace(evidence_mapping.get("core_trace")),
    }
    return sha256_canonical_json(witness_payload)


def _semantics_diagnostics_hash(payload: Mapping[str, Any]) -> str:
    basis = {k: payload[k] for k in sorted(payload.keys()) if k != "semantics_diagnostics_hash"}
    return sha256_canonical_json(basis)


def _group_replay_determinism_pct(
    *,
    replay_groups: dict[str, set[str]],
    replay_counts: dict[str, int],
) -> float:
    total = len(replay_groups)
    if total <= 0:
        return 0.0
    passed = sum(
        1
        for replay_key, hashes in replay_groups.items()
        if len(hashes) == 1
        and replay_counts.get(replay_key, 0) == SEMANTICS_DETERMINISM_REPLAY_COUNT
    )
    return _pct(passed, total)


def _proof_packet_hash(payload: Mapping[str, Any]) -> str:
    return sha256_canonical_json(strip_nonsemantic_proof_fields(payload))


def _policy_lineage_hash(payload: Mapping[str, Any]) -> str:
    return sha256_canonical_json(payload)


def _strip_nonsemantic_explain_fields(
    value: Any,
    *,
    excluded_fields: set[str],
) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for key in sorted(value.keys()):
            key_str = str(key)
            if key_str in excluded_fields:
                continue
            normalized[key_str] = _strip_nonsemantic_explain_fields(
                value[key],
                excluded_fields=excluded_fields,
            )
        return normalized
    if isinstance(value, list):
        return [
            _strip_nonsemantic_explain_fields(item, excluded_fields=excluded_fields)
            for item in value
        ]
    return value


def _explain_payload_hash(payload: Mapping[str, Any]) -> str:
    raw_excluded_fields = payload.get("hash_excluded_fields")
    if not isinstance(raw_excluded_fields, list) or not all(
        isinstance(field, str) for field in raw_excluded_fields
    ):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "explain_diff fixture missing valid hash_excluded_fields list",
            )
        )
    excluded_fields = set(raw_excluded_fields)
    stripped = _strip_nonsemantic_explain_fields(
        payload,
        excluded_fields=excluded_fields,
    )
    return sha256_canonical_json(stripped)


def _validated_explain_payload(
    *,
    explain_path: Path,
    description: str,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(explain_path, description=description)
    if payload.get("schema") != EXPLAIN_DIFF_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "explain fixture input must use explain_diff@1",
                context={"path": str(explain_path)},
            )
        )
    recomputed_hash = _explain_payload_hash(payload)
    embedded_hash = payload.get("explain_hash")
    if not isinstance(embedded_hash, str) or embedded_hash != recomputed_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "explain_hash mismatch for fixture payload",
                context={"path": str(explain_path)},
            )
        )
    return payload, recomputed_hash


def _explain_fixture_hash(*, explain_diff_path: Path) -> str:
    _, recomputed_hash = _validated_explain_payload(
        explain_path=explain_diff_path,
        description="explain diff fixture",
    )
    return recomputed_hash


def _explain_packet_snapshot_hash(*, explain_diff_path: Path) -> str:
    payload, _ = _validated_explain_payload(
        explain_path=explain_diff_path,
        description="explain diff fixture",
    )
    return sha256_canonical_json(payload)


def _explain_api_cli_parity_hash(
    *,
    api_explain_path: Path,
    cli_explain_path: Path,
) -> tuple[str, bool]:
    _, api_recomputed_hash = _validated_explain_payload(
        explain_path=api_explain_path,
        description="api explain fixture",
    )
    _, cli_recomputed_hash = _validated_explain_payload(
        explain_path=cli_explain_path,
        description="cli explain fixture",
    )
    pair_hash = sha256_canonical_json(
        {
            "api_recomputed_hash": api_recomputed_hash,
            "cli_recomputed_hash": cli_recomputed_hash,
        }
    )
    return pair_hash, api_recomputed_hash == cli_recomputed_hash


def _scheduler_dispatch_fixture_hash(*, dispatch_token_path: Path) -> str:
    payload = _read_json_object(dispatch_token_path, description="scheduler dispatch token fixture")
    if payload.get("schema") != "scheduler_dispatch_token@1":
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "scheduler dispatch token fixture must use scheduler_dispatch_token@1",
                context={"path": str(dispatch_token_path)},
            )
        )
    required_fields: dict[str, type] = {
        "child_id": str,
        "parent_session_id": str,
        "parent_stream_id": str,
        "parent_seq": int,
        "queue_seq": int,
        "dispatch_seq": int,
        "worker_run_id": str,
        "phase": str,
    }
    semantic_payload: dict[str, Any] = {}
    for field_name, field_type in required_fields.items():
        value = payload.get(field_name)
        if not isinstance(value, field_type):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "scheduler dispatch token fixture is missing required fields",
                    context={"path": str(dispatch_token_path), "field": field_name},
                )
            )
        semantic_payload[field_name] = value
    if semantic_payload["dispatch_seq"] < 1 or semantic_payload["queue_seq"] < 1:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "scheduler dispatch token fixture has invalid sequence anchors",
                context={"path": str(dispatch_token_path)},
            )
        )
    return sha256_canonical_json(semantic_payload)


def _orphan_lease_recovery_fixture_hash(*, orphan_recovery_event_path: Path) -> str:
    validation = validate_events(orphan_recovery_event_path, strict=True)
    if validation.get("valid") is not True:
        issues = validation.get("issues", [])
        first = issues[0] if issues and isinstance(issues[0], dict) else {}
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "orphan-lease fixture event stream failed validation",
                context={
                    "path": str(orphan_recovery_event_path),
                    "issue_code": first.get("code"),
                    "issue_message": first.get("message"),
                },
            )
        )
    events = _load_events(orphan_recovery_event_path)
    recovery_events: list[dict[str, Any]] = []
    for event in events:
        if event.event != "WORKER_FAIL":
            continue
        detail = event.detail
        reason = detail.get("reason")
        code = detail.get("code")
        if not isinstance(code, str):
            code = detail.get("error_code")
        if (
            reason != "lease_orphaned"
            or not isinstance(code, str)
            or code != "URM_SCHEDULER_LEASE_ORPHANED"
        ):
            continue
        recovery_events.append(
            {
                "stream_id": event.stream_id,
                "seq": event.seq,
                "child_id": detail.get("child_id"),
                "dispatch_seq": detail.get("dispatch_seq"),
                "lease_id": detail.get("lease_id"),
                "parent_stream_id": detail.get("parent_stream_id"),
                "parent_seq": detail.get("parent_seq"),
                "phase": detail.get("phase"),
                "reason": reason,
                "code": code,
            }
        )
    if not recovery_events:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "orphan-lease fixture must include WORKER_FAIL lease_orphaned event(s)",
                context={"path": str(orphan_recovery_event_path)},
            )
        )
    return sha256_canonical_json(recovery_events)


def _concurrent_budget_cancel_fixture_hash(*, budget_cancel_event_path: Path) -> str:
    validation = validate_events(budget_cancel_event_path, strict=True)
    if validation.get("valid") is not True:
        issues = validation.get("issues", [])
        first = issues[0] if issues and isinstance(issues[0], dict) else {}
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "concurrent budget/cancel fixture event stream failed validation",
                context={
                    "path": str(budget_cancel_event_path),
                    "issue_code": first.get("code"),
                    "issue_message": first.get("message"),
                },
            )
        )
    events = _load_events(budget_cancel_event_path)
    projection: list[dict[str, Any]] = []
    has_cancel = False
    has_budget_fail = False
    for event in events:
        if event.event not in {"WORKER_CANCEL", "WORKER_FAIL", "WORKER_PASS"}:
            continue
        detail = event.detail
        code = detail.get("code")
        if not isinstance(code, str):
            code = detail.get("error_code")
        if event.event == "WORKER_CANCEL":
            has_cancel = True
        if isinstance(code, str) and code == "URM_CHILD_BUDGET_EXCEEDED":
            has_budget_fail = True
        projection.append(
            {
                "event": event.event,
                "stream_id": event.stream_id,
                "seq": event.seq,
                "child_id": detail.get("child_id"),
                "dispatch_seq": detail.get("dispatch_seq"),
                "lease_id": detail.get("lease_id"),
                "parent_stream_id": detail.get("parent_stream_id"),
                "parent_seq": detail.get("parent_seq"),
                "phase": detail.get("phase"),
                "status": detail.get("status"),
                "reason": detail.get("reason"),
                "code": code,
                "cancel_request_id": detail.get("cancel_request_id"),
            }
        )
    if not has_cancel or not has_budget_fail:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "concurrent budget/cancel fixture must include cancel and budget-fail events",
                context={"path": str(budget_cancel_event_path)},
            )
        )
    return sha256_canonical_json(projection)


def _validated_semantic_depth_report_payload(*, semantic_depth_report_path: Path) -> dict[str, Any]:
    payload = _read_json_object(
        semantic_depth_report_path,
        description="semantic-depth report fixture",
    )
    try:
        validate_semantic_depth_report(payload)
    except SemanticDepthError as exc:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "semantic-depth report fixture failed validation",
                context={
                    "path": str(semantic_depth_report_path),
                    "error": str(exc),
                },
            )
        ) from exc
    return payload


def _load_expected_conflict_ids(
    *,
    expected_conflict_ids_path: Path,
) -> set[str]:
    payload = _read_json_object(
        expected_conflict_ids_path,
        description="semantic-depth expected conflicts fixture",
    )
    if payload.get("schema") != SEMANTIC_DEPTH_EXPECTED_CONFLICTS_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "semantic-depth expected conflicts fixture has unsupported schema",
                context={
                    "path": str(expected_conflict_ids_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    raw_expected_ids = payload.get("expected_conflict_ids")
    if not isinstance(raw_expected_ids, list) or not all(
        isinstance(conflict_id, str) and conflict_id
        for conflict_id in raw_expected_ids
    ):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "semantic-depth expected conflicts fixture must include expected_conflict_ids[]",
                context={"path": str(expected_conflict_ids_path)},
            )
        )
    normalized_expected_ids = sorted(raw_expected_ids)
    if len(normalized_expected_ids) != len(set(normalized_expected_ids)):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "semantic-depth expected conflicts fixture contains duplicate conflict ids",
                context={"path": str(expected_conflict_ids_path)},
            )
        )
    return set(normalized_expected_ids)


def _semantic_depth_fixture_conflict_stats(
    *,
    semantic_depth_report_path: Path,
    expected_conflict_ids_path: Path,
) -> tuple[str, tuple[int, int, int]]:
    payload = _validated_semantic_depth_report_payload(
        semantic_depth_report_path=semantic_depth_report_path,
    )
    conflict_items = payload.get("conflict_items")
    if not isinstance(conflict_items, list):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "semantic-depth fixture missing conflict_items",
                context={"path": str(semantic_depth_report_path)},
            )
        )
    predicted_conflict_ids = sorted(
        str(item.get("conflict_id"))
        for item in conflict_items
        if isinstance(item, Mapping) and isinstance(item.get("conflict_id"), str)
    )
    if len(predicted_conflict_ids) != len(conflict_items):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "semantic-depth fixture contains invalid conflict_id entries",
                context={"path": str(semantic_depth_report_path)},
            )
        )
    predicted_ids = set(predicted_conflict_ids)
    expected_ids = _load_expected_conflict_ids(
        expected_conflict_ids_path=expected_conflict_ids_path,
    )
    tp = len(predicted_ids & expected_ids)
    fp = len(predicted_ids - expected_ids)
    fn = len(expected_ids - predicted_ids)
    run_hash = sha256_canonical_json(
        {
            "expected_conflict_ids": sorted(expected_ids),
            "predicted_conflict_ids": sorted(predicted_ids),
            "tp": tp,
            "fp": fp,
            "fn": fn,
        }
    )
    return run_hash, (tp, fp, fn)


def _semantic_depth_coherence_fixture_hash(*, semantic_depth_report_path: Path) -> str:
    payload = _validated_semantic_depth_report_payload(
        semantic_depth_report_path=semantic_depth_report_path,
    )
    coherence_summary_hash = payload.get("coherence_summary_hash")
    if not isinstance(coherence_summary_hash, str) or not coherence_summary_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "semantic-depth fixture missing coherence_summary_hash",
                context={"path": str(semantic_depth_report_path)},
            )
        )
    return coherence_summary_hash


def _strip_nonsemantic_domain_conformance_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for key in sorted(value.keys()):
            key_str = str(key)
            if key_str in DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELDS:
                continue
            normalized[key_str] = _strip_nonsemantic_domain_conformance_fields(value[key])
        return normalized
    if isinstance(value, list):
        return [_strip_nonsemantic_domain_conformance_fields(item) for item in value]
    return value


def _domain_conformance_hash(payload: Mapping[str, Any]) -> str:
    return sha256_canonical_json(_strip_nonsemantic_domain_conformance_fields(payload))


def _validated_domain_conformance_payload(
    *, domain_conformance_path: Path
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(
        domain_conformance_path,
        description="domain conformance fixture",
    )
    if payload.get("schema") != DOMAIN_CONFORMANCE_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "domain conformance fixture must use domain_conformance@1",
                context={"path": str(domain_conformance_path)},
            )
        )
    embedded_hash = payload.get("domain_conformance_hash")
    recomputed_hash = _domain_conformance_hash(payload)
    if not isinstance(embedded_hash, str) or embedded_hash != recomputed_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "domain_conformance_hash mismatch for fixture payload",
                context={"path": str(domain_conformance_path)},
            )
        )
    return payload, recomputed_hash


def _domain_conformance_replay_fixture_hash(*, domain_conformance_path: Path) -> str:
    _, recomputed_hash = _validated_domain_conformance_payload(
        domain_conformance_path=domain_conformance_path
    )
    return recomputed_hash


def _domain_conformance_artifact_parity_fixture_hash(
    *, domain_conformance_path: Path
) -> tuple[str, bool]:
    payload, recomputed_hash = _validated_domain_conformance_payload(
        domain_conformance_path=domain_conformance_path
    )
    artifact_parity = payload.get("artifact_parity")
    if not isinstance(artifact_parity, Mapping):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "domain conformance fixture missing artifact_parity",
                context={"path": str(domain_conformance_path)},
            )
        )
    return recomputed_hash, artifact_parity.get("valid") is True


def _domain_conformance_coupling_guard_fixture_hash(
    *, domain_conformance_path: Path
) -> tuple[str, bool]:
    payload, recomputed_hash = _validated_domain_conformance_payload(
        domain_conformance_path=domain_conformance_path
    )
    import_audit = payload.get("import_audit")
    registry_order_determinism = payload.get("registry_order_determinism")
    if not isinstance(import_audit, Mapping) or not isinstance(
        registry_order_determinism, Mapping
    ):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "domain conformance fixture missing runtime coupling checks",
                context={"path": str(domain_conformance_path)},
            )
        )
    run_ok = (
        import_audit.get("valid") is True
        and registry_order_determinism.get("valid") is True
    )
    return recomputed_hash, run_ok


_ADEU_CORE_LAYER_ORDER: dict[str, int] = {"O": 0, "E": 1, "D": 2, "U": 3}
_ADEU_CORE_ALLOWED_KINDS: dict[str, set[str]] = {
    "O": {"Entity", "Concept", "RelationType"},
    "E": {"Claim", "Assumption", "Question", "Evidence"},
    "D": {"PhysicalConstraint", "Norm", "Policy", "Exception"},
    "U": {"Goal", "Metric", "Preference"},
}
_ADEU_CORE_EDGE_TYPING_MATRIX: dict[str, tuple[set[str], set[str]]] = {
    "about": (
        {"E.Claim", "E.Assumption", "E.Question", "E.Evidence"},
        {"O.Entity", "O.Concept", "O.RelationType"},
    ),
    "defines": (
        {"E.Claim", "E.Evidence"},
        {"O.Concept", "O.RelationType"},
    ),
    "supports": (
        {"E.Evidence", "E.Claim"},
        {"E.Claim"},
    ),
    "refutes": (
        {"E.Evidence", "E.Claim"},
        {"E.Claim"},
    ),
    "depends_on": (
        {"E.Claim"},
        {"E.Claim", "E.Assumption", "E.Question", "E.Evidence"},
    ),
    "justifies": (
        {"E.Claim", "E.Evidence"},
        {"D.Norm", "D.Policy"},
    ),
    "gates": (
        {"D.Policy"},
        {"E.Claim", "E.Assumption", "E.Question"},
    ),
    "serves_goal": (
        {"D.PhysicalConstraint", "D.Norm", "D.Policy", "E.Claim"},
        {"U.Goal", "U.Metric"},
    ),
    "prioritizes": (
        {"U.Preference"},
        {"U.Goal", "U.Metric", "D.PhysicalConstraint", "D.Norm", "D.Policy", "D.Exception"},
    ),
    "excepts": (
        {"D.Exception"},
        {"D.PhysicalConstraint", "D.Norm", "D.Policy"},
    ),
}


def _core_ir_node_sort_key(node: Mapping[str, Any]) -> tuple[int, str, str]:
    raw_layer = node.get("layer")
    layer = raw_layer if isinstance(raw_layer, str) else ""
    raw_kind = node.get("kind")
    kind = raw_kind if isinstance(raw_kind, str) else ""
    raw_id = node.get("id")
    node_id = raw_id if isinstance(raw_id, str) else ""
    return (_ADEU_CORE_LAYER_ORDER.get(layer, 99), kind, node_id)


def _clamp_0_1000(value: int) -> int:
    if value < 0:
        return 0
    if value > 1000:
        return 1000
    return value


def _clamp01(value: float) -> float:
    if value < 0.0:
        return 0.0
    if value > 1.0:
        return 1.0
    return value


def _ratio_to_milli(value: float) -> int:
    return _clamp_0_1000(round(1000 * value))


def _display_from_milli(value: int) -> str:
    return f"{value / 1000:.3f}"


def _validate_claim_spans(
    *,
    core_ir_path: Path,
    claim_id: str,
    raw_spans: Any,
) -> None:
    if raw_spans is None:
        return
    if not isinstance(raw_spans, list):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "core IR claim spans must be a list",
                context={"path": str(core_ir_path), "claim_id": claim_id},
            )
        )
    for span_idx, span in enumerate(raw_spans):
        if not isinstance(span, Mapping):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "core IR claim span must be an object",
                    context={
                        "path": str(core_ir_path),
                        "claim_id": claim_id,
                        "span_index": span_idx,
                    },
                )
            )
        start = span.get("start")
        end = span.get("end")
        if not isinstance(start, int) or not isinstance(end, int) or start < 0 or end <= start:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "core IR claim span must satisfy 0 <= start < end",
                    context={
                        "path": str(core_ir_path),
                        "claim_id": claim_id,
                        "span_index": span_idx,
                    },
                )
            )


def _validated_adeu_core_ir_payload(
    *,
    core_ir_path: Path,
) -> tuple[dict[str, Any], dict[str, Mapping[str, Any]]]:
    payload = _read_json_object(core_ir_path, description="adeu core IR fixture")
    if payload.get("schema") != ADEU_CORE_IR_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "core IR fixture input must use adeu_core_ir@0.1",
                context={"path": str(core_ir_path)},
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "core IR fixture missing source_text_hash",
                context={"path": str(core_ir_path)},
            )
        )

    raw_nodes = payload.get("nodes")
    if not isinstance(raw_nodes, list):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "core IR fixture nodes must be a list",
                context={"path": str(core_ir_path)},
            )
        )
    observed_node_order: list[tuple[int, str, str]] = []
    node_index: dict[str, Mapping[str, Any]] = {}
    for node_idx, node in enumerate(raw_nodes):
        if not isinstance(node, Mapping):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "core IR node must be an object",
                    context={"path": str(core_ir_path), "node_index": node_idx},
                )
            )
        node_id = node.get("id")
        layer = node.get("layer")
        kind = node.get("kind")
        if not isinstance(node_id, str) or not node_id:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "core IR node id must be a non-empty string",
                    context={"path": str(core_ir_path), "node_index": node_idx},
                )
            )
        if not isinstance(layer, str) or layer not in _ADEU_CORE_ALLOWED_KINDS:
            raise ValueError(
                _issue(
                    "URM_ADEU_CORE_INVALID_LAYER",
                    "core IR node layer is invalid",
                    context={
                        "path": str(core_ir_path),
                        "node_id": node_id,
                        "layer": layer,
                    },
                )
            )
        if not isinstance(kind, str) or kind not in _ADEU_CORE_ALLOWED_KINDS[layer]:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "core IR node kind is invalid for layer",
                    context={
                        "path": str(core_ir_path),
                        "node_id": node_id,
                        "layer": layer,
                        "kind": kind,
                    },
                )
            )
        if node_id in node_index:
            raise ValueError(
                _issue(
                    "URM_ADEU_CORE_DUPLICATE_NODE_ID",
                    "core IR fixture contains duplicate node id",
                    context={"path": str(core_ir_path), "node_id": node_id},
                )
            )
        if layer == "E" and kind == "Claim":
            _validate_claim_spans(
                core_ir_path=core_ir_path,
                claim_id=node_id,
                raw_spans=node.get("spans"),
            )
            confidence = node.get("confidence")
            if confidence is not None and not isinstance(confidence, (int, float)):
                raise ValueError(
                    _issue(
                        "URM_STOP_GATE_INPUT_INVALID",
                        "core IR claim confidence must be numeric when present",
                        context={"path": str(core_ir_path), "claim_id": node_id},
                    )
                )
        node_index[node_id] = node
        observed_node_order.append(
            (_ADEU_CORE_LAYER_ORDER[layer], kind, node_id)
        )
    if observed_node_order != sorted(observed_node_order):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "core IR fixture nodes must be sorted by (layer, kind, id)",
                context={"path": str(core_ir_path)},
            )
        )

    raw_edges = payload.get("edges")
    if not isinstance(raw_edges, list):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "core IR fixture edges must be a list",
                context={"path": str(core_ir_path)},
            )
        )
    observed_edge_order: list[tuple[str, str, str]] = []
    seen_edges: set[tuple[str, str, str]] = set()
    for edge_idx, edge in enumerate(raw_edges):
        if not isinstance(edge, Mapping):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "core IR edge must be an object",
                    context={"path": str(core_ir_path), "edge_index": edge_idx},
                )
            )
        edge_type = edge.get("type")
        from_ref = edge.get("from")
        to_ref = edge.get("to")
        if not isinstance(edge_type, str) or edge_type not in _ADEU_CORE_EDGE_TYPING_MATRIX:
            raise ValueError(
                _issue(
                    "URM_ADEU_CORE_INVALID_EDGE_TYPE",
                    "core IR edge type is invalid",
                    context={
                        "path": str(core_ir_path),
                        "edge_index": edge_idx,
                        "type": edge_type,
                    },
                )
            )
        if (
            not isinstance(from_ref, str)
            or not from_ref
            or not isinstance(to_ref, str)
            or not to_ref
        ):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "core IR edge refs must be non-empty strings",
                    context={
                        "path": str(core_ir_path),
                        "edge_index": edge_idx,
                    },
                )
            )
        identity = (edge_type, from_ref, to_ref)
        if identity in seen_edges:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "core IR fixture contains duplicate edge identity",
                    context={"path": str(core_ir_path), "edge": identity},
                )
            )
        seen_edges.add(identity)
        observed_edge_order.append(identity)
        from_node = node_index.get(from_ref)
        to_node = node_index.get(to_ref)
        if from_node is None or to_node is None:
            raise ValueError(
                _issue(
                    "URM_ADEU_CORE_DANGLING_REF",
                    "core IR fixture edge references unknown node id",
                    context={
                        "path": str(core_ir_path),
                        "edge": identity,
                    },
                )
            )
        from_sig = f"{from_node['layer']}.{from_node['kind']}"
        to_sig = f"{to_node['layer']}.{to_node['kind']}"
        allowed_from, allowed_to = _ADEU_CORE_EDGE_TYPING_MATRIX[edge_type]
        if from_sig not in allowed_from or to_sig not in allowed_to:
            raise ValueError(
                _issue(
                    "URM_ADEU_CORE_EDGE_TYPING_VIOLATION",
                    "core IR fixture edge violates frozen typing matrix",
                    context={
                        "path": str(core_ir_path),
                        "edge_type": edge_type,
                        "from": from_sig,
                        "to": to_sig,
                    },
                )
            )
    if observed_edge_order != sorted(observed_edge_order):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "core IR fixture edges must be sorted by (type, from, to)",
                context={"path": str(core_ir_path)},
            )
        )
    return payload, node_index


def _compute_adeu_claim_scores(
    *,
    payload: Mapping[str, Any],
    node_index: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    claim_nodes = {
        str(node["id"]): node
        for node in payload.get("nodes", [])
        if isinstance(node, Mapping)
        and node.get("layer") == "E"
        and node.get("kind") == "Claim"
        and isinstance(node.get("id"), str)
    }
    supports_to_claim: dict[str, int] = {claim_id: 0 for claim_id in claim_nodes}
    refutes_to_claim: dict[str, int] = {claim_id: 0 for claim_id in claim_nodes}
    dependencies_from_claim: dict[str, list[str]] = {claim_id: [] for claim_id in claim_nodes}
    for edge in payload.get("edges", []):
        if not isinstance(edge, Mapping):
            continue
        edge_type = edge.get("type")
        from_ref = edge.get("from")
        to_ref = edge.get("to")
        if not isinstance(from_ref, str) or not isinstance(to_ref, str):
            continue
        if edge_type == "supports" and to_ref in supports_to_claim:
            supports_to_claim[to_ref] += 1
        elif edge_type == "refutes" and to_ref in refutes_to_claim:
            refutes_to_claim[to_ref] += 1
        elif edge_type == "depends_on" and from_ref in dependencies_from_claim:
            dependencies_from_claim[from_ref].append(to_ref)

    claim_scores: dict[str, dict[str, Any]] = {}
    for claim_id, claim_node in claim_nodes.items():
        supports = supports_to_claim.get(claim_id, 0)
        refutes = refutes_to_claim.get(claim_id, 0)
        dependencies = dependencies_from_claim.get(claim_id, [])
        total_dependencies = len(dependencies)
        resolved_dependencies = sum(
            1
            for dep_id in dependencies
            if isinstance(node_index.get(dep_id), Mapping)
            and node_index[dep_id].get("layer") == "E"
            and node_index[dep_id].get("kind") in {"Claim", "Evidence"}
        )
        evidence_support_ratio_milli = _ratio_to_milli(
            supports / max(1, supports + refutes)
        )
        dependency_resolution_ratio_milli = _ratio_to_milli(
            resolved_dependencies / max(1, total_dependencies)
        )
        claim_spans = claim_node.get("spans")
        if claim_spans is None:
            claim_spans = []
        provenance_anchor_ratio_milli = 1000 if isinstance(claim_spans, list) and claim_spans else 0
        s_milli = _clamp_0_1000(
            (
                500 * evidence_support_ratio_milli
                + 300 * dependency_resolution_ratio_milli
                + 200 * provenance_anchor_ratio_milli
                + 500
            )
            // 1000
        )
        raw_confidence = claim_node.get("confidence")
        confidence = float(raw_confidence) if isinstance(raw_confidence, (int, float)) else 0.0
        b_milli = _clamp_0_1000(round(1000 * _clamp01(confidence)))
        r_milli = _clamp_0_1000(b_milli - s_milli)
        claim_scores[claim_id] = {
            "claim_id": claim_id,
            "ledger_version": "adeu.sbr.v0_1",
            "S_milli": s_milli,
            "B_milli": b_milli,
            "R_milli": r_milli,
            "S": _display_from_milli(s_milli),
            "B": _display_from_milli(b_milli),
            "R": _display_from_milli(r_milli),
        }
    return claim_scores


def _assert_adeu_claim_ledger_recompute_match(
    *,
    payload: Mapping[str, Any],
    node_index: Mapping[str, Mapping[str, Any]],
    core_ir_path: Path,
) -> dict[str, dict[str, Any]]:
    claim_scores = _compute_adeu_claim_scores(payload=payload, node_index=node_index)
    mismatched_claims: list[str] = []
    for node in payload.get("nodes", []):
        if not isinstance(node, Mapping):
            continue
        if node.get("layer") != "E" or node.get("kind") != "Claim":
            continue
        claim_id = node.get("id")
        if not isinstance(claim_id, str):
            continue
        expected = claim_scores.get(claim_id)
        if expected is None:
            mismatched_claims.append(claim_id)
            continue
        display_mismatch = False
        for display_key in ("S", "B", "R"):
            raw_display = node.get(display_key)
            if raw_display is not None and raw_display != expected[display_key]:
                display_mismatch = True
                break
        if (
            node.get("ledger_version") != expected["ledger_version"]
            or node.get("S_milli") != expected["S_milli"]
            or node.get("B_milli") != expected["B_milli"]
            or node.get("R_milli") != expected["R_milli"]
            or display_mismatch
        ):
            mismatched_claims.append(claim_id)
    if mismatched_claims:
        raise ValueError(
            _issue(
                "URM_ADEU_CORE_LEDGER_RECOMPUTE_MISMATCH",
                "core IR claim-ledger recompute mismatch",
                context={
                    "path": str(core_ir_path),
                    "claims": sorted(mismatched_claims),
                },
            )
        )
    return claim_scores


def _adeu_core_ir_replay_fixture_hash(*, core_ir_path: Path) -> str:
    payload, _ = _validated_adeu_core_ir_payload(core_ir_path=core_ir_path)
    return sha256_canonical_json(payload)


def _adeu_claim_ledger_recompute_fixture_hash(*, core_ir_path: Path) -> str:
    payload, node_index = _validated_adeu_core_ir_payload(core_ir_path=core_ir_path)
    claim_scores = _assert_adeu_claim_ledger_recompute_match(
        payload=payload,
        node_index=node_index,
        core_ir_path=core_ir_path,
    )
    return sha256_canonical_json(
        {
            "source_text_hash": payload.get("source_text_hash"),
            "claims": [claim_scores[claim_id] for claim_id in sorted(claim_scores)],
        }
    )


def _adeu_lane_projection_fixture_hash(*, core_ir_path: Path) -> str:
    payload, _ = _validated_adeu_core_ir_payload(core_ir_path=core_ir_path)
    projection = {
        "schema": ADEU_LANE_PROJECTION_SCHEMA,
        "source_text_hash": payload.get("source_text_hash"),
        "lanes": {
            "O": [
                str(node["id"])
                for node in payload.get("nodes", [])
                if isinstance(node, Mapping) and node.get("layer") == "O"
            ],
            "E": [
                str(node["id"])
                for node in payload.get("nodes", [])
                if isinstance(node, Mapping) and node.get("layer") == "E"
            ],
            "D": [
                str(node["id"])
                for node in payload.get("nodes", [])
                if isinstance(node, Mapping) and node.get("layer") == "D"
            ],
            "U": [
                str(node["id"])
                for node in payload.get("nodes", [])
                if isinstance(node, Mapping) and node.get("layer") == "U"
            ],
        },
        "edges": [
            {
                "type": edge["type"],
                "from": edge["from"],
                "to": edge["to"],
            }
            for edge in payload.get("edges", [])
            if isinstance(edge, Mapping)
        ],
    }
    return sha256_canonical_json(projection)


def _issue(code: str, message: str, *, context: dict[str, Any] | None = None) -> dict[str, Any]:
    return {"code": code, "message": message, "context": dict(context or {})}


def _issue_with_context(issue: dict[str, Any], *, context: dict[str, Any]) -> dict[str, Any]:
    merged_context = dict(issue.get("context") or {})
    merged_context.update(context)
    return {
        "code": issue.get("code"),
        "message": issue.get("message"),
        "context": merged_context,
    }


def _read_json_object(path: Path, *, description: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                f"{description} is not readable",
                context={"path": str(path), "error": str(exc)},
            )
        ) from exc
    except json.JSONDecodeError as exc:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                f"{description} is invalid JSON",
                context={"path": str(path), "error": str(exc)},
            )
        ) from exc
    if not isinstance(payload, dict):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                f"{description} must be a JSON object",
                context={"path": str(path)},
            )
        )
    return payload


def _load_events(path: Path) -> list[NormalizedEvent]:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    events: list[NormalizedEvent] = []
    for line_no, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        try:
            payload = json.loads(line)
            event = NormalizedEvent.model_validate(payload)
        except (json.JSONDecodeError, ValidationError) as exc:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "event stream contains invalid urm-events@1 record",
                    context={
                        "path": str(path),
                        "line": line_no,
                        "error": str(exc),
                    },
                )
            ) from exc
        events.append(event)
    return events


def _parse_replay(lines: list[str]) -> list[NormalizedEvent]:
    parsed: list[NormalizedEvent] = []
    for line in lines:
        if not line.strip():
            continue
        parsed.append(NormalizedEvent.model_validate(json.loads(line)))
    return parsed


def _pct(passed: int, total: int) -> float:
    if total <= 0:
        return 0.0
    return round((passed / total) * 100.0, 6)


def _semantic_depth_precision_pct(*, tp: int, fp: int, fn: int) -> float:
    if (tp + fp) == 0:
        return 100.0 if (tp + fn) == 0 else 0.0
    return round((tp / (tp + fp)) * 100.0, 6)


def _semantic_depth_recall_pct(*, tp: int, fn: int) -> float:
    if (tp + fn) == 0:
        return 100.0
    return round((tp / (tp + fn)) * 100.0, 6)


def _mean(values: list[float]) -> float:
    if not values:
        return 0.0
    return round(sum(values) / len(values), 6)


def _resolve_manifest_relative_path(*, manifest_path: Path, raw_path: Any) -> Path:
    if not isinstance(raw_path, str) or not raw_path.strip():
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "manifest run path must be a non-empty string",
                context={"manifest_path": str(manifest_path)},
            )
        )
    candidate = Path(raw_path)
    if not candidate.is_absolute():
        candidate = (manifest_path.parent / candidate).resolve()
    return candidate


def _load_manifest_payload(*, manifest_path: Path) -> dict[str, Any]:
    payload = _read_json_object(manifest_path, description="vnext+7 stop-gate manifest")
    if payload.get("schema") != VNEXT_PLUS7_MANIFEST_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+7 stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS7_REPLAY_COUNT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+7 replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": VNEXT_PLUS7_REPLAY_COUNT,
                    "observed_replay_count": replay_count,
                },
            )
        )
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+7 stop-gate manifest metrics must be an object",
                context={"manifest_path": str(manifest_path)},
            )
        )
    return payload


def _manifest_metric_entries(
    *,
    metrics: Mapping[str, Any],
    metric_name: str,
    manifest_path: Path,
) -> list[dict[str, Any]]:
    raw_entries = metrics.get(metric_name)
    if not isinstance(raw_entries, list):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "manifest metric entries must be a list",
                context={
                    "manifest_path": str(manifest_path),
                    "metric": metric_name,
                },
            )
        )
    entries: list[dict[str, Any]] = []
    for idx, entry in enumerate(raw_entries):
        if not isinstance(entry, dict):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture entry must be an object",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_index": idx,
                    },
                )
            )
        entries.append(entry)
    return entries


def _policy_lint_fixture_hash(*, policy_lint_event_path: Path) -> str:
    validation = validate_events(policy_lint_event_path, strict=True)
    if validation.get("valid") is not True:
        issues = validation.get("issues", [])
        first = issues[0] if issues and isinstance(issues[0], dict) else {}
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "policy lint fixture event stream failed validation",
                context={
                    "path": str(policy_lint_event_path),
                    "issue_code": first.get("code"),
                    "issue_message": first.get("message"),
                },
            )
        )
    events = _load_events(policy_lint_event_path)
    lint_events: list[dict[str, Any]] = []
    for event in events:
        if event.event != "POLICY_LINT_FAILED":
            continue
        lint_events.append(
            {
                "event": event.event,
                "stream_id": event.stream_id,
                "seq": event.seq,
                "detail": event.detail,
            }
        )
    if not lint_events:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "policy lint fixture must include POLICY_LINT_FAILED event(s)",
                context={"path": str(policy_lint_event_path)},
            )
        )
    return sha256_canonical_json(lint_events)


def _proof_fixture_hash(*, proof_evidence_path: Path) -> str:
    payload = _read_json_object(proof_evidence_path, description="proof evidence fixture")
    if payload.get("schema") != PROOF_EVIDENCE_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "proof fixture input must use proof_evidence@1",
                context={"path": str(proof_evidence_path)},
            )
        )
    expected_hash = _proof_packet_hash(payload)
    actual_hash = payload.get("proof_evidence_hash")
    if not isinstance(actual_hash, str) or actual_hash != expected_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "proof_evidence_hash mismatch for fixture payload",
                context={"path": str(proof_evidence_path)},
            )
        )
    return expected_hash


def _policy_proof_fixture_hash(*, policy_lineage_path: Path, proof_evidence_path: Path) -> str:
    lineage_payload = _read_json_object(policy_lineage_path, description="policy lineage fixture")
    if lineage_payload.get("schema") != POLICY_LINEAGE_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "policy fixture input must use policy_lineage@1",
                context={"path": str(policy_lineage_path)},
            )
        )
    proof_hash = _proof_fixture_hash(proof_evidence_path=proof_evidence_path)
    lineage_hash = _policy_lineage_hash(lineage_payload)
    return sha256_canonical_json(
        {
            "policy_lineage_hash": lineage_hash,
            "proof_evidence_hash": proof_hash,
        }
    )


def _manifest_metric_pct(
    *,
    manifest_path: Path,
    metric_name: str,
    fixtures: list[dict[str, Any]],
    replay_count: int,
    required_run_fields: tuple[str, ...],
    run_hash_builder: Callable[..., Any],
    issues: list[dict[str, Any]],
) -> float:
    total = len(fixtures)
    if total <= 0:
        return 0.0

    passed = 0
    for fixture_index, fixture in enumerate(fixtures):
        fixture_id = fixture.get("fixture_id")
        if not isinstance(fixture_id, str) or not fixture_id:
            fixture_id = f"{metric_name}_fixture_{fixture_index}"
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture_id must be a non-empty string",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_index": fixture_index,
                    },
                )
            )

        runs = fixture.get("runs")
        if not isinstance(runs, list):
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture runs must be a list",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )
            continue
        if len(runs) != replay_count:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture run count does not match frozen replay count",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                        "expected_replays": replay_count,
                        "observed_replays": len(runs),
                    },
                )
            )
            continue

        fixture_hashes: set[str] = set()
        fixture_ok = True
        for run_index, run in enumerate(runs):
            if not isinstance(run, dict):
                issues.append(
                    _issue(
                        "URM_STOP_GATE_INPUT_INVALID",
                        "manifest run entry must be an object",
                        context={
                            "manifest_path": str(manifest_path),
                            "metric": metric_name,
                            "fixture_id": fixture_id,
                            "run_index": run_index,
                        },
                    )
                )
                fixture_ok = False
                continue
            try:
                resolved_paths = {
                    key: _resolve_manifest_relative_path(
                        manifest_path=manifest_path,
                        raw_path=run.get(key),
                    )
                    for key in required_run_fields
                }
                run_hash = run_hash_builder(**resolved_paths)
            except ValueError as exc:
                issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    str(exc),
                )
                issues.append(
                    _issue_with_context(
                        issue,
                        context={
                            "metric": metric_name,
                            "fixture_id": fixture_id,
                            "run_index": run_index,
                        },
                    )
                )
                fixture_ok = False
                continue
            run_ok = True
            run_hash_value = run_hash
            if isinstance(run_hash, tuple) and len(run_hash) == 2:
                run_hash_value, run_ok = run_hash
            if not isinstance(run_hash_value, str):
                issues.append(
                    _issue(
                        "URM_STOP_GATE_INPUT_INVALID",
                        "manifest run hash builder must return string hash",
                        context={
                            "manifest_path": str(manifest_path),
                            "metric": metric_name,
                            "fixture_id": fixture_id,
                            "run_index": run_index,
                        },
                    )
                )
                fixture_ok = False
                continue
            if not run_ok:
                fixture_ok = False
            fixture_hashes.add(run_hash_value)

        if fixture_ok and len(fixture_hashes) == 1:
            passed += 1
    return _pct(passed, total)


def _semantic_depth_precision_recall_from_manifest(
    *,
    manifest_path: Path,
    metric_name: str,
    fixtures: list[dict[str, Any]],
    replay_count: int,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    total_fixtures = len(fixtures)
    if total_fixtures <= 0:
        return {
            "precision_pct": 0.0,
            "recall_pct": 0.0,
            "precision_macro_pct": 0.0,
            "recall_macro_pct": 0.0,
            "evaluated_fixture_count": 0,
            "fixture_count": 0,
            "tp": 0,
            "fp": 0,
            "fn": 0,
        }

    total_tp = 0
    total_fp = 0
    total_fn = 0
    macro_precision_values: list[float] = []
    macro_recall_values: list[float] = []
    evaluated_fixture_count = 0

    for fixture_index, fixture in enumerate(fixtures):
        fixture_id = fixture.get("fixture_id")
        if not isinstance(fixture_id, str) or not fixture_id:
            fixture_id = f"{metric_name}_fixture_{fixture_index}"
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture_id must be a non-empty string",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_index": fixture_index,
                    },
                )
            )

        runs = fixture.get("runs")
        if not isinstance(runs, list):
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture runs must be a list",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )
            continue
        if len(runs) != replay_count:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture run count does not match frozen replay count",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                        "expected_replays": replay_count,
                        "observed_replays": len(runs),
                    },
                )
            )
            continue

        fixture_run_hashes: set[str] = set()
        fixture_run_stats: list[tuple[int, int, int]] = []
        fixture_ok = True
        for run_index, run in enumerate(runs):
            if not isinstance(run, dict):
                issues.append(
                    _issue(
                        "URM_STOP_GATE_INPUT_INVALID",
                        "manifest run entry must be an object",
                        context={
                            "manifest_path": str(manifest_path),
                            "metric": metric_name,
                            "fixture_id": fixture_id,
                            "run_index": run_index,
                        },
                    )
                )
                fixture_ok = False
                continue
            try:
                report_path = _resolve_manifest_relative_path(
                    manifest_path=manifest_path,
                    raw_path=run.get("semantic_depth_report_path"),
                )
                expected_conflict_ids_path = _resolve_manifest_relative_path(
                    manifest_path=manifest_path,
                    raw_path=run.get("expected_conflict_ids_path"),
                )
                run_hash, (tp, fp, fn) = _semantic_depth_fixture_conflict_stats(
                    semantic_depth_report_path=report_path,
                    expected_conflict_ids_path=expected_conflict_ids_path,
                )
            except ValueError as exc:
                issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    str(exc),
                )
                issues.append(
                    _issue_with_context(
                        issue,
                        context={
                            "metric": metric_name,
                            "fixture_id": fixture_id,
                            "run_index": run_index,
                        },
                    )
                )
                fixture_ok = False
                continue
            fixture_run_hashes.add(run_hash)
            fixture_run_stats.append((tp, fp, fn))

        if not fixture_ok:
            continue
        if len(fixture_run_hashes) != 1:
            continue

        tp, fp, fn = fixture_run_stats[0]
        total_tp += tp
        total_fp += fp
        total_fn += fn
        macro_precision_values.append(_semantic_depth_precision_pct(tp=tp, fp=fp, fn=fn))
        macro_recall_values.append(_semantic_depth_recall_pct(tp=tp, fn=fn))
        evaluated_fixture_count += 1

    precision_pct = _semantic_depth_precision_pct(tp=total_tp, fp=total_fp, fn=total_fn)
    recall_pct = _semantic_depth_recall_pct(tp=total_tp, fn=total_fn)
    if evaluated_fixture_count != total_fixtures:
        precision_pct = 0.0
        recall_pct = 0.0

    return {
        "precision_pct": precision_pct,
        "recall_pct": recall_pct,
        "precision_macro_pct": _mean(macro_precision_values),
        "recall_macro_pct": _mean(macro_recall_values),
        "evaluated_fixture_count": evaluated_fixture_count,
        "fixture_count": total_fixtures,
        "tp": total_tp,
        "fp": total_fp,
        "fn": total_fn,
    }


def _compute_vnext_plus7_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, float]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS7_MANIFEST_PATH
    )
    try:
        manifest = _load_manifest_payload(manifest_path=resolved_manifest_path)
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return dict(VNEXT_PLUS7_DEFAULT_METRICS)

    metrics_doc = manifest.get("metrics")
    assert isinstance(metrics_doc, Mapping)
    try:
        policy_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="policy_lint_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        proof_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="proof_replay_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        policy_proof_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="policy_proof_packet_hash_stability_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return dict(VNEXT_PLUS7_DEFAULT_METRICS)

    policy_lint_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="policy_lint_determinism_pct",
        fixtures=policy_fixtures,
        replay_count=VNEXT_PLUS7_REPLAY_COUNT,
        required_run_fields=("policy_lint_event_path",),
        run_hash_builder=_policy_lint_fixture_hash,
        issues=issues,
    )
    proof_replay_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="proof_replay_determinism_pct",
        fixtures=proof_fixtures,
        replay_count=VNEXT_PLUS7_REPLAY_COUNT,
        required_run_fields=("proof_evidence_path",),
        run_hash_builder=_proof_fixture_hash,
        issues=issues,
    )
    policy_proof_packet_hash_stability_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="policy_proof_packet_hash_stability_pct",
        fixtures=policy_proof_fixtures,
        replay_count=VNEXT_PLUS7_REPLAY_COUNT,
        required_run_fields=("policy_lineage_path", "proof_evidence_path"),
        run_hash_builder=_policy_proof_fixture_hash,
        issues=issues,
    )
    return {
        "policy_lint_determinism_pct": policy_lint_determinism_pct,
        "proof_replay_determinism_pct": proof_replay_determinism_pct,
        "policy_proof_packet_hash_stability_pct": policy_proof_packet_hash_stability_pct,
    }


def _load_vnext_plus8_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(manifest_path, description="vnext+8 stop-gate manifest")
    if payload.get("schema") != VNEXT_PLUS8_MANIFEST_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+8 stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS8_REPLAY_COUNT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+8 replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": VNEXT_PLUS8_REPLAY_COUNT,
                    "observed_replay_count": replay_count,
                },
            )
        )
    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+8 stop-gate manifest missing manifest_hash",
                context={"manifest_path": str(manifest_path)},
            )
        )
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+8 stop-gate manifest metrics must be an object",
                context={"manifest_path": str(manifest_path)},
            )
        )
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+8 manifest_hash mismatch",
                context={
                    "manifest_path": str(manifest_path),
                    "embedded_manifest_hash": raw_manifest_hash,
                    "recomputed_manifest_hash": recomputed_manifest_hash,
                },
            )
        )
    return payload, recomputed_manifest_hash


def _compute_vnext_plus8_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS8_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus8_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS8_DEFAULT_METRICS,
            "vnext_plus8_manifest_hash": "",
        }

    metrics_doc = manifest.get("metrics")
    assert isinstance(metrics_doc, Mapping)
    try:
        explain_diff_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="explain_diff_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        explain_api_cli_parity_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="explain_api_cli_parity_pct",
            manifest_path=resolved_manifest_path,
        )
        explain_hash_stability_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="explain_hash_stability_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS8_DEFAULT_METRICS,
            "vnext_plus8_manifest_hash": manifest_hash,
        }

    explain_diff_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="explain_diff_determinism_pct",
        fixtures=explain_diff_fixtures,
        replay_count=VNEXT_PLUS8_REPLAY_COUNT,
        required_run_fields=("explain_diff_path",),
        run_hash_builder=_explain_packet_snapshot_hash,
        issues=issues,
    )
    explain_api_cli_parity_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="explain_api_cli_parity_pct",
        fixtures=explain_api_cli_parity_fixtures,
        replay_count=VNEXT_PLUS8_REPLAY_COUNT,
        required_run_fields=("api_explain_path", "cli_explain_path"),
        run_hash_builder=_explain_api_cli_parity_hash,
        issues=issues,
    )
    explain_hash_stability_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="explain_hash_stability_pct",
        fixtures=explain_hash_stability_fixtures,
        replay_count=VNEXT_PLUS8_REPLAY_COUNT,
        required_run_fields=("explain_diff_path",),
        run_hash_builder=_explain_fixture_hash,
        issues=issues,
    )
    return {
        "explain_diff_determinism_pct": explain_diff_determinism_pct,
        "explain_api_cli_parity_pct": explain_api_cli_parity_pct,
        "explain_hash_stability_pct": explain_hash_stability_pct,
        "vnext_plus8_manifest_hash": manifest_hash,
    }


def _load_vnext_plus9_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(manifest_path, description="vnext+9 stop-gate manifest")
    if payload.get("schema") != VNEXT_PLUS9_MANIFEST_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+9 stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS9_REPLAY_COUNT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+9 replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": VNEXT_PLUS9_REPLAY_COUNT,
                    "observed_replay_count": replay_count,
                },
            )
        )
    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+9 stop-gate manifest missing manifest_hash",
                context={"manifest_path": str(manifest_path)},
            )
        )
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+9 stop-gate manifest metrics must be an object",
                context={"manifest_path": str(manifest_path)},
            )
        )
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+9 manifest_hash mismatch",
                context={
                    "manifest_path": str(manifest_path),
                    "embedded_manifest_hash": raw_manifest_hash,
                    "recomputed_manifest_hash": recomputed_manifest_hash,
                },
            )
        )
    return payload, recomputed_manifest_hash


def _compute_vnext_plus9_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS9_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus9_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS9_DEFAULT_METRICS,
            "vnext_plus9_manifest_hash": "",
        }

    metrics_doc = manifest.get("metrics")
    assert isinstance(metrics_doc, Mapping)
    try:
        scheduler_dispatch_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="scheduler_dispatch_replay_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        orphan_lease_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="orphan_lease_recovery_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        concurrent_budget_cancel_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="concurrent_budget_cancel_stability_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS9_DEFAULT_METRICS,
            "vnext_plus9_manifest_hash": manifest_hash,
        }

    scheduler_dispatch_replay_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="scheduler_dispatch_replay_determinism_pct",
        fixtures=scheduler_dispatch_fixtures,
        replay_count=VNEXT_PLUS9_REPLAY_COUNT,
        required_run_fields=("dispatch_token_path",),
        run_hash_builder=_scheduler_dispatch_fixture_hash,
        issues=issues,
    )
    orphan_lease_recovery_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="orphan_lease_recovery_determinism_pct",
        fixtures=orphan_lease_fixtures,
        replay_count=VNEXT_PLUS9_REPLAY_COUNT,
        required_run_fields=("orphan_recovery_event_path",),
        run_hash_builder=_orphan_lease_recovery_fixture_hash,
        issues=issues,
    )
    concurrent_budget_cancel_stability_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="concurrent_budget_cancel_stability_pct",
        fixtures=concurrent_budget_cancel_fixtures,
        replay_count=VNEXT_PLUS9_REPLAY_COUNT,
        required_run_fields=("budget_cancel_event_path",),
        run_hash_builder=_concurrent_budget_cancel_fixture_hash,
        issues=issues,
    )
    return {
        "scheduler_dispatch_replay_determinism_pct": scheduler_dispatch_replay_determinism_pct,
        "orphan_lease_recovery_determinism_pct": orphan_lease_recovery_determinism_pct,
        "concurrent_budget_cancel_stability_pct": concurrent_budget_cancel_stability_pct,
        "vnext_plus9_manifest_hash": manifest_hash,
    }


def _load_vnext_plus10_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(manifest_path, description="vnext+10 stop-gate manifest")
    if payload.get("schema") != VNEXT_PLUS10_MANIFEST_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+10 stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS10_REPLAY_COUNT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+10 replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": VNEXT_PLUS10_REPLAY_COUNT,
                    "observed_replay_count": replay_count,
                },
            )
        )
    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+10 stop-gate manifest missing manifest_hash",
                context={"manifest_path": str(manifest_path)},
            )
        )
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+10 stop-gate manifest metrics must be an object",
                context={"manifest_path": str(manifest_path)},
            )
        )
    for baseline_key in (
        "baseline_concept_conflict_precision_pct",
        "baseline_concept_conflict_recall_pct",
    ):
        baseline_value = payload.get(baseline_key)
        if not isinstance(baseline_value, (int, float)):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "vnext+10 manifest missing numeric baseline metric",
                    context={
                        "manifest_path": str(manifest_path),
                        "field": baseline_key,
                    },
                )
            )
    plateau_epsilon_pct = payload.get(
        "plateau_epsilon_pct",
        VNEXT_PLUS10_MAX_PLATEAU_EPSILON_PCT,
    )
    if not isinstance(plateau_epsilon_pct, (int, float)) or plateau_epsilon_pct < 0.0:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+10 plateau_epsilon_pct must be a non-negative number",
                context={"manifest_path": str(manifest_path)},
            )
        )
    if float(plateau_epsilon_pct) > VNEXT_PLUS10_MAX_PLATEAU_EPSILON_PCT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+10 plateau_epsilon_pct exceeds frozen maximum",
                context={
                    "manifest_path": str(manifest_path),
                    "observed_plateau_epsilon_pct": float(plateau_epsilon_pct),
                    "max_plateau_epsilon_pct": VNEXT_PLUS10_MAX_PLATEAU_EPSILON_PCT,
                },
            )
        )

    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+10 manifest_hash mismatch",
                context={
                    "manifest_path": str(manifest_path),
                    "embedded_manifest_hash": raw_manifest_hash,
                    "recomputed_manifest_hash": recomputed_manifest_hash,
                },
            )
        )
    return payload, recomputed_manifest_hash


def _compute_vnext_plus10_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS10_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus10_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS10_DEFAULT_METRICS,
            "precision_non_regression": False,
            "recall_non_regression": False,
            "strict_improvement_required": True,
            "strict_improvement_met": False,
            "plateau_eligible": False,
            "semantic_depth_improvement_lock_passed": False,
            "baseline_concept_conflict_precision_pct": 0.0,
            "baseline_concept_conflict_recall_pct": 0.0,
            "concept_conflict_precision_delta_pct": 0.0,
            "concept_conflict_recall_delta_pct": 0.0,
            "plateau_epsilon_pct": VNEXT_PLUS10_MAX_PLATEAU_EPSILON_PCT,
            "precision_fixture_count": 0,
            "precision_fixture_count_evaluated": 0,
            "recall_fixture_count": 0,
            "recall_fixture_count_evaluated": 0,
            "vnext_plus10_manifest_hash": "",
        }

    metrics_doc = manifest.get("metrics")
    assert isinstance(metrics_doc, Mapping)
    try:
        precision_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="concept_conflict_precision_pct",
            manifest_path=resolved_manifest_path,
        )
        recall_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="concept_conflict_recall_pct",
            manifest_path=resolved_manifest_path,
        )
        coherence_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="coherence_permutation_stability_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS10_DEFAULT_METRICS,
            "precision_non_regression": False,
            "recall_non_regression": False,
            "strict_improvement_required": True,
            "strict_improvement_met": False,
            "plateau_eligible": False,
            "semantic_depth_improvement_lock_passed": False,
            "baseline_concept_conflict_precision_pct": 0.0,
            "baseline_concept_conflict_recall_pct": 0.0,
            "concept_conflict_precision_delta_pct": 0.0,
            "concept_conflict_recall_delta_pct": 0.0,
            "plateau_epsilon_pct": VNEXT_PLUS10_MAX_PLATEAU_EPSILON_PCT,
            "precision_fixture_count": 0,
            "precision_fixture_count_evaluated": 0,
            "recall_fixture_count": 0,
            "recall_fixture_count_evaluated": 0,
            "vnext_plus10_manifest_hash": manifest_hash,
        }

    precision_eval = _semantic_depth_precision_recall_from_manifest(
        manifest_path=resolved_manifest_path,
        metric_name="concept_conflict_precision_pct",
        fixtures=precision_fixtures,
        replay_count=VNEXT_PLUS10_REPLAY_COUNT,
        issues=issues,
    )
    recall_eval = _semantic_depth_precision_recall_from_manifest(
        manifest_path=resolved_manifest_path,
        metric_name="concept_conflict_recall_pct",
        fixtures=recall_fixtures,
        replay_count=VNEXT_PLUS10_REPLAY_COUNT,
        issues=issues,
    )
    coherence_permutation_stability_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="coherence_permutation_stability_pct",
        fixtures=coherence_fixtures,
        replay_count=VNEXT_PLUS10_REPLAY_COUNT,
        required_run_fields=("semantic_depth_report_path",),
        run_hash_builder=_semantic_depth_coherence_fixture_hash,
        issues=issues,
    )

    concept_conflict_precision_pct = precision_eval["precision_pct"]
    concept_conflict_recall_pct = recall_eval["recall_pct"]
    baseline_precision = float(manifest.get("baseline_concept_conflict_precision_pct", 0.0))
    baseline_recall = float(manifest.get("baseline_concept_conflict_recall_pct", 0.0))
    precision_delta = round(concept_conflict_precision_pct - baseline_precision, 6)
    recall_delta = round(concept_conflict_recall_pct - baseline_recall, 6)
    precision_non_regression = concept_conflict_precision_pct >= baseline_precision
    recall_non_regression = concept_conflict_recall_pct >= baseline_recall
    strict_improvement_required = not (baseline_precision == 100.0 and baseline_recall == 100.0)
    strict_improvement_met = (
        concept_conflict_precision_pct > baseline_precision
        or concept_conflict_recall_pct > baseline_recall
    )
    plateau_epsilon_pct = float(
        manifest.get("plateau_epsilon_pct", VNEXT_PLUS10_MAX_PLATEAU_EPSILON_PCT)
    )
    plateau_eligible = (
        precision_non_regression
        and recall_non_regression
        and concept_conflict_precision_pct >= THRESHOLDS["concept_conflict_precision_pct"]
        and concept_conflict_recall_pct >= THRESHOLDS["concept_conflict_recall_pct"]
        and abs(precision_delta) <= plateau_epsilon_pct
        and abs(recall_delta) <= plateau_epsilon_pct
    )
    if strict_improvement_required:
        semantic_depth_improvement_lock_passed = (
            precision_non_regression
            and recall_non_regression
            and (strict_improvement_met or plateau_eligible)
        )
    else:
        semantic_depth_improvement_lock_passed = (
            precision_non_regression and recall_non_regression
        )

    return {
        "concept_conflict_precision_pct": concept_conflict_precision_pct,
        "concept_conflict_recall_pct": concept_conflict_recall_pct,
        "coherence_permutation_stability_pct": coherence_permutation_stability_pct,
        "concept_conflict_precision_macro_pct": precision_eval["precision_macro_pct"],
        "concept_conflict_recall_macro_pct": recall_eval["recall_macro_pct"],
        "precision_non_regression": precision_non_regression,
        "recall_non_regression": recall_non_regression,
        "strict_improvement_required": strict_improvement_required,
        "strict_improvement_met": strict_improvement_met,
        "plateau_eligible": plateau_eligible,
        "semantic_depth_improvement_lock_passed": semantic_depth_improvement_lock_passed,
        "baseline_concept_conflict_precision_pct": baseline_precision,
        "baseline_concept_conflict_recall_pct": baseline_recall,
        "concept_conflict_precision_delta_pct": precision_delta,
        "concept_conflict_recall_delta_pct": recall_delta,
        "plateau_epsilon_pct": plateau_epsilon_pct,
        "precision_fixture_count": precision_eval["fixture_count"],
        "precision_fixture_count_evaluated": precision_eval["evaluated_fixture_count"],
        "recall_fixture_count": recall_eval["fixture_count"],
        "recall_fixture_count_evaluated": recall_eval["evaluated_fixture_count"],
        "vnext_plus10_manifest_hash": manifest_hash,
    }


def _load_vnext_plus11_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(manifest_path, description="vnext+11 stop-gate manifest")
    if payload.get("schema") != VNEXT_PLUS11_MANIFEST_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+11 stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS11_REPLAY_COUNT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+11 replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": VNEXT_PLUS11_REPLAY_COUNT,
                    "observed_replay_count": replay_count,
                },
            )
        )
    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+11 stop-gate manifest missing manifest_hash",
                context={"manifest_path": str(manifest_path)},
            )
        )
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+11 stop-gate manifest metrics must be an object",
                context={"manifest_path": str(manifest_path)},
            )
        )
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ValueError(
            _issue(
                "URM_CONFORMANCE_MANIFEST_HASH_MISMATCH",
                "vnext+11 manifest_hash mismatch",
                context={
                    "manifest_path": str(manifest_path),
                    "embedded_manifest_hash": raw_manifest_hash,
                    "recomputed_manifest_hash": recomputed_manifest_hash,
                },
            )
        )
    return payload, recomputed_manifest_hash


def _compute_vnext_plus11_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS11_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus11_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS11_DEFAULT_METRICS,
            "vnext_plus11_manifest_hash": "",
        }

    metrics_doc = manifest.get("metrics")
    assert isinstance(metrics_doc, Mapping)
    try:
        domain_conformance_replay_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="domain_conformance_replay_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        artifact_parity_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="cross_domain_artifact_parity_pct",
            manifest_path=resolved_manifest_path,
        )
        runtime_coupling_fixtures = _manifest_metric_entries(
            metrics=metrics_doc,
            metric_name="runtime_domain_coupling_guard_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS11_DEFAULT_METRICS,
            "vnext_plus11_manifest_hash": manifest_hash,
        }

    domain_conformance_replay_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="domain_conformance_replay_determinism_pct",
        fixtures=domain_conformance_replay_fixtures,
        replay_count=VNEXT_PLUS11_REPLAY_COUNT,
        required_run_fields=("domain_conformance_path",),
        run_hash_builder=_domain_conformance_replay_fixture_hash,
        issues=issues,
    )
    cross_domain_artifact_parity_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="cross_domain_artifact_parity_pct",
        fixtures=artifact_parity_fixtures,
        replay_count=VNEXT_PLUS11_REPLAY_COUNT,
        required_run_fields=("domain_conformance_path",),
        run_hash_builder=_domain_conformance_artifact_parity_fixture_hash,
        issues=issues,
    )
    runtime_domain_coupling_guard_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="runtime_domain_coupling_guard_pct",
        fixtures=runtime_coupling_fixtures,
        replay_count=VNEXT_PLUS11_REPLAY_COUNT,
        required_run_fields=("domain_conformance_path",),
        run_hash_builder=_domain_conformance_coupling_guard_fixture_hash,
        issues=issues,
    )
    return {
        "domain_conformance_replay_determinism_pct": domain_conformance_replay_determinism_pct,
        "cross_domain_artifact_parity_pct": cross_domain_artifact_parity_pct,
        "runtime_domain_coupling_guard_pct": runtime_domain_coupling_guard_pct,
        "vnext_plus11_manifest_hash": manifest_hash,
    }


def _load_vnext_plus13_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(manifest_path, description="vnext+13 stop-gate manifest")
    if payload.get("schema") != VNEXT_PLUS13_MANIFEST_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+13 stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS13_REPLAY_COUNT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+13 replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": VNEXT_PLUS13_REPLAY_COUNT,
                    "observed_replay_count": replay_count,
                },
            )
        )
    for key in (
        "core_ir_replay_fixtures",
        "ledger_recompute_fixtures",
        "lane_projection_fixtures",
    ):
        if not isinstance(payload.get(key), list):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "vnext+13 stop-gate manifest missing required fixture list",
                    context={"manifest_path": str(manifest_path), "key": key},
                )
            )
    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+13 stop-gate manifest missing manifest_hash",
                context={"manifest_path": str(manifest_path)},
            )
        )
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_CORE_MANIFEST_HASH_MISMATCH",
                "vnext+13 manifest_hash mismatch",
                context={
                    "manifest_path": str(manifest_path),
                    "embedded_manifest_hash": raw_manifest_hash,
                    "recomputed_manifest_hash": recomputed_manifest_hash,
                },
            )
        )
    return payload, recomputed_manifest_hash


def _compute_vnext_plus13_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS13_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus13_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS13_DEFAULT_METRICS,
            "vnext_plus13_manifest_hash": "",
        }

    try:
        core_ir_replay_fixtures = _manifest_metric_entries(
            metrics={
                "adeu_core_ir_replay_determinism_pct": manifest.get(
                    "core_ir_replay_fixtures"
                )
            },
            metric_name="adeu_core_ir_replay_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        ledger_recompute_fixtures = _manifest_metric_entries(
            metrics={
                "adeu_claim_ledger_recompute_match_pct": manifest.get("ledger_recompute_fixtures")
            },
            metric_name="adeu_claim_ledger_recompute_match_pct",
            manifest_path=resolved_manifest_path,
        )
        lane_projection_fixtures = _manifest_metric_entries(
            metrics={
                "adeu_lane_projection_determinism_pct": manifest.get("lane_projection_fixtures")
            },
            metric_name="adeu_lane_projection_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS13_DEFAULT_METRICS,
            "vnext_plus13_manifest_hash": manifest_hash,
        }

    adeu_core_ir_replay_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="adeu_core_ir_replay_determinism_pct",
        fixtures=core_ir_replay_fixtures,
        replay_count=VNEXT_PLUS13_REPLAY_COUNT,
        required_run_fields=("core_ir_path",),
        run_hash_builder=_adeu_core_ir_replay_fixture_hash,
        issues=issues,
    )
    adeu_claim_ledger_recompute_match_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="adeu_claim_ledger_recompute_match_pct",
        fixtures=ledger_recompute_fixtures,
        replay_count=VNEXT_PLUS13_REPLAY_COUNT,
        required_run_fields=("core_ir_path",),
        run_hash_builder=_adeu_claim_ledger_recompute_fixture_hash,
        issues=issues,
    )
    adeu_lane_projection_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="adeu_lane_projection_determinism_pct",
        fixtures=lane_projection_fixtures,
        replay_count=VNEXT_PLUS13_REPLAY_COUNT,
        required_run_fields=("core_ir_path",),
        run_hash_builder=_adeu_lane_projection_fixture_hash,
        issues=issues,
    )
    return {
        "adeu_core_ir_replay_determinism_pct": adeu_core_ir_replay_determinism_pct,
        "adeu_claim_ledger_recompute_match_pct": adeu_claim_ledger_recompute_match_pct,
        "adeu_lane_projection_determinism_pct": adeu_lane_projection_determinism_pct,
        "vnext_plus13_manifest_hash": manifest_hash,
    }


def _metric_delta_satisfies_rule(*, rule: str, delta: float) -> bool:
    if rule == "non_decreasing":
        return delta >= 0.0
    if rule == "non_increasing":
        return delta <= 0.0
    return False


def _resolve_quality_metric_rules(
    *, current_metrics: dict[str, Any], baseline_metrics: dict[str, Any]
) -> tuple[dict[str, str] | None, str]:
    if all(
        metric_name in current_metrics and metric_name in baseline_metrics
        for metric_name in FROZEN_QUALITY_METRIC_RULES
    ):
        return FROZEN_QUALITY_METRIC_RULES, "frozen_v3"
    if all(
        metric_name in current_metrics and metric_name in baseline_metrics
        for metric_name in LEGACY_QUALITY_METRIC_RULES
    ):
        return LEGACY_QUALITY_METRIC_RULES, "legacy_v1"
    return None, "unresolved"


def _failure_code_sequence(events: list[NormalizedEvent]) -> list[dict[str, str | None]]:
    sequence: list[dict[str, str | None]] = []
    for event in events:
        detail = event.detail
        decision_code = detail.get("decision_code")
        if not isinstance(decision_code, str):
            decision_code = None
        terminal_event_code: str | None = None
        if event.event in _TERMINAL_CODE_EVENTS:
            terminal_raw = detail.get("terminal_event_code")
            if not isinstance(terminal_raw, str):
                terminal_raw = detail.get("error_code")
            if not isinstance(terminal_raw, str):
                terminal_raw = detail.get("code")
            if isinstance(terminal_raw, str):
                terminal_event_code = terminal_raw
        if decision_code is not None or terminal_event_code is not None:
            sequence.append(
                {
                    "decision_code": decision_code,
                    "terminal_event_code": terminal_event_code,
                }
            )
    return sequence


def build_stop_gate_metrics(
    *,
    incident_packet_paths: list[Path],
    event_stream_paths: list[Path],
    connector_snapshot_paths: list[Path],
    validator_evidence_packet_paths: list[Path],
    semantics_diagnostics_paths: list[Path],
    quality_current_path: Path,
    quality_baseline_path: Path | None = None,
    vnext_plus7_manifest_path: Path | None = None,
    vnext_plus8_manifest_path: Path | None = None,
    vnext_plus9_manifest_path: Path | None = None,
    vnext_plus10_manifest_path: Path | None = None,
    vnext_plus11_manifest_path: Path | None = None,
    vnext_plus13_manifest_path: Path | None = None,
) -> dict[str, Any]:
    issues: list[dict[str, Any]] = []
    try:
        incident_payloads = [
            _read_json_object(path, description="incident packet") for path in incident_packet_paths
        ]
        connector_payloads = [
            _read_json_object(path, description="connector snapshot")
            for path in connector_snapshot_paths
        ]
        validator_packet_payloads = [
            _read_json_object(path, description="validator evidence packet")
            for path in validator_evidence_packet_paths
        ]
        semantics_diagnostics_payloads = [
            _read_json_object(path, description="semantics diagnostics")
            for path in semantics_diagnostics_paths
        ]
        quality_current = _read_json_object(quality_current_path, description="quality dashboard")
        quality_baseline = _read_json_object(
            quality_baseline_path if quality_baseline_path is not None else quality_current_path,
            description="quality dashboard baseline",
        )

        parsed_event_streams: list[tuple[Path, list[NormalizedEvent]]] = []
        for path in event_stream_paths:
            validation = validate_events(path, strict=True)
            if validation["valid"] is not True:
                first = validation["issues"][0] if validation["issues"] else {"code": "UNKNOWN"}
                raise ValueError(
                    _issue(
                        "URM_STOP_GATE_INPUT_INVALID",
                        "event stream validation failed",
                        context={
                            "path": str(path),
                            "issue_code": first.get("code"),
                            "issue_message": first.get("message"),
                        },
                    )
                )
            parsed_event_streams.append((path, _load_events(path)))
    except ValueError as exc:
        issue = exc.args[0] if exc.args else _issue("URM_STOP_GATE_INPUT_INVALID", "invalid input")
        if isinstance(issue, dict):
            issues.append(issue)
        else:
            issues.append(_issue("URM_STOP_GATE_INPUT_INVALID", str(exc)))
        return {
            "schema": STOP_GATE_SCHEMA,
            "valid": False,
            "issues": issues,
        }

    if quality_current.get("dashboard_version") != QUALITY_DASHBOARD_SCHEMA:
        issues.append(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "quality dashboard current input has unsupported schema",
                context={"path": str(quality_current_path)},
            )
        )
    if quality_baseline.get("dashboard_version") != QUALITY_DASHBOARD_SCHEMA:
        issues.append(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "quality dashboard baseline input has unsupported schema",
                context={
                    "path": str(
                        quality_baseline_path
                        if quality_baseline_path is not None
                        else quality_current_path
                    )
                },
            )
        )

    incident_groups: dict[tuple[str, str], set[str]] = {}
    for payload, path in zip(incident_payloads, incident_packet_paths):
        if payload.get("schema") != POLICY_INCIDENT_SCHEMA or payload.get("valid") is not True:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "incident packet input must be valid incident_packet@1",
                    context={"path": str(path)},
                )
            )
            continue
        policy_hash = payload.get("policy_hash")
        input_context_hash = payload.get("input_context_hash")
        if not isinstance(policy_hash, str) or not isinstance(input_context_hash, str):
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "incident packet input missing required hash fields",
                    context={"path": str(path)},
                )
            )
            continue
        semantic_payload = {
            "decision_code": payload.get("decision_code"),
            "matched_rule_ids": payload.get("matched_rule_ids"),
            "artifact_refs": payload.get("artifact_refs"),
            "streams": payload.get("streams"),
        }
        group_key = (policy_hash, input_context_hash)
        incident_groups.setdefault(group_key, set()).add(sha256_canonical_json(semantic_payload))
    incident_total = len(incident_groups)
    incident_passed = sum(1 for hashes in incident_groups.values() if len(hashes) == 1)
    policy_incident_reproducibility_pct = _pct(incident_passed, incident_total)

    child_stream_total = 0
    child_stream_passed = 0
    failure_sequence_total = 0
    failure_sequence_passed = 0
    for stream_path, events in parsed_event_streams:
        original_lines = stream_path.read_text(encoding="utf-8", errors="replace").splitlines()
        replay_first = replay_events(stream_path)
        replay_second = replay_events(stream_path)
        if any(event.event in _CHILD_LIFECYCLE_EVENTS for event in events):
            child_stream_total += 1
            if replay_first == replay_second == original_lines:
                child_stream_passed += 1

        original_sequence = _failure_code_sequence(events)
        replay_first_sequence = _failure_code_sequence(
            _parse_replay(replay_first)
        )
        replay_second_sequence = _failure_code_sequence(
            _parse_replay(replay_second)
        )
        failure_sequence_total += 1
        if original_sequence == replay_first_sequence == replay_second_sequence:
            failure_sequence_passed += 1

    child_lifecycle_replay_determinism_pct = _pct(child_stream_passed, child_stream_total)
    runtime_failure_code_stability_pct = _pct(failure_sequence_passed, failure_sequence_total)

    connector_groups: dict[str, set[str]] = {}
    for payload, path in zip(connector_payloads, connector_snapshot_paths):
        if payload.get("schema") != CONNECTOR_SNAPSHOT_SCHEMA:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "connector snapshot input must use connector_snapshot@1",
                    context={"path": str(path)},
                )
            )
            continue
        snapshot_id = payload.get("snapshot_id")
        connectors = payload.get("connectors")
        connector_snapshot_hash = payload.get("connector_snapshot_hash")
        if not isinstance(snapshot_id, str) or not isinstance(connectors, list):
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "connector snapshot input missing required fields",
                    context={"path": str(path)},
                )
            )
            continue
        expected_hash = sha256_canonical_json(connectors)
        if connector_snapshot_hash != expected_hash:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "connector snapshot hash mismatch for connectors payload",
                    context={
                        "path": str(path),
                        "snapshot_id": snapshot_id,
                    },
                )
            )
            continue
        semantic_payload = {
            "provider": payload.get("provider"),
            "capability_snapshot_id": payload.get("capability_snapshot_id"),
            "connector_snapshot_hash": connector_snapshot_hash,
            "connectors": connectors,
        }
        connector_groups.setdefault(snapshot_id, set()).add(sha256_canonical_json(semantic_payload))
    connector_total = len(connector_groups)
    connector_passed = sum(1 for hashes in connector_groups.values() if len(hashes) == 1)
    connector_snapshot_replay_stability_pct = _pct(connector_passed, connector_total)

    validator_packet_groups: dict[str, set[str]] = {}
    validator_packet_replay_counts: dict[str, int] = {}
    witness_groups: dict[str, set[str]] = {}
    witness_replay_counts: dict[str, int] = {}
    for payload, path in zip(validator_packet_payloads, validator_evidence_packet_paths):
        if payload.get("schema") != VALIDATOR_EVIDENCE_PACKET_SCHEMA:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "validator evidence input must use validator_evidence_packet@1",
                    context={"path": str(path)},
                )
            )
            continue

        validator_run_id = payload.get("validator_run_id")
        if not isinstance(validator_run_id, str) or not validator_run_id:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "validator evidence input missing validator_run_id",
                    context={"path": str(path)},
                )
            )
            continue

        expected_packet_hash = _validator_packet_hash(payload)
        actual_packet_hash = payload.get("evidence_packet_hash")
        if not isinstance(actual_packet_hash, str) or actual_packet_hash != expected_packet_hash:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "validator evidence packet hash mismatch",
                    context={"path": str(path)},
                )
            )
            continue

        validator_packet_replay_counts[validator_run_id] = (
            validator_packet_replay_counts.get(validator_run_id, 0) + 1
        )
        witness_replay_counts[validator_run_id] = witness_replay_counts.get(validator_run_id, 0) + 1
        validator_packet_groups.setdefault(validator_run_id, set()).add(expected_packet_hash)
        witness_groups.setdefault(validator_run_id, set()).add(
            _witness_reconstruction_hash(payload)
        )

    for validator_run_id in sorted(validator_packet_replay_counts):
        replay_count = validator_packet_replay_counts[validator_run_id]
        if replay_count != SEMANTICS_DETERMINISM_REPLAY_COUNT:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "validator evidence replay count mismatch",
                    context={
                        "validator_run_id": validator_run_id,
                        "expected_replays": SEMANTICS_DETERMINISM_REPLAY_COUNT,
                        "observed_replays": replay_count,
                    },
                )
            )
    for validator_run_id in sorted(witness_replay_counts):
        replay_count = witness_replay_counts[validator_run_id]
        if replay_count != SEMANTICS_DETERMINISM_REPLAY_COUNT:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "witness replay count mismatch",
                    context={
                        "validator_run_id": validator_run_id,
                        "expected_replays": SEMANTICS_DETERMINISM_REPLAY_COUNT,
                        "observed_replays": replay_count,
                    },
                )
            )

    validator_packet_determinism_pct = _group_replay_determinism_pct(
        replay_groups=validator_packet_groups,
        replay_counts=validator_packet_replay_counts,
    )
    witness_reconstruction_determinism_pct = _group_replay_determinism_pct(
        replay_groups=witness_groups,
        replay_counts=witness_replay_counts,
    )

    semantics_diagnostics_groups: dict[str, set[str]] = {}
    semantics_diagnostics_replay_counts: dict[str, int] = {}
    for payload, path in zip(semantics_diagnostics_payloads, semantics_diagnostics_paths):
        if payload.get("schema") != SEMANTICS_DIAGNOSTICS_SCHEMA:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "semantics diagnostics input must use semantics_diagnostics@1",
                    context={"path": str(path)},
                )
            )
            continue

        artifact_ref = payload.get("artifact_ref")
        if not isinstance(artifact_ref, str) or not artifact_ref:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "semantics diagnostics input missing artifact_ref",
                    context={"path": str(path)},
                )
            )
            continue

        expected_diagnostics_hash = _semantics_diagnostics_hash(payload)
        actual_diagnostics_hash = payload.get("semantics_diagnostics_hash")
        if not isinstance(actual_diagnostics_hash, str) or (
            actual_diagnostics_hash != expected_diagnostics_hash
        ):
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "semantics diagnostics hash mismatch",
                    context={"path": str(path)},
                )
            )
            continue

        semantics_diagnostics_replay_counts[artifact_ref] = (
            semantics_diagnostics_replay_counts.get(artifact_ref, 0) + 1
        )
        semantics_diagnostics_groups.setdefault(artifact_ref, set()).add(expected_diagnostics_hash)

    for artifact_ref in sorted(semantics_diagnostics_replay_counts):
        replay_count = semantics_diagnostics_replay_counts[artifact_ref]
        if replay_count != SEMANTICS_DETERMINISM_REPLAY_COUNT:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "semantics diagnostics replay count mismatch",
                    context={
                        "artifact_ref": artifact_ref,
                        "expected_replays": SEMANTICS_DETERMINISM_REPLAY_COUNT,
                        "observed_replays": replay_count,
                    },
                )
            )

    semantics_diagnostics_determinism_pct = _group_replay_determinism_pct(
        replay_groups=semantics_diagnostics_groups,
        replay_counts=semantics_diagnostics_replay_counts,
    )
    vnext_plus7_metrics = _compute_vnext_plus7_metrics(
        manifest_path=vnext_plus7_manifest_path,
        issues=issues,
    )
    vnext_plus8_metrics = _compute_vnext_plus8_metrics(
        manifest_path=vnext_plus8_manifest_path,
        issues=issues,
    )
    vnext_plus9_metrics = _compute_vnext_plus9_metrics(
        manifest_path=vnext_plus9_manifest_path,
        issues=issues,
    )
    vnext_plus10_metrics = _compute_vnext_plus10_metrics(
        manifest_path=vnext_plus10_manifest_path,
        issues=issues,
    )
    vnext_plus11_metrics = _compute_vnext_plus11_metrics(
        manifest_path=vnext_plus11_manifest_path,
        issues=issues,
    )
    vnext_plus13_metrics = _compute_vnext_plus13_metrics(
        manifest_path=vnext_plus13_manifest_path,
        issues=issues,
    )

    quality_current_metrics = quality_current.get("metrics")
    quality_baseline_metrics = quality_baseline.get("metrics")
    if not isinstance(quality_current_metrics, dict) or not isinstance(
        quality_baseline_metrics, dict
    ):
        issues.append(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "quality dashboard payload missing metrics object",
            )
        )
        quality_deltas: dict[str, float] = {}
        quality_metric_rules: dict[str, str] = {}
        quality_metric_ruleset = "unresolved"
        quality_delta_non_negative = False
    else:
        quality_metric_rules, quality_metric_ruleset = _resolve_quality_metric_rules(
            current_metrics=quality_current_metrics,
            baseline_metrics=quality_baseline_metrics,
        )
        quality_deltas = {}
        quality_checks: list[bool] = []
        if quality_metric_rules is None:
            required_metrics = sorted(
                FROZEN_QUALITY_METRIC_RULES.keys() | LEGACY_QUALITY_METRIC_RULES.keys()
            )
            missing_metrics = [
                metric_name
                for metric_name in required_metrics
                if metric_name not in quality_current_metrics
                or metric_name not in quality_baseline_metrics
            ]
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "quality dashboard payload is missing required metrics for delta comparison",
                    context={"missing_metrics": missing_metrics},
                )
            )
            quality_metric_rules = {}
            quality_delta_non_negative = False
        else:
            for metric_name, rule in quality_metric_rules.items():
                current_value = quality_current_metrics.get(metric_name)
                baseline_value = quality_baseline_metrics.get(metric_name)
                if not isinstance(current_value, (int, float)) or not isinstance(
                    baseline_value, (int, float)
                ):
                    issues.append(
                        _issue(
                            "URM_STOP_GATE_INPUT_INVALID",
                            "quality dashboard metric is missing or non-numeric",
                            context={"metric": metric_name},
                        )
                    )
                    continue
                delta = round(float(current_value) - float(baseline_value), 6)
                quality_deltas[metric_name] = delta
                quality_checks.append(
                    _metric_delta_satisfies_rule(rule=rule, delta=delta)
                )
            quality_delta_non_negative = bool(quality_checks) and all(quality_checks)

    metrics = {
        "policy_incident_reproducibility_pct": policy_incident_reproducibility_pct,
        "child_lifecycle_replay_determinism_pct": child_lifecycle_replay_determinism_pct,
        "runtime_failure_code_stability_pct": runtime_failure_code_stability_pct,
        "connector_snapshot_replay_stability_pct": connector_snapshot_replay_stability_pct,
        "validator_packet_determinism_pct": validator_packet_determinism_pct,
        "witness_reconstruction_determinism_pct": witness_reconstruction_determinism_pct,
        "semantics_diagnostics_determinism_pct": semantics_diagnostics_determinism_pct,
        "quality_metric_ruleset": quality_metric_ruleset,
        "quality_delta_non_negative": quality_delta_non_negative,
        "quality_deltas": {key: quality_deltas[key] for key in sorted(quality_deltas)},
        "quality_delta_rules": {
            key: quality_metric_rules[key] for key in sorted(quality_metric_rules)
        },
        "policy_lint_determinism_pct": vnext_plus7_metrics["policy_lint_determinism_pct"],
        "proof_replay_determinism_pct": vnext_plus7_metrics["proof_replay_determinism_pct"],
        "policy_proof_packet_hash_stability_pct": vnext_plus7_metrics[
            "policy_proof_packet_hash_stability_pct"
        ],
        "explain_diff_determinism_pct": vnext_plus8_metrics["explain_diff_determinism_pct"],
        "explain_api_cli_parity_pct": vnext_plus8_metrics["explain_api_cli_parity_pct"],
        "explain_hash_stability_pct": vnext_plus8_metrics["explain_hash_stability_pct"],
        "scheduler_dispatch_replay_determinism_pct": vnext_plus9_metrics[
            "scheduler_dispatch_replay_determinism_pct"
        ],
        "orphan_lease_recovery_determinism_pct": vnext_plus9_metrics[
            "orphan_lease_recovery_determinism_pct"
        ],
        "concurrent_budget_cancel_stability_pct": vnext_plus9_metrics[
            "concurrent_budget_cancel_stability_pct"
        ],
        "concept_conflict_precision_pct": vnext_plus10_metrics[
            "concept_conflict_precision_pct"
        ],
        "concept_conflict_recall_pct": vnext_plus10_metrics["concept_conflict_recall_pct"],
        "coherence_permutation_stability_pct": vnext_plus10_metrics[
            "coherence_permutation_stability_pct"
        ],
        # Non-gating diagnostics: rendered in reports, excluded from gates.
        "concept_conflict_precision_macro_pct": vnext_plus10_metrics[
            "concept_conflict_precision_macro_pct"
        ],
        "concept_conflict_recall_macro_pct": vnext_plus10_metrics[
            "concept_conflict_recall_macro_pct"
        ],
        "baseline_concept_conflict_precision_pct": vnext_plus10_metrics[
            "baseline_concept_conflict_precision_pct"
        ],
        "baseline_concept_conflict_recall_pct": vnext_plus10_metrics[
            "baseline_concept_conflict_recall_pct"
        ],
        "concept_conflict_precision_delta_pct": vnext_plus10_metrics[
            "concept_conflict_precision_delta_pct"
        ],
        "concept_conflict_recall_delta_pct": vnext_plus10_metrics[
            "concept_conflict_recall_delta_pct"
        ],
        "plateau_epsilon_pct": vnext_plus10_metrics["plateau_epsilon_pct"],
        "precision_non_regression": vnext_plus10_metrics["precision_non_regression"],
        "recall_non_regression": vnext_plus10_metrics["recall_non_regression"],
        "strict_improvement_required": vnext_plus10_metrics["strict_improvement_required"],
        "strict_improvement_met": vnext_plus10_metrics["strict_improvement_met"],
        "plateau_eligible": vnext_plus10_metrics["plateau_eligible"],
        "semantic_depth_improvement_lock_passed": vnext_plus10_metrics[
            "semantic_depth_improvement_lock_passed"
        ],
        "precision_fixture_count": vnext_plus10_metrics["precision_fixture_count"],
        "precision_fixture_count_evaluated": vnext_plus10_metrics[
            "precision_fixture_count_evaluated"
        ],
        "recall_fixture_count": vnext_plus10_metrics["recall_fixture_count"],
        "recall_fixture_count_evaluated": vnext_plus10_metrics[
            "recall_fixture_count_evaluated"
        ],
        "domain_conformance_replay_determinism_pct": vnext_plus11_metrics[
            "domain_conformance_replay_determinism_pct"
        ],
        "cross_domain_artifact_parity_pct": vnext_plus11_metrics[
            "cross_domain_artifact_parity_pct"
        ],
        "runtime_domain_coupling_guard_pct": vnext_plus11_metrics[
            "runtime_domain_coupling_guard_pct"
        ],
        "adeu_core_ir_replay_determinism_pct": vnext_plus13_metrics[
            "adeu_core_ir_replay_determinism_pct"
        ],
        "adeu_claim_ledger_recompute_match_pct": vnext_plus13_metrics[
            "adeu_claim_ledger_recompute_match_pct"
        ],
        "adeu_lane_projection_determinism_pct": vnext_plus13_metrics[
            "adeu_lane_projection_determinism_pct"
        ],
    }
    gates = {
        "policy_incident_reproducibility": metrics["policy_incident_reproducibility_pct"]
        >= THRESHOLDS["policy_incident_reproducibility_pct"],
        "child_lifecycle_replay_determinism": metrics["child_lifecycle_replay_determinism_pct"]
        >= THRESHOLDS["child_lifecycle_replay_determinism_pct"],
        "runtime_failure_code_stability": metrics["runtime_failure_code_stability_pct"]
        >= THRESHOLDS["runtime_failure_code_stability_pct"],
        "connector_snapshot_replay_stability": metrics["connector_snapshot_replay_stability_pct"]
        >= THRESHOLDS["connector_snapshot_replay_stability_pct"],
        "validator_packet_determinism": metrics["validator_packet_determinism_pct"]
        >= THRESHOLDS["validator_packet_determinism_pct"],
        "witness_reconstruction_determinism": metrics["witness_reconstruction_determinism_pct"]
        >= THRESHOLDS["witness_reconstruction_determinism_pct"],
        "semantics_diagnostics_determinism": metrics["semantics_diagnostics_determinism_pct"]
        >= THRESHOLDS["semantics_diagnostics_determinism_pct"],
        "policy_lint_determinism": metrics["policy_lint_determinism_pct"]
        >= THRESHOLDS["policy_lint_determinism_pct"],
        "proof_replay_determinism": metrics["proof_replay_determinism_pct"]
        >= THRESHOLDS["proof_replay_determinism_pct"],
        "policy_proof_packet_hash_stability": metrics["policy_proof_packet_hash_stability_pct"]
        >= THRESHOLDS["policy_proof_packet_hash_stability_pct"],
        "explain_diff_determinism": metrics["explain_diff_determinism_pct"]
        >= THRESHOLDS["explain_diff_determinism_pct"],
        "explain_api_cli_parity": metrics["explain_api_cli_parity_pct"]
        >= THRESHOLDS["explain_api_cli_parity_pct"],
        "explain_hash_stability": metrics["explain_hash_stability_pct"]
        >= THRESHOLDS["explain_hash_stability_pct"],
        "scheduler_dispatch_replay_determinism": metrics[
            "scheduler_dispatch_replay_determinism_pct"
        ]
        >= THRESHOLDS["scheduler_dispatch_replay_determinism_pct"],
        "orphan_lease_recovery_determinism": metrics["orphan_lease_recovery_determinism_pct"]
        >= THRESHOLDS["orphan_lease_recovery_determinism_pct"],
        "concurrent_budget_cancel_stability": metrics["concurrent_budget_cancel_stability_pct"]
        >= THRESHOLDS["concurrent_budget_cancel_stability_pct"],
        "concept_conflict_precision": metrics["concept_conflict_precision_pct"]
        >= THRESHOLDS["concept_conflict_precision_pct"],
        "concept_conflict_recall": metrics["concept_conflict_recall_pct"]
        >= THRESHOLDS["concept_conflict_recall_pct"],
        "coherence_permutation_stability": metrics["coherence_permutation_stability_pct"]
        >= THRESHOLDS["coherence_permutation_stability_pct"],
        "semantic_depth_improvement_lock": metrics["semantic_depth_improvement_lock_passed"]
        is THRESHOLDS["semantic_depth_improvement_lock"],
        # Macro precision/recall are intentionally not part of stop-gate decisions.
        "domain_conformance_replay_determinism": metrics[
            "domain_conformance_replay_determinism_pct"
        ]
        >= THRESHOLDS["domain_conformance_replay_determinism_pct"],
        "cross_domain_artifact_parity": metrics["cross_domain_artifact_parity_pct"]
        >= THRESHOLDS["cross_domain_artifact_parity_pct"],
        "runtime_domain_coupling_guard": metrics["runtime_domain_coupling_guard_pct"]
        >= THRESHOLDS["runtime_domain_coupling_guard_pct"],
        "adeu_core_ir_replay_determinism": metrics["adeu_core_ir_replay_determinism_pct"]
        >= THRESHOLDS["adeu_core_ir_replay_determinism_pct"],
        "adeu_claim_ledger_recompute_match": metrics["adeu_claim_ledger_recompute_match_pct"]
        >= THRESHOLDS["adeu_claim_ledger_recompute_match_pct"],
        "adeu_lane_projection_determinism": metrics["adeu_lane_projection_determinism_pct"]
        >= THRESHOLDS["adeu_lane_projection_determinism_pct"],
        "quality_delta_non_negative": metrics["quality_delta_non_negative"]
        is THRESHOLDS["quality_delta_non_negative"],
    }

    return {
        "schema": STOP_GATE_SCHEMA,
        "valid": len(issues) == 0,
        "inputs": {
            "incident_packet_paths": [str(path) for path in sorted(incident_packet_paths)],
            "event_stream_paths": [str(path) for path in sorted(event_stream_paths)],
            "connector_snapshot_paths": [str(path) for path in sorted(connector_snapshot_paths)],
            "validator_evidence_packet_paths": [
                str(path) for path in sorted(validator_evidence_packet_paths)
            ],
            "semantics_diagnostics_paths": [
                str(path) for path in sorted(semantics_diagnostics_paths)
            ],
            "quality_current_path": str(quality_current_path),
            "quality_baseline_path": str(
                quality_baseline_path if quality_baseline_path is not None else quality_current_path
            ),
            "vnext_plus7_manifest_path": str(
                vnext_plus7_manifest_path
                if vnext_plus7_manifest_path is not None
                else VNEXT_PLUS7_MANIFEST_PATH
            ),
            "vnext_plus8_manifest_path": str(
                vnext_plus8_manifest_path
                if vnext_plus8_manifest_path is not None
                else VNEXT_PLUS8_MANIFEST_PATH
            ),
            "vnext_plus9_manifest_path": str(
                vnext_plus9_manifest_path
                if vnext_plus9_manifest_path is not None
                else VNEXT_PLUS9_MANIFEST_PATH
            ),
            "vnext_plus10_manifest_path": str(
                vnext_plus10_manifest_path
                if vnext_plus10_manifest_path is not None
                else VNEXT_PLUS10_MANIFEST_PATH
            ),
            "vnext_plus11_manifest_path": str(
                vnext_plus11_manifest_path
                if vnext_plus11_manifest_path is not None
                else VNEXT_PLUS11_MANIFEST_PATH
            ),
            "vnext_plus13_manifest_path": str(
                vnext_plus13_manifest_path
                if vnext_plus13_manifest_path is not None
                else VNEXT_PLUS13_MANIFEST_PATH
            ),
        },
        "vnext_plus8_manifest_hash": vnext_plus8_metrics["vnext_plus8_manifest_hash"],
        "vnext_plus9_manifest_hash": vnext_plus9_metrics["vnext_plus9_manifest_hash"],
        "vnext_plus10_manifest_hash": vnext_plus10_metrics["vnext_plus10_manifest_hash"],
        "vnext_plus11_manifest_hash": vnext_plus11_metrics["vnext_plus11_manifest_hash"],
        "vnext_plus13_manifest_hash": vnext_plus13_metrics["vnext_plus13_manifest_hash"],
        "thresholds": THRESHOLDS,
        "metrics": metrics,
        "gates": gates,
        "all_passed": all(gates.values()),
        "issues": sorted(
            issues,
            key=lambda issue: (
                str(issue.get("code", "")),
                str(issue.get("message", "")),
                canonical_json(issue.get("context", {})),
            ),
        ),
    }


def stop_gate_markdown(report: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Stop-Gate Metrics")
    lines.append("")
    lines.append(f"- Schema: `{report.get('schema')}`")
    lines.append(f"- Valid: `{report.get('valid')}`")
    lines.append(f"- All Passed: `{report.get('all_passed')}`")
    lines.append(f"- vnext+8 manifest hash: `{report.get('vnext_plus8_manifest_hash')}`")
    lines.append(f"- vnext+9 manifest hash: `{report.get('vnext_plus9_manifest_hash')}`")
    lines.append(f"- vnext+10 manifest hash: `{report.get('vnext_plus10_manifest_hash')}`")
    lines.append(f"- vnext+11 manifest hash: `{report.get('vnext_plus11_manifest_hash')}`")
    lines.append(f"- vnext+13 manifest hash: `{report.get('vnext_plus13_manifest_hash')}`")
    lines.append("")
    lines.append("## Metrics")
    lines.append("")
    metrics = report.get("metrics", {})
    lines.append(
        "- policy incident reproducibility pct: "
        f"`{metrics.get('policy_incident_reproducibility_pct')}`"
    )
    lines.append(
        "- child lifecycle replay determinism pct: "
        f"`{metrics.get('child_lifecycle_replay_determinism_pct')}`"
    )
    lines.append(
        "- runtime failure-code stability pct: "
        f"`{metrics.get('runtime_failure_code_stability_pct')}`"
    )
    lines.append(
        "- connector snapshot replay stability pct: "
        f"`{metrics.get('connector_snapshot_replay_stability_pct')}`"
    )
    lines.append(
        "- validator packet determinism pct: "
        f"`{metrics.get('validator_packet_determinism_pct')}`"
    )
    lines.append(
        "- witness reconstruction determinism pct: "
        f"`{metrics.get('witness_reconstruction_determinism_pct')}`"
    )
    lines.append(
        "- semantics diagnostics determinism pct: "
        f"`{metrics.get('semantics_diagnostics_determinism_pct')}`"
    )
    lines.append(
        "- policy lint determinism pct: "
        f"`{metrics.get('policy_lint_determinism_pct')}`"
    )
    lines.append(
        "- proof replay determinism pct: "
        f"`{metrics.get('proof_replay_determinism_pct')}`"
    )
    lines.append(
        "- policy/proof packet hash stability pct: "
        f"`{metrics.get('policy_proof_packet_hash_stability_pct')}`"
    )
    lines.append(
        "- explain diff determinism pct: "
        f"`{metrics.get('explain_diff_determinism_pct')}`"
    )
    lines.append(
        "- explain api/cli parity pct: "
        f"`{metrics.get('explain_api_cli_parity_pct')}`"
    )
    lines.append(
        "- explain hash stability pct: "
        f"`{metrics.get('explain_hash_stability_pct')}`"
    )
    lines.append(
        "- scheduler dispatch replay determinism pct: "
        f"`{metrics.get('scheduler_dispatch_replay_determinism_pct')}`"
    )
    lines.append(
        "- orphan lease recovery determinism pct: "
        f"`{metrics.get('orphan_lease_recovery_determinism_pct')}`"
    )
    lines.append(
        "- concurrent budget/cancel stability pct: "
        f"`{metrics.get('concurrent_budget_cancel_stability_pct')}`"
    )
    lines.append(
        "- concept conflict precision pct: "
        f"`{metrics.get('concept_conflict_precision_pct')}`"
    )
    lines.append(
        "- concept conflict recall pct: "
        f"`{metrics.get('concept_conflict_recall_pct')}`"
    )
    lines.append(
        "- coherence permutation stability pct: "
        f"`{metrics.get('coherence_permutation_stability_pct')}`"
    )
    lines.append(
        "- concept conflict precision macro pct (non-gating): "
        f"`{metrics.get('concept_conflict_precision_macro_pct')}`"
    )
    lines.append(
        "- concept conflict recall macro pct (non-gating): "
        f"`{metrics.get('concept_conflict_recall_macro_pct')}`"
    )
    lines.append(
        "- baseline concept conflict precision pct: "
        f"`{metrics.get('baseline_concept_conflict_precision_pct')}`"
    )
    lines.append(
        "- baseline concept conflict recall pct: "
        f"`{metrics.get('baseline_concept_conflict_recall_pct')}`"
    )
    lines.append(
        "- concept conflict precision delta pct: "
        f"`{metrics.get('concept_conflict_precision_delta_pct')}`"
    )
    lines.append(
        "- concept conflict recall delta pct: "
        f"`{metrics.get('concept_conflict_recall_delta_pct')}`"
    )
    lines.append(
        "- semantic-depth plateau epsilon pct: "
        f"`{metrics.get('plateau_epsilon_pct')}`"
    )
    lines.append(
        "- semantic-depth strict improvement required: "
        f"`{metrics.get('strict_improvement_required')}`"
    )
    lines.append(
        "- semantic-depth strict improvement met: "
        f"`{metrics.get('strict_improvement_met')}`"
    )
    lines.append(
        "- semantic-depth plateau eligible: "
        f"`{metrics.get('plateau_eligible')}`"
    )
    lines.append(
        "- semantic-depth improvement lock passed: "
        f"`{metrics.get('semantic_depth_improvement_lock_passed')}`"
    )
    lines.append(
        "- domain conformance replay determinism pct: "
        f"`{metrics.get('domain_conformance_replay_determinism_pct')}`"
    )
    lines.append(
        "- cross-domain artifact parity pct: "
        f"`{metrics.get('cross_domain_artifact_parity_pct')}`"
    )
    lines.append(
        "- runtime domain coupling guard pct: "
        f"`{metrics.get('runtime_domain_coupling_guard_pct')}`"
    )
    lines.append(
        "- adeu core IR replay determinism pct: "
        f"`{metrics.get('adeu_core_ir_replay_determinism_pct')}`"
    )
    lines.append(
        "- adeu claim ledger recompute match pct: "
        f"`{metrics.get('adeu_claim_ledger_recompute_match_pct')}`"
    )
    lines.append(
        "- adeu lane projection determinism pct: "
        f"`{metrics.get('adeu_lane_projection_determinism_pct')}`"
    )
    lines.append(
        "- quality delta non-negative: "
        f"`{metrics.get('quality_delta_non_negative')}`"
    )
    lines.append(
        "- quality metric ruleset: "
        f"`{metrics.get('quality_metric_ruleset')}`"
    )
    quality_delta_rules = metrics.get("quality_delta_rules", {})
    if isinstance(quality_delta_rules, dict):
        for metric_name in sorted(quality_delta_rules):
            lines.append(
                f"- quality delta rule `{metric_name}`: `{quality_delta_rules[metric_name]}`"
            )
    quality_deltas = metrics.get("quality_deltas", {})
    if isinstance(quality_deltas, dict):
        for metric_name in sorted(quality_deltas):
            lines.append(f"- quality delta `{metric_name}`: `{quality_deltas[metric_name]}`")
    lines.append("")
    lines.append("## Gates")
    lines.append("")
    gates = report.get("gates", {})
    if isinstance(gates, dict):
        for gate_name in sorted(gates):
            lines.append(f"- `{gate_name}`: `{gates[gate_name]}`")
    lines.append("")
    issues = report.get("issues", [])
    if isinstance(issues, list) and issues:
        lines.append("## Issues")
        lines.append("")
        for issue in issues:
            if not isinstance(issue, dict):
                continue
            lines.append(
                f"- `{issue.get('code')}`: {issue.get('message')} "
                f"({canonical_json(issue.get('context', {}))})"
            )
        lines.append("")
    return "\n".join(lines)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="stop-gate",
        description="Build deterministic stop-gate metrics from persisted evidence artifacts.",
    )
    parser.add_argument(
        "--incident-packet",
        dest="incident_packet_paths",
        action="append",
        type=Path,
    )
    parser.add_argument("--event-stream", dest="event_stream_paths", action="append", type=Path)
    parser.add_argument(
        "--connector-snapshot",
        dest="connector_snapshot_paths",
        action="append",
        type=Path,
    )
    parser.add_argument(
        "--validator-evidence-packet",
        dest="validator_evidence_packet_paths",
        action="append",
        type=Path,
    )
    parser.add_argument(
        "--semantics-diagnostics",
        dest="semantics_diagnostics_paths",
        action="append",
        type=Path,
    )
    parser.add_argument("--quality-current", dest="quality_current_path", type=Path, required=True)
    parser.add_argument("--quality-baseline", dest="quality_baseline_path", type=Path)
    parser.add_argument(
        "--vnext-plus7-manifest",
        dest="vnext_plus7_manifest_path",
        type=Path,
        default=VNEXT_PLUS7_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus8-manifest",
        dest="vnext_plus8_manifest_path",
        type=Path,
        default=VNEXT_PLUS8_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus9-manifest",
        dest="vnext_plus9_manifest_path",
        type=Path,
        default=VNEXT_PLUS9_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus10-manifest",
        dest="vnext_plus10_manifest_path",
        type=Path,
        default=VNEXT_PLUS10_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus11-manifest",
        dest="vnext_plus11_manifest_path",
        type=Path,
        default=VNEXT_PLUS11_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus13-manifest",
        dest="vnext_plus13_manifest_path",
        type=Path,
        default=VNEXT_PLUS13_MANIFEST_PATH,
    )
    parser.add_argument("--out-json", dest="out_json_path", type=Path)
    parser.add_argument("--out-md", dest="out_md_path", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    report = build_stop_gate_metrics(
        incident_packet_paths=list(args.incident_packet_paths or []),
        event_stream_paths=list(args.event_stream_paths or []),
        connector_snapshot_paths=list(args.connector_snapshot_paths or []),
        validator_evidence_packet_paths=list(args.validator_evidence_packet_paths or []),
        semantics_diagnostics_paths=list(args.semantics_diagnostics_paths or []),
        quality_current_path=args.quality_current_path,
        quality_baseline_path=args.quality_baseline_path,
        vnext_plus7_manifest_path=args.vnext_plus7_manifest_path,
        vnext_plus8_manifest_path=args.vnext_plus8_manifest_path,
        vnext_plus9_manifest_path=args.vnext_plus9_manifest_path,
        vnext_plus10_manifest_path=args.vnext_plus10_manifest_path,
        vnext_plus11_manifest_path=args.vnext_plus11_manifest_path,
        vnext_plus13_manifest_path=args.vnext_plus13_manifest_path,
    )
    payload = canonical_json(report)
    if args.out_json_path is not None:
        _write_text(args.out_json_path, payload + "\n")
    else:
        print(payload)
    if args.out_md_path is not None:
        _write_text(args.out_md_path, stop_gate_markdown(report))
    return 0 if report.get("valid") else 1


if __name__ == "__main__":
    raise SystemExit(main())
