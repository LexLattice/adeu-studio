from __future__ import annotations

import argparse
import json
import time
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any, cast

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
ADEU_LANE_REPORT_SCHEMA = "adeu_lane_report@0.1"
ADEU_PROJECTION_ALIGNMENT_SCHEMA = "adeu_projection_alignment@0.1"
ADEU_INTEGRITY_DANGLING_REFERENCE_SCHEMA = "adeu_integrity_dangling_reference@0.1"
ADEU_INTEGRITY_CYCLE_POLICY_SCHEMA = "adeu_integrity_cycle_policy@0.1"
ADEU_INTEGRITY_DEONTIC_CONFLICT_SCHEMA = "adeu_integrity_deontic_conflict@0.1"
ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_SCHEMA = (
    "adeu_integrity_reference_integrity_extended@0.1"
)
ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_SCHEMA = "adeu_integrity_cycle_policy_extended@0.1"
ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_SCHEMA = (
    "adeu_integrity_deontic_conflict_extended@0.1"
)
VNEXT_PLUS13_REPLAY_COUNT = 3
VNEXT_PLUS13_MANIFEST_SCHEMA = "stop_gate.vnext_plus13_manifest@1"
VNEXT_PLUS13_DEFAULT_METRICS = {
    "adeu_core_ir_replay_determinism_pct": 0.0,
    "adeu_claim_ledger_recompute_match_pct": 0.0,
    "adeu_lane_projection_determinism_pct": 0.0,
}
VNEXT_PLUS14_REPLAY_COUNT = 3
VNEXT_PLUS14_MANIFEST_SCHEMA = "stop_gate.vnext_plus14_manifest@1"
PROVIDER_PARITY_FIXTURE_SCHEMA = "provider_parity_fixture@1"
VNEXT_PLUS14_DEFAULT_METRICS = {
    "provider_route_contract_parity_pct": 0.0,
    "codex_candidate_contract_valid_pct": 0.0,
    "provider_parity_replay_determinism_pct": 0.0,
}
VNEXT_PLUS15_REPLAY_COUNT = 3
VNEXT_PLUS15_MANIFEST_SCHEMA = "stop_gate.vnext_plus15_manifest@1"
VNEXT_PLUS15_DEFAULT_METRICS = {
    "adeu_lane_report_replay_determinism_pct": 0.0,
    "adeu_projection_alignment_determinism_pct": 0.0,
    "adeu_depth_report_replay_determinism_pct": 0.0,
}
VNEXT_PLUS16_REPLAY_COUNT = 3
VNEXT_PLUS16_MANIFEST_SCHEMA = "stop_gate.vnext_plus16_manifest@1"
VNEXT_PLUS16_DEFAULT_METRICS = {
    "artifact_dangling_reference_determinism_pct": 0.0,
    "artifact_cycle_policy_determinism_pct": 0.0,
    "artifact_deontic_conflict_determinism_pct": 0.0,
}
VNEXT_PLUS17_REPLAY_COUNT = 3
VNEXT_PLUS17_MANIFEST_SCHEMA = "stop_gate.vnext_plus17_manifest@1"
VNEXT_PLUS17_DEFAULT_METRICS = {
    "artifact_reference_integrity_extended_determinism_pct": 0.0,
    "artifact_cycle_policy_extended_determinism_pct": 0.0,
    "artifact_deontic_conflict_extended_determinism_pct": 0.0,
}
VNEXT_PLUS18_REPLAY_COUNT = 3
VNEXT_PLUS18_MANIFEST_SCHEMA = "stop_gate.vnext_plus18_manifest@1"
VNEXT_PLUS18_DEFAULT_METRICS = {
    "artifact_validation_consolidation_parity_pct": 0.0,
    "artifact_transfer_report_consolidation_parity_pct": 0.0,
}
VNEXT_PLUS18_CI_BUDGET_CEILING_MS = 120000
VNEXT_PLUS18_CI_BUDGET_METRIC_KEY = "artifact_stop_gate_ci_budget_within_ceiling_pct"
VNEXT_PLUS18_CI_BUDGET_GATE_KEY = "artifact_stop_gate_ci_budget_within_ceiling"
VNEXT_PLUS19_REPLAY_COUNT = 3
VNEXT_PLUS19_MANIFEST_SCHEMA = "stop_gate.vnext_plus19_manifest@1"
VNEXT_PLUS19_DEFAULT_METRICS = {
    "artifact_core_ir_read_surface_determinism_pct": 0.0,
    "artifact_lane_read_surface_determinism_pct": 0.0,
    "artifact_integrity_read_surface_determinism_pct": 0.0,
}
_READ_SURFACE_LANE_CAPTURE_SCHEMA = "adeu_lane_read_surface_capture@0.1"
_READ_SURFACE_INTEGRITY_CAPTURE_SCHEMA = "adeu_integrity_read_surface_capture@0.1"
_FROZEN_READ_SURFACE_INTEGRITY_FAMILIES: tuple[str, ...] = (
    "dangling_reference",
    "cycle_policy",
    "deontic_conflict",
    "reference_integrity_extended",
    "cycle_policy_extended",
    "deontic_conflict_extended",
)
_READ_SURFACE_INTEGRITY_FAMILY_TO_SCHEMA: dict[str, str] = {
    "dangling_reference": ADEU_INTEGRITY_DANGLING_REFERENCE_SCHEMA,
    "cycle_policy": ADEU_INTEGRITY_CYCLE_POLICY_SCHEMA,
    "deontic_conflict": ADEU_INTEGRITY_DEONTIC_CONFLICT_SCHEMA,
    "reference_integrity_extended": ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_SCHEMA,
    "cycle_policy_extended": ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_SCHEMA,
    "deontic_conflict_extended": ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_SCHEMA,
}
_FROZEN_PROVIDER_KINDS: tuple[str, ...] = ("mock", "openai", "codex")
_FROZEN_PROVIDER_KIND_SET = frozenset(_FROZEN_PROVIDER_KINDS)
_FROZEN_DEPTH_SURFACES: tuple[str, ...] = (
    "adeu.core_ir.lane_report",
    "adeu.core_ir.projection_alignment",
    "adeu.core_ir.depth_report",
)
_FROZEN_DEPTH_SURFACE_SET = frozenset(_FROZEN_DEPTH_SURFACES)
_FROZEN_INTEGRITY_SURFACES: tuple[str, ...] = (
    "adeu.integrity.dangling_reference",
    "adeu.integrity.cycle_policy",
    "adeu.integrity.deontic_conflict",
)
_FROZEN_INTEGRITY_SURFACE_SET = frozenset(_FROZEN_INTEGRITY_SURFACES)
_FROZEN_INTEGRITY_EXTENDED_SURFACES: tuple[str, ...] = (
    "adeu.integrity.reference_integrity_extended",
    "adeu.integrity.cycle_policy_extended",
    "adeu.integrity.deontic_conflict_extended",
)
_FROZEN_INTEGRITY_EXTENDED_SURFACE_SET = frozenset(_FROZEN_INTEGRITY_EXTENDED_SURFACES)
_FROZEN_TOOLING_SURFACES: tuple[str, ...] = (
    "adeu.tooling.validation_parity",
    "adeu.tooling.transfer_report_parity",
    "adeu.tooling.ci_budget",
)
_FROZEN_TOOLING_SURFACE_SET = frozenset(_FROZEN_TOOLING_SURFACES)
_FROZEN_READ_SURFACE_SURFACES: tuple[str, ...] = (
    "adeu.read_surface.core_ir",
    "adeu.read_surface.lane",
    "adeu.read_surface.integrity",
)
_FROZEN_READ_SURFACE_SURFACE_SET = frozenset(_FROZEN_READ_SURFACE_SURFACES)
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
    "provider_route_contract_parity_pct": 100.0,
    "codex_candidate_contract_valid_pct": 100.0,
    "provider_parity_replay_determinism_pct": 100.0,
    "adeu_lane_report_replay_determinism_pct": 100.0,
    "adeu_projection_alignment_determinism_pct": 100.0,
    "adeu_depth_report_replay_determinism_pct": 100.0,
    "artifact_dangling_reference_determinism_pct": 100.0,
    "artifact_cycle_policy_determinism_pct": 100.0,
    "artifact_deontic_conflict_determinism_pct": 100.0,
    "artifact_reference_integrity_extended_determinism_pct": 100.0,
    "artifact_cycle_policy_extended_determinism_pct": 100.0,
    "artifact_deontic_conflict_extended_determinism_pct": 100.0,
    "artifact_validation_consolidation_parity_pct": 100.0,
    "artifact_transfer_report_consolidation_parity_pct": 100.0,
    "artifact_stop_gate_ci_budget_within_ceiling_pct": 100.0,
    "artifact_core_ir_read_surface_determinism_pct": 100.0,
    "artifact_lane_read_surface_determinism_pct": 100.0,
    "artifact_integrity_read_surface_determinism_pct": 100.0,
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


def _default_vnext_plus14_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus14_manifest.json")


def _default_vnext_plus15_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus15_manifest.json")


def _default_vnext_plus16_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus16_manifest.json")


def _default_vnext_plus17_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus17_manifest.json")


def _default_vnext_plus18_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus18_manifest.json")


def _default_vnext_plus19_manifest_path() -> Path:
    return _default_manifest_path("vnext_plus19_manifest.json")


VNEXT_PLUS7_MANIFEST_PATH = _default_vnext_plus7_manifest_path()
VNEXT_PLUS8_MANIFEST_PATH = _default_vnext_plus8_manifest_path()
VNEXT_PLUS9_MANIFEST_PATH = _default_vnext_plus9_manifest_path()
VNEXT_PLUS10_MANIFEST_PATH = _default_vnext_plus10_manifest_path()
VNEXT_PLUS11_MANIFEST_PATH = _default_vnext_plus11_manifest_path()
VNEXT_PLUS13_MANIFEST_PATH = _default_vnext_plus13_manifest_path()
VNEXT_PLUS14_MANIFEST_PATH = _default_vnext_plus14_manifest_path()
VNEXT_PLUS15_MANIFEST_PATH = _default_vnext_plus15_manifest_path()
VNEXT_PLUS16_MANIFEST_PATH = _default_vnext_plus16_manifest_path()
VNEXT_PLUS17_MANIFEST_PATH = _default_vnext_plus17_manifest_path()
VNEXT_PLUS18_MANIFEST_PATH = _default_vnext_plus18_manifest_path()
VNEXT_PLUS19_MANIFEST_PATH = _default_vnext_plus19_manifest_path()


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
_INVALID_LAYER_SORT_ORDER = 99
_S_MILLI_EVIDENCE_WEIGHT = 500
_S_MILLI_DEPENDENCY_WEIGHT = 300
_S_MILLI_PROVENANCE_WEIGHT = 200
_S_MILLI_ROUNDING_BIAS = 500


def _core_ir_node_sort_key(node: Mapping[str, Any]) -> tuple[int, str, str]:
    raw_layer = node.get("layer")
    layer = raw_layer if isinstance(raw_layer, str) else ""
    raw_kind = node.get("kind")
    kind = raw_kind if isinstance(raw_kind, str) else ""
    raw_id = node.get("id")
    node_id = raw_id if isinstance(raw_id, str) else ""
    return (_ADEU_CORE_LAYER_ORDER.get(layer, _INVALID_LAYER_SORT_ORDER), kind, node_id)


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


def _validate_core_ir_nodes(
    *,
    core_ir_path: Path,
    raw_nodes: Any,
) -> dict[str, Mapping[str, Any]]:
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

        if layer == "E":
            text = node.get("text")
            if not isinstance(text, str) or not text:
                raise ValueError(
                    _issue(
                        "URM_STOP_GATE_INPUT_INVALID",
                        "core IR E-node must include non-empty text",
                        context={"path": str(core_ir_path), "node_id": node_id},
                    )
                )
            if "spans" in node:
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
                        "core IR E-node confidence must be numeric when present",
                        context={"path": str(core_ir_path), "node_id": node_id},
                    )
                )
        else:
            label = node.get("label")
            if not isinstance(label, str) or not label:
                raise ValueError(
                    _issue(
                        "URM_STOP_GATE_INPUT_INVALID",
                        "core IR O/D/U node must include non-empty label",
                        context={"path": str(core_ir_path), "node_id": node_id},
                    )
                )
        if layer == "O" and "aliases" in node:
            aliases = node.get("aliases")
            if not isinstance(aliases, list) or not all(
                isinstance(alias, str) for alias in aliases
            ):
                raise ValueError(
                    _issue(
                        "URM_STOP_GATE_INPUT_INVALID",
                        "core IR O-node aliases must be a string list when present",
                        context={"path": str(core_ir_path), "node_id": node_id},
                    )
                )

        node_index[node_id] = node
        observed_node_order.append(_core_ir_node_sort_key(node))

    if observed_node_order != sorted(observed_node_order):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "core IR fixture nodes must be sorted by (layer, kind, id)",
                context={"path": str(core_ir_path)},
            )
        )
    return node_index


def _validate_core_ir_edges(
    *,
    core_ir_path: Path,
    raw_edges: Any,
    node_index: Mapping[str, Mapping[str, Any]],
) -> None:
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

    node_index = _validate_core_ir_nodes(
        core_ir_path=core_ir_path,
        raw_nodes=payload.get("nodes"),
    )
    _validate_core_ir_edges(
        core_ir_path=core_ir_path,
        raw_edges=payload.get("edges"),
        node_index=node_index,
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
                _S_MILLI_EVIDENCE_WEIGHT * evidence_support_ratio_milli
                + _S_MILLI_DEPENDENCY_WEIGHT * dependency_resolution_ratio_milli
                + _S_MILLI_PROVENANCE_WEIGHT * provenance_anchor_ratio_milli
                + _S_MILLI_ROUNDING_BIAS
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


def _provider_parity_fixture_hash(*, artifact_ref: Path) -> tuple[str, bool]:
    payload = _read_json_object(artifact_ref, description="provider parity fixture")
    if payload.get("schema") != PROVIDER_PARITY_FIXTURE_SCHEMA:
        raise ValueError(
            _issue(
                "URM_PROVIDER_PARITY_FIXTURE_INVALID",
                "provider parity fixture has unsupported schema",
                context={"path": str(artifact_ref), "schema": payload.get("schema")},
            )
        )
    fixture_version = payload.get("fixture_version")
    if not isinstance(fixture_version, str) or not fixture_version:
        raise ValueError(
            _issue(
                "URM_PROVIDER_PARITY_FIXTURE_INVALID",
                "provider parity fixture missing fixture_version",
                context={"path": str(artifact_ref)},
            )
        )
    status = payload.get("status")
    if not isinstance(status, str) or not status:
        raise ValueError(
            _issue(
                "URM_PROVIDER_PARITY_FIXTURE_INVALID",
                "provider parity fixture missing status",
                context={"path": str(artifact_ref)},
            )
        )
    hash_basis = {
        key: value
        for key, value in payload.items()
        if key not in {"run_index", "notes"}
    }
    return sha256_canonical_json(hash_basis), status == "PASS"


def _validated_adeu_lane_report_payload(*, lane_report_path: Path) -> dict[str, Any]:
    payload = _read_json_object(lane_report_path, description="adeu lane report fixture")
    if payload.get("schema") != ADEU_LANE_REPORT_SCHEMA:
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_LANE_REPORT_INVALID",
                "lane report fixture has unsupported schema",
                context={"path": str(lane_report_path), "schema": payload.get("schema")},
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_LANE_REPORT_INVALID",
                "lane report fixture missing source_text_hash",
                context={"path": str(lane_report_path)},
            )
        )
    lane_nodes = payload.get("lane_nodes")
    if not isinstance(lane_nodes, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_LANE_REPORT_INVALID",
                "lane report fixture lane_nodes must be an object",
                context={"path": str(lane_report_path)},
            )
        )
    lane_edge_counts = payload.get("lane_edge_counts")
    if not isinstance(lane_edge_counts, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_LANE_REPORT_INVALID",
                "lane report fixture lane_edge_counts must be an object",
                context={"path": str(lane_report_path)},
            )
        )

    total_nodes = 0
    for lane in ("O", "E", "D", "U"):
        node_ids = lane_nodes.get(lane)
        if not isinstance(node_ids, list):
            raise ValueError(
                _issue(
                    "URM_ADEU_DEPTH_LANE_REPORT_INVALID",
                    "lane report fixture lane_nodes entry must be a list",
                    context={"path": str(lane_report_path), "lane": lane},
                )
            )
        normalized_node_ids: list[str] = []
        for node_id in node_ids:
            if not isinstance(node_id, str) or not node_id:
                raise ValueError(
                    _issue(
                        "URM_ADEU_DEPTH_LANE_REPORT_INVALID",
                        "lane report fixture lane_nodes contains empty node id",
                        context={"path": str(lane_report_path), "lane": lane},
                    )
                )
            normalized_node_ids.append(node_id)
        if normalized_node_ids != sorted(normalized_node_ids):
            raise ValueError(
                _issue(
                    "URM_ADEU_DEPTH_LANE_REPORT_INVALID",
                    "lane report fixture lane_nodes must be lexicographically sorted",
                    context={"path": str(lane_report_path), "lane": lane},
                )
            )
        total_nodes += len(normalized_node_ids)

        edge_count = lane_edge_counts.get(lane)
        if not isinstance(edge_count, int) or edge_count < 0:
            raise ValueError(
                _issue(
                    "URM_ADEU_DEPTH_LANE_REPORT_INVALID",
                    "lane report fixture lane_edge_counts must be non-negative integers",
                    context={"path": str(lane_report_path), "lane": lane},
                )
            )

    if total_nodes <= 0:
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_FIXTURE_INVALID",
                "lane report fixture has empty lane-node evidence",
                context={"path": str(lane_report_path)},
            )
        )
    return payload


def _validated_adeu_projection_alignment_payload(
    *,
    projection_alignment_path: Path,
) -> dict[str, Any]:
    payload = _read_json_object(
        projection_alignment_path,
        description="adeu projection alignment fixture",
    )
    if payload.get("schema") != ADEU_PROJECTION_ALIGNMENT_SCHEMA:
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                "projection alignment fixture has unsupported schema",
                context={
                    "path": str(projection_alignment_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                "projection alignment fixture missing source_text_hash",
                context={"path": str(projection_alignment_path)},
            )
        )

    summary = payload.get("summary")
    if not isinstance(summary, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                "projection alignment fixture summary must be an object",
                context={"path": str(projection_alignment_path)},
            )
        )
    issues = payload.get("issues")
    if not isinstance(issues, list):
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                "projection alignment fixture issues must be a list",
                context={"path": str(projection_alignment_path)},
            )
        )

    issue_kind_counts = {
        "missing_in_projection": 0,
        "missing_in_extraction": 0,
        "kind_mismatch": 0,
        "edge_type_mismatch": 0,
    }
    issue_order_keys: list[tuple[str, str, str]] = []
    for issue_idx, raw_issue in enumerate(issues):
        if not isinstance(raw_issue, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                    "projection alignment issue must be an object",
                    context={"path": str(projection_alignment_path), "issue_index": issue_idx},
                )
            )
        kind = raw_issue.get("kind")
        if not isinstance(kind, str) or kind not in issue_kind_counts:
            raise ValueError(
                _issue(
                    "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                    "projection alignment issue kind is invalid",
                    context={"path": str(projection_alignment_path), "issue_index": issue_idx},
                )
            )
        subject_id = raw_issue.get("subject_id")
        if not isinstance(subject_id, str) or not subject_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                    "projection alignment issue subject_id is invalid",
                    context={"path": str(projection_alignment_path), "issue_index": issue_idx},
                )
            )
        related_id = raw_issue.get("related_id")
        if related_id is None:
            related_id = ""
        if not isinstance(related_id, str):
            raise ValueError(
                _issue(
                    "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                    "projection alignment issue related_id is invalid",
                    context={"path": str(projection_alignment_path), "issue_index": issue_idx},
                )
            )
        issue_order_keys.append((kind, subject_id, related_id))
        issue_kind_counts[kind] += 1

    if issue_order_keys != sorted(issue_order_keys):
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                "projection alignment issues must be sorted by (kind, subject_id, related_id)",
                context={"path": str(projection_alignment_path)},
            )
        )

    total_issues = summary.get("total_issues")
    if not isinstance(total_issues, int) or total_issues != len(issues):
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                "projection alignment summary.total_issues mismatch",
                context={"path": str(projection_alignment_path)},
            )
        )
    for kind, count in issue_kind_counts.items():
        observed = summary.get(kind)
        if not isinstance(observed, int) or observed != count:
            raise ValueError(
                _issue(
                    "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID",
                    f"projection alignment summary.{kind} mismatch",
                    context={"path": str(projection_alignment_path)},
                )
            )
    return payload


def _adeu_lane_report_fixture_hash(*, lane_report_path: Path) -> str:
    payload = _validated_adeu_lane_report_payload(lane_report_path=lane_report_path)
    return sha256_canonical_json(payload)


def _adeu_projection_alignment_fixture_hash(*, projection_alignment_path: Path) -> str:
    payload = _validated_adeu_projection_alignment_payload(
        projection_alignment_path=projection_alignment_path
    )
    return sha256_canonical_json(payload)


def _adeu_depth_report_fixture_hash(
    *,
    lane_report_path: Path,
    projection_alignment_path: Path,
) -> str:
    lane_report_payload = _validated_adeu_lane_report_payload(
        lane_report_path=lane_report_path
    )
    projection_alignment_payload = _validated_adeu_projection_alignment_payload(
        projection_alignment_path=projection_alignment_path
    )
    lane_source_hash = lane_report_payload.get("source_text_hash")
    alignment_source_hash = projection_alignment_payload.get("source_text_hash")
    if lane_source_hash != alignment_source_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_FIXTURE_INVALID",
                "depth report fixture source_text_hash mismatch",
                context={
                    "lane_report_path": str(lane_report_path),
                    "projection_alignment_path": str(projection_alignment_path),
                },
            )
        )
    lane_report_hash = sha256_canonical_json(lane_report_payload)
    projection_alignment_hash = sha256_canonical_json(projection_alignment_payload)
    return sha256_canonical_json(
        {
            "source_text_hash": lane_source_hash,
            "lane_report_hash": lane_report_hash,
            "projection_alignment_hash": projection_alignment_hash,
        }
    )


def _canonical_cycle_rotation(node_ids: list[str]) -> list[str]:
    if len(node_ids) <= 1:
        return list(node_ids)
    rotations = [node_ids[index:] + node_ids[:index] for index in range(len(node_ids))]
    return min(rotations)


def _validated_adeu_integrity_dangling_reference_payload(
    *,
    dangling_reference_path: Path,
) -> dict[str, Any]:
    payload = _read_json_object(
        dangling_reference_path,
        description="adeu integrity dangling-reference fixture",
    )
    if payload.get("schema") != ADEU_INTEGRITY_DANGLING_REFERENCE_SCHEMA:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                "dangling-reference fixture has unsupported schema",
                context={
                    "path": str(dangling_reference_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                "dangling-reference fixture missing source_text_hash",
                context={"path": str(dangling_reference_path)},
            )
        )
    summary = payload.get("summary")
    issues = payload.get("issues")
    if not isinstance(summary, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                "dangling-reference fixture summary must be an object",
                context={"path": str(dangling_reference_path)},
            )
        )
    if not isinstance(issues, list):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                "dangling-reference fixture issues must be a list",
                context={"path": str(dangling_reference_path)},
            )
        )

    issue_kind_counts = {
        "missing_node_reference": 0,
        "missing_edge_endpoint": 0,
    }
    issue_order_keys: list[tuple[str, str, str]] = []
    for issue_index, raw_issue in enumerate(issues):
        if not isinstance(raw_issue, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                    "dangling-reference issue must be an object",
                    context={"path": str(dangling_reference_path), "issue_index": issue_index},
                )
            )
        kind = raw_issue.get("kind")
        if not isinstance(kind, str) or kind not in issue_kind_counts:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                    "dangling-reference issue kind is invalid",
                    context={"path": str(dangling_reference_path), "issue_index": issue_index},
                )
            )
        subject_id = raw_issue.get("subject_id")
        if not isinstance(subject_id, str) or not subject_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                    "dangling-reference issue subject_id is invalid",
                    context={"path": str(dangling_reference_path), "issue_index": issue_index},
                )
            )
        related_id = raw_issue.get("related_id")
        if related_id is None:
            related_id = ""
        if not isinstance(related_id, str):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                    "dangling-reference issue related_id is invalid",
                    context={"path": str(dangling_reference_path), "issue_index": issue_index},
                )
            )
        issue_order_keys.append((kind, subject_id, related_id))
        issue_kind_counts[kind] += 1

    if issue_order_keys != sorted(issue_order_keys):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                "dangling-reference issues must be sorted by (kind, subject_id, related_id)",
                context={"path": str(dangling_reference_path)},
            )
        )

    total_issues = summary.get("total_issues")
    if not isinstance(total_issues, int) or total_issues != len(issues):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                "dangling-reference summary.total_issues mismatch",
                context={"path": str(dangling_reference_path)},
            )
        )
    for kind, count in issue_kind_counts.items():
        observed = summary.get(kind)
        if not isinstance(observed, int) or observed != count:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID",
                    f"dangling-reference summary.{kind} mismatch",
                    context={"path": str(dangling_reference_path)},
                )
            )

    return payload


def _validated_adeu_integrity_cycle_policy_payload(
    *,
    cycle_policy_path: Path,
) -> dict[str, Any]:
    payload = _read_json_object(
        cycle_policy_path,
        description="adeu integrity cycle-policy fixture",
    )
    if payload.get("schema") != ADEU_INTEGRITY_CYCLE_POLICY_SCHEMA:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                "cycle-policy fixture has unsupported schema",
                context={"path": str(cycle_policy_path), "schema": payload.get("schema")},
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                "cycle-policy fixture missing source_text_hash",
                context={"path": str(cycle_policy_path)},
            )
        )
    summary = payload.get("summary")
    cycles = payload.get("cycles")
    if not isinstance(summary, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                "cycle-policy fixture summary must be an object",
                context={"path": str(cycle_policy_path)},
            )
        )
    if not isinstance(cycles, list):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                "cycle-policy fixture cycles must be a list",
                context={"path": str(cycle_policy_path)},
            )
        )
    if len(cycles) > 1000:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "cycle-policy fixture exceeds frozen cycle cap",
                context={"path": str(cycle_policy_path), "max_cycles": 1000},
            )
        )

    cycle_kind_counts = {
        "self_cycle": 0,
        "multi_node_cycle": 0,
    }
    cycle_signatures: list[str] = []
    for cycle_index, raw_cycle in enumerate(cycles):
        if not isinstance(raw_cycle, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    "cycle entry must be an object",
                    context={"path": str(cycle_policy_path), "cycle_index": cycle_index},
                )
            )
        kind = raw_cycle.get("kind")
        if not isinstance(kind, str) or kind not in cycle_kind_counts:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    "cycle kind is invalid",
                    context={"path": str(cycle_policy_path), "cycle_index": cycle_index},
                )
            )
        cycle_signature = raw_cycle.get("cycle_signature")
        if not isinstance(cycle_signature, str) or not cycle_signature:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    "cycle_signature is invalid",
                    context={"path": str(cycle_policy_path), "cycle_index": cycle_index},
                )
            )
        raw_node_ids = raw_cycle.get("node_ids")
        if not isinstance(raw_node_ids, list) or not raw_node_ids:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    "cycle node_ids must be a non-empty list",
                    context={"path": str(cycle_policy_path), "cycle_index": cycle_index},
                )
            )
        node_ids: list[str] = []
        for node_id in raw_node_ids:
            if not isinstance(node_id, str) or not node_id:
                raise ValueError(
                    _issue(
                        "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                        "cycle node_ids contains invalid node id",
                        context={
                            "path": str(cycle_policy_path),
                            "cycle_index": cycle_index,
                        },
                    )
                )
            node_ids.append(node_id)
        if len(node_ids) > 1 and len(set(node_ids)) != len(node_ids):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    "cycle node_ids must not contain duplicate node ids",
                    context={"path": str(cycle_policy_path), "cycle_index": cycle_index},
                )
            )
        canonical_node_ids = _canonical_cycle_rotation(node_ids)
        if node_ids != canonical_node_ids:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    "cycle node_ids must use canonical rotation",
                    context={"path": str(cycle_policy_path), "cycle_index": cycle_index},
                )
            )
        expected_signature = "cycle:" + "->".join(node_ids)
        if cycle_signature != expected_signature:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    "cycle_signature must match canonical node_ids",
                    context={"path": str(cycle_policy_path), "cycle_index": cycle_index},
                )
            )
        expected_kind = "self_cycle" if len(node_ids) == 1 else "multi_node_cycle"
        if kind != expected_kind:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    "cycle kind must match node_ids cycle cardinality",
                    context={"path": str(cycle_policy_path), "cycle_index": cycle_index},
                )
            )
        cycle_signatures.append(cycle_signature)
        cycle_kind_counts[kind] += 1

    if cycle_signatures != sorted(cycle_signatures):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                "cycle entries must be sorted by cycle_signature",
                context={"path": str(cycle_policy_path)},
            )
        )
    if len(set(cycle_signatures)) != len(cycle_signatures):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                "cycle entries must be unique by cycle_signature",
                context={"path": str(cycle_policy_path)},
            )
        )

    total_cycles = summary.get("total_cycles")
    if not isinstance(total_cycles, int) or total_cycles != len(cycles):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                "cycle-policy summary.total_cycles mismatch",
                context={"path": str(cycle_policy_path)},
            )
        )
    for kind, count in cycle_kind_counts.items():
        observed = summary.get(kind)
        if not isinstance(observed, int) or observed != count:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID",
                    f"cycle-policy summary.{kind} mismatch",
                    context={"path": str(cycle_policy_path)},
                )
            )
    return payload


def _validated_adeu_integrity_deontic_conflict_payload(
    *,
    deontic_conflict_path: Path,
) -> dict[str, Any]:
    payload = _read_json_object(
        deontic_conflict_path,
        description="adeu integrity deontic-conflict fixture",
    )
    if payload.get("schema") != ADEU_INTEGRITY_DEONTIC_CONFLICT_SCHEMA:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                "deontic-conflict fixture has unsupported schema",
                context={
                    "path": str(deontic_conflict_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                "deontic-conflict fixture missing source_text_hash",
                context={"path": str(deontic_conflict_path)},
            )
        )
    summary = payload.get("summary")
    conflicts = payload.get("conflicts")
    if not isinstance(summary, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                "deontic-conflict fixture summary must be an object",
                context={"path": str(deontic_conflict_path)},
            )
        )
    if not isinstance(conflicts, list):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                "deontic-conflict fixture conflicts must be a list",
                context={"path": str(deontic_conflict_path)},
            )
        )
    if len(conflicts) > 1000:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "deontic-conflict fixture exceeds frozen conflict cap",
                context={"path": str(deontic_conflict_path), "max_conflicts": 1000},
            )
        )

    conflict_order_keys: list[tuple[str, str, str]] = []
    pair_keys: set[tuple[str, str]] = set()
    for conflict_index, raw_conflict in enumerate(conflicts):
        if not isinstance(raw_conflict, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                    "deontic-conflict entry must be an object",
                    context={"path": str(deontic_conflict_path), "conflict_index": conflict_index},
                )
            )
        kind = raw_conflict.get("kind")
        if kind != "deontic_conflict":
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                    "deontic-conflict entry kind is invalid",
                    context={"path": str(deontic_conflict_path), "conflict_index": conflict_index},
                )
            )
        primary_id = raw_conflict.get("primary_id")
        if not isinstance(primary_id, str) or not primary_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                    "deontic-conflict entry primary_id is invalid",
                    context={"path": str(deontic_conflict_path), "conflict_index": conflict_index},
                )
            )
        related_id = raw_conflict.get("related_id")
        if related_id is None:
            related_id = ""
        if not isinstance(related_id, str):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                    "deontic-conflict entry related_id is invalid",
                    context={"path": str(deontic_conflict_path), "conflict_index": conflict_index},
                )
            )
        if related_id and primary_id > related_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                    "deontic-conflict entry ids must follow canonical orientation",
                    context={"path": str(deontic_conflict_path), "conflict_index": conflict_index},
                )
            )
        details = raw_conflict.get("details")
        if details is not None and not isinstance(details, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                    "deontic-conflict entry details must be an object when present",
                    context={"path": str(deontic_conflict_path), "conflict_index": conflict_index},
                )
            )
        conflict_order_keys.append((str(kind), primary_id, related_id))
        pair_key = (primary_id, related_id)
        if pair_key in pair_keys:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                    "deontic-conflict entries must be unique by (primary_id, related_id)",
                    context={"path": str(deontic_conflict_path)},
                )
            )
        pair_keys.add(pair_key)

    if conflict_order_keys != sorted(conflict_order_keys):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                "deontic-conflict entries must be sorted by (kind, primary_id, related_id)",
                context={"path": str(deontic_conflict_path)},
            )
        )

    total_conflicts = summary.get("total_conflicts")
    deontic_conflict = summary.get("deontic_conflict")
    if not isinstance(total_conflicts, int) or total_conflicts != len(conflicts):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                "deontic-conflict summary.total_conflicts mismatch",
                context={"path": str(deontic_conflict_path)},
            )
        )
    if not isinstance(deontic_conflict, int) or deontic_conflict != len(conflicts):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID",
                "deontic-conflict summary.deontic_conflict mismatch",
                context={"path": str(deontic_conflict_path)},
            )
        )
    return payload


def _adeu_integrity_dangling_reference_fixture_hash(
    *,
    dangling_reference_path: Path,
) -> str:
    payload = _validated_adeu_integrity_dangling_reference_payload(
        dangling_reference_path=dangling_reference_path
    )
    return sha256_canonical_json(payload)


def _adeu_integrity_cycle_policy_fixture_hash(
    *,
    cycle_policy_path: Path,
) -> str:
    payload = _validated_adeu_integrity_cycle_policy_payload(
        cycle_policy_path=cycle_policy_path
    )
    return sha256_canonical_json(payload)


def _adeu_integrity_deontic_conflict_fixture_hash(
    *,
    deontic_conflict_path: Path,
) -> str:
    payload = _validated_adeu_integrity_deontic_conflict_payload(
        deontic_conflict_path=deontic_conflict_path
    )
    return sha256_canonical_json(payload)


def _adeu_integrity_dangling_reference_diagnostic_count(
    *,
    dangling_reference_path: Path,
) -> int:
    payload = _validated_adeu_integrity_dangling_reference_payload(
        dangling_reference_path=dangling_reference_path
    )
    summary = cast(Mapping[str, Any], payload.get("summary", {}))
    return int(summary.get("total_issues", 0))


def _adeu_integrity_cycle_policy_diagnostic_count(
    *,
    cycle_policy_path: Path,
) -> int:
    payload = _validated_adeu_integrity_cycle_policy_payload(
        cycle_policy_path=cycle_policy_path
    )
    summary = cast(Mapping[str, Any], payload.get("summary", {}))
    return int(summary.get("total_cycles", 0))


def _adeu_integrity_deontic_conflict_diagnostic_count(
    *,
    deontic_conflict_path: Path,
) -> int:
    payload = _validated_adeu_integrity_deontic_conflict_payload(
        deontic_conflict_path=deontic_conflict_path
    )
    summary = cast(Mapping[str, Any], payload.get("summary", {}))
    return int(summary.get("total_conflicts", 0))


def _validated_adeu_integrity_reference_integrity_extended_payload(
    *,
    reference_integrity_extended_path: Path,
) -> dict[str, Any]:
    payload = _read_json_object(
        reference_integrity_extended_path,
        description="adeu integrity reference-integrity extended fixture",
    )
    if payload.get("schema") != ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_SCHEMA:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                "reference-integrity extended fixture has unsupported schema",
                context={
                    "path": str(reference_integrity_extended_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                "reference-integrity extended fixture missing source_text_hash",
                context={"path": str(reference_integrity_extended_path)},
            )
        )
    summary = payload.get("summary")
    issues = payload.get("issues")
    if not isinstance(summary, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                "reference-integrity extended fixture summary must be an object",
                context={"path": str(reference_integrity_extended_path)},
            )
        )
    if not isinstance(issues, list):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                "reference-integrity extended fixture issues must be a list",
                context={"path": str(reference_integrity_extended_path)},
            )
        )
    if len(issues) > 1000:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "reference-integrity extended fixture exceeds frozen issue cap",
                context={"path": str(reference_integrity_extended_path), "max_issues": 1000},
            )
        )

    issue_kind_counts = {
        "edge_type_constraint_violation": 0,
        "duplicate_edge_identity": 0,
    }
    issue_order_keys: list[tuple[str, str, str]] = []
    issue_identity_keys: set[tuple[str, str, str]] = set()
    for issue_index, raw_issue in enumerate(issues):
        if not isinstance(raw_issue, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                    "reference-integrity extended issue must be an object",
                    context={
                        "path": str(reference_integrity_extended_path),
                        "issue_index": issue_index,
                    },
                )
            )
        kind = raw_issue.get("kind")
        if not isinstance(kind, str) or kind not in issue_kind_counts:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                    "reference-integrity extended issue kind is invalid",
                    context={
                        "path": str(reference_integrity_extended_path),
                        "issue_index": issue_index,
                    },
                )
            )
        subject_id = raw_issue.get("subject_id")
        if not isinstance(subject_id, str) or not subject_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                    "reference-integrity extended issue subject_id is invalid",
                    context={
                        "path": str(reference_integrity_extended_path),
                        "issue_index": issue_index,
                    },
                )
            )
        related_id = raw_issue.get("related_id")
        if related_id is None:
            related_id = ""
        if not isinstance(related_id, str):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                    "reference-integrity extended issue related_id is invalid",
                    context={
                        "path": str(reference_integrity_extended_path),
                        "issue_index": issue_index,
                    },
                )
            )
        details = raw_issue.get("details")
        if details is not None and not isinstance(details, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                    "reference-integrity extended issue details must be an object when present",
                    context={
                        "path": str(reference_integrity_extended_path),
                        "issue_index": issue_index,
                    },
                )
            )
        issue_order_keys.append((kind, subject_id, related_id))
        issue_identity_key = (kind, subject_id, related_id)
        if issue_identity_key in issue_identity_keys:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                    "reference-integrity extended issues must be unique by "
                    "(kind, subject_id, related_id)",
                    context={"path": str(reference_integrity_extended_path)},
                )
            )
        issue_identity_keys.add(issue_identity_key)
        issue_kind_counts[kind] += 1

    if issue_order_keys != sorted(issue_order_keys):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                "reference-integrity extended issues must be sorted by "
                "(kind, subject_id, related_id)",
                context={"path": str(reference_integrity_extended_path)},
            )
        )

    total_issues = summary.get("total_issues")
    if not isinstance(total_issues, int) or total_issues != len(issues):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                "reference-integrity extended summary.total_issues mismatch",
                context={"path": str(reference_integrity_extended_path)},
            )
        )
    for kind, count in issue_kind_counts.items():
        observed = summary.get(kind)
        if not isinstance(observed, int) or observed != count:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID",
                    f"reference-integrity extended summary.{kind} mismatch",
                    context={"path": str(reference_integrity_extended_path)},
                )
            )
    return payload


def _validated_adeu_integrity_cycle_policy_extended_payload(
    *,
    cycle_policy_extended_path: Path,
) -> dict[str, Any]:
    payload = _read_json_object(
        cycle_policy_extended_path,
        description="adeu integrity cycle-policy extended fixture",
    )
    if payload.get("schema") != ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_SCHEMA:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                "cycle-policy extended fixture has unsupported schema",
                context={
                    "path": str(cycle_policy_extended_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                "cycle-policy extended fixture missing source_text_hash",
                context={"path": str(cycle_policy_extended_path)},
            )
        )
    summary = payload.get("summary")
    cycles = payload.get("cycles")
    if not isinstance(summary, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                "cycle-policy extended fixture summary must be an object",
                context={"path": str(cycle_policy_extended_path)},
            )
        )
    if not isinstance(cycles, list):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                "cycle-policy extended fixture cycles must be a list",
                context={"path": str(cycle_policy_extended_path)},
            )
        )
    if len(cycles) > 1000:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "cycle-policy extended fixture exceeds frozen cycle cap",
                context={"path": str(cycle_policy_extended_path), "max_cycles": 1000},
            )
        )

    cycle_kind_counts = {
        "self_cycle": 0,
        "multi_node_cycle": 0,
        "dependency_loop": 0,
        "exception_loop": 0,
    }
    cycle_order_keys: list[tuple[str, str]] = []
    cycle_identity_keys: set[tuple[str, str]] = set()
    for cycle_index, raw_cycle in enumerate(cycles):
        if not isinstance(raw_cycle, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "cycle entry must be an object",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        kind = raw_cycle.get("kind")
        if not isinstance(kind, str) or kind not in cycle_kind_counts:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "cycle kind is invalid",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        cycle_signature = raw_cycle.get("cycle_signature")
        if not isinstance(cycle_signature, str) or not cycle_signature:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "cycle_signature is invalid",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        raw_node_ids = raw_cycle.get("node_ids")
        if not isinstance(raw_node_ids, list) or not raw_node_ids:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "cycle node_ids must be a non-empty list",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        node_ids: list[str] = []
        for node_id in raw_node_ids:
            if not isinstance(node_id, str) or not node_id:
                raise ValueError(
                    _issue(
                        "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                        "cycle node_ids contains invalid node id",
                        context={
                            "path": str(cycle_policy_extended_path),
                            "cycle_index": cycle_index,
                        },
                    )
                )
            node_ids.append(node_id)
        if len(node_ids) > 1 and len(set(node_ids)) != len(node_ids):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "cycle node_ids must not contain duplicate node ids",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        canonical_node_ids = _canonical_cycle_rotation(node_ids)
        if node_ids != canonical_node_ids:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "cycle node_ids must use canonical rotation",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        expected_signature = "cycle:" + "->".join(node_ids)
        if cycle_signature != expected_signature:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "cycle_signature must match canonical node_ids",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        if kind == "self_cycle" and len(node_ids) != 1:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "self_cycle must include exactly one node_id",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        if kind == "multi_node_cycle" and len(node_ids) <= 1:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "multi_node_cycle must include at least two node_ids",
                    context={"path": str(cycle_policy_extended_path), "cycle_index": cycle_index},
                )
            )
        cycle_order_keys.append((kind, cycle_signature))
        cycle_identity_key = (kind, cycle_signature)
        if cycle_identity_key in cycle_identity_keys:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    "cycle entries must be unique by (kind, cycle_signature)",
                    context={"path": str(cycle_policy_extended_path)},
                )
            )
        cycle_identity_keys.add(cycle_identity_key)
        cycle_kind_counts[kind] += 1

    if cycle_order_keys != sorted(cycle_order_keys):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                "cycle entries must be sorted by (kind, cycle_signature)",
                context={"path": str(cycle_policy_extended_path)},
            )
        )

    total_cycles = summary.get("total_cycles")
    if not isinstance(total_cycles, int) or total_cycles != len(cycles):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                "cycle-policy extended summary.total_cycles mismatch",
                context={"path": str(cycle_policy_extended_path)},
            )
        )
    for kind, count in cycle_kind_counts.items():
        observed = summary.get(kind)
        if not isinstance(observed, int) or observed != count:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID",
                    f"cycle-policy extended summary.{kind} mismatch",
                    context={"path": str(cycle_policy_extended_path)},
                )
            )
    return payload


def _validated_adeu_integrity_deontic_conflict_extended_payload(
    *,
    deontic_conflict_extended_path: Path,
) -> dict[str, Any]:
    payload = _read_json_object(
        deontic_conflict_extended_path,
        description="adeu integrity deontic-conflict extended fixture",
    )
    if payload.get("schema") != ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_SCHEMA:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                "deontic-conflict extended fixture has unsupported schema",
                context={
                    "path": str(deontic_conflict_extended_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    source_text_hash = payload.get("source_text_hash")
    if not isinstance(source_text_hash, str) or not source_text_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                "deontic-conflict extended fixture missing source_text_hash",
                context={"path": str(deontic_conflict_extended_path)},
            )
        )
    summary = payload.get("summary")
    conflicts = payload.get("conflicts")
    if not isinstance(summary, Mapping):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                "deontic-conflict extended fixture summary must be an object",
                context={"path": str(deontic_conflict_extended_path)},
            )
        )
    if not isinstance(conflicts, list):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                "deontic-conflict extended fixture conflicts must be a list",
                context={"path": str(deontic_conflict_extended_path)},
            )
        )
    if len(conflicts) > 1000:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "deontic-conflict extended fixture exceeds frozen conflict cap",
                context={"path": str(deontic_conflict_extended_path), "max_conflicts": 1000},
            )
        )

    conflict_kind_counts = {
        "deontic_conflict": 0,
        "deontic_tension": 0,
    }
    conflict_order_keys: list[tuple[str, str, str]] = []
    conflict_identity_keys: set[tuple[str, str, str]] = set()
    pair_keys: set[tuple[str, str]] = set()
    for conflict_index, raw_conflict in enumerate(conflicts):
        if not isinstance(raw_conflict, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    "deontic-conflict extended entry must be an object",
                    context={
                        "path": str(deontic_conflict_extended_path),
                        "conflict_index": conflict_index,
                    },
                )
            )
        kind = raw_conflict.get("kind")
        if not isinstance(kind, str) or kind not in conflict_kind_counts:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    "deontic-conflict extended entry kind is invalid",
                    context={
                        "path": str(deontic_conflict_extended_path),
                        "conflict_index": conflict_index,
                    },
                )
            )
        primary_id = raw_conflict.get("primary_id")
        if not isinstance(primary_id, str) or not primary_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    "deontic-conflict extended entry primary_id is invalid",
                    context={
                        "path": str(deontic_conflict_extended_path),
                        "conflict_index": conflict_index,
                    },
                )
            )
        related_id = raw_conflict.get("related_id")
        if related_id is None:
            related_id = ""
        if not isinstance(related_id, str):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    "deontic-conflict extended entry related_id is invalid",
                    context={
                        "path": str(deontic_conflict_extended_path),
                        "conflict_index": conflict_index,
                    },
                )
            )
        if related_id and primary_id > related_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    "deontic-conflict extended entry ids must follow canonical orientation",
                    context={
                        "path": str(deontic_conflict_extended_path),
                        "conflict_index": conflict_index,
                    },
                )
            )
        details = raw_conflict.get("details")
        if details is not None and not isinstance(details, Mapping):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    "deontic-conflict extended entry details must be an object when present",
                    context={
                        "path": str(deontic_conflict_extended_path),
                        "conflict_index": conflict_index,
                    },
                )
            )
        conflict_order_keys.append((kind, primary_id, related_id))
        conflict_identity_key = (kind, primary_id, related_id)
        if conflict_identity_key in conflict_identity_keys:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    "deontic-conflict extended entries must be unique by "
                    "(kind, primary_id, related_id)",
                    context={"path": str(deontic_conflict_extended_path)},
                )
            )
        conflict_identity_keys.add(conflict_identity_key)
        pair_key = (primary_id, related_id)
        if pair_key in pair_keys:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    "deontic-conflict extended entries must be unique by "
                    "(primary_id, related_id) across kinds",
                    context={"path": str(deontic_conflict_extended_path)},
                )
            )
        pair_keys.add(pair_key)
        conflict_kind_counts[kind] += 1

    if conflict_order_keys != sorted(conflict_order_keys):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                "deontic-conflict extended entries must be sorted by "
                "(kind, primary_id, related_id)",
                context={"path": str(deontic_conflict_extended_path)},
            )
        )

    total_conflicts = summary.get("total_conflicts")
    if not isinstance(total_conflicts, int) or total_conflicts != len(conflicts):
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                "deontic-conflict extended summary.total_conflicts mismatch",
                context={"path": str(deontic_conflict_extended_path)},
            )
        )
    for kind, count in conflict_kind_counts.items():
        observed = summary.get(kind)
        if not isinstance(observed, int) or observed != count:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID",
                    f"deontic-conflict extended summary.{kind} mismatch",
                    context={"path": str(deontic_conflict_extended_path)},
                )
            )
    return payload


def _adeu_integrity_reference_integrity_extended_fixture_hash(
    *,
    reference_integrity_extended_path: Path,
) -> str:
    payload = _validated_adeu_integrity_reference_integrity_extended_payload(
        reference_integrity_extended_path=reference_integrity_extended_path
    )
    return sha256_canonical_json(payload)


def _adeu_integrity_cycle_policy_extended_fixture_hash(
    *,
    cycle_policy_extended_path: Path,
) -> str:
    payload = _validated_adeu_integrity_cycle_policy_extended_payload(
        cycle_policy_extended_path=cycle_policy_extended_path
    )
    return sha256_canonical_json(payload)


def _adeu_integrity_deontic_conflict_extended_fixture_hash(
    *,
    deontic_conflict_extended_path: Path,
) -> str:
    payload = _validated_adeu_integrity_deontic_conflict_extended_payload(
        deontic_conflict_extended_path=deontic_conflict_extended_path
    )
    return sha256_canonical_json(payload)


def _adeu_integrity_reference_integrity_extended_diagnostic_count(
    *,
    reference_integrity_extended_path: Path,
) -> int:
    payload = _validated_adeu_integrity_reference_integrity_extended_payload(
        reference_integrity_extended_path=reference_integrity_extended_path
    )
    summary = cast(Mapping[str, Any], payload.get("summary", {}))
    return int(summary.get("total_issues", 0))


def _adeu_integrity_cycle_policy_extended_diagnostic_count(
    *,
    cycle_policy_extended_path: Path,
) -> int:
    payload = _validated_adeu_integrity_cycle_policy_extended_payload(
        cycle_policy_extended_path=cycle_policy_extended_path
    )
    summary = cast(Mapping[str, Any], payload.get("summary", {}))
    return int(summary.get("total_cycles", 0))


def _adeu_integrity_deontic_conflict_extended_diagnostic_count(
    *,
    deontic_conflict_extended_path: Path,
) -> int:
    payload = _validated_adeu_integrity_deontic_conflict_extended_payload(
        deontic_conflict_extended_path=deontic_conflict_extended_path
    )
    summary = cast(Mapping[str, Any], payload.get("summary", {}))
    return int(summary.get("total_conflicts", 0))


def _expand_provider_route_unit_fixtures(
    *,
    fixtures: list[dict[str, Any]],
    manifest_path: Path,
    metric_name: str,
    issues: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    expanded: list[dict[str, Any]] = []
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
        surface_id = fixture.get("surface_id")
        if not isinstance(surface_id, str) or not surface_id:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture surface_id must be a non-empty string",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )
            continue
        providers = fixture.get("providers")
        if not isinstance(providers, list) or not providers:
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture providers must be a non-empty list",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )
            continue
        normalized_providers: list[str] = []
        providers_ok = True
        for provider in providers:
            provider_value = provider if isinstance(provider, str) else ""
            if not provider_value or provider_value not in _FROZEN_PROVIDER_KIND_SET:
                providers_ok = False
                break
            normalized_providers.append(provider_value)
        if not providers_ok or len(set(normalized_providers)) != len(normalized_providers):
            issues.append(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture providers must contain unique frozen provider kinds",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )
            continue
        runs = fixture.get("runs")
        for provider in normalized_providers:
            expanded.append(
                {
                    "fixture_id": f"{fixture_id}.{surface_id}.{provider}",
                    "runs": runs,
                }
            )
    return expanded


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


def _map_issue_code(
    issue: dict[str, Any],
    *,
    code_map: Mapping[str, str],
) -> dict[str, Any]:
    mapped = dict(issue)
    code = mapped.get("code")
    if isinstance(code, str) and code in code_map:
        mapped["code"] = code_map[code]
    return mapped


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
    invalid_issue_code: str = "URM_STOP_GATE_INPUT_INVALID",
    drift_issue_code: str | None = None,
    drift_issue_message: str | None = None,
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
                    invalid_issue_code,
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
                    invalid_issue_code,
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
                    invalid_issue_code,
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
                        invalid_issue_code,
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
                    invalid_issue_code,
                    str(exc),
                )
                issue = _map_issue_code(
                    issue,
                    code_map={"URM_STOP_GATE_INPUT_INVALID": invalid_issue_code},
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
                        invalid_issue_code,
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
        elif fixture_ok and len(fixture_hashes) > 1 and drift_issue_code is not None:
            issues.append(
                _issue(
                    drift_issue_code,
                    drift_issue_message
                    or "fixture replay produced non-deterministic hashes",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                        "replay_count": replay_count,
                        "distinct_hash_count": len(fixture_hashes),
                    },
                )
            )
    return _pct(passed, total)


def _has_non_zero_diagnostic_fixture(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
    required_run_fields: tuple[str, ...],
    run_diagnostic_count_builder: Callable[..., int],
) -> bool:
    for fixture in fixtures:
        runs = fixture.get("runs")
        if not isinstance(runs, list):
            continue
        for run in runs:
            if not isinstance(run, dict):
                continue
            try:
                resolved_paths = {
                    key: _resolve_manifest_relative_path(
                        manifest_path=manifest_path,
                        raw_path=run.get(key),
                    )
                    for key in required_run_fields
                }
                diagnostic_count = run_diagnostic_count_builder(**resolved_paths)
            except ValueError:
                continue
            if diagnostic_count > 0:
                return True
    return False


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


def _validate_vnext_plus14_surface_provider_fixtures(
    *,
    fixtures: list[Any],
    manifest_path: Path,
    metric_name: str,
    codex_only: bool = False,
) -> None:
    for fixture_index, raw_fixture in enumerate(fixtures):
        if not isinstance(raw_fixture, dict):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture entry must be an object",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_index": fixture_index,
                    },
                )
            )

        fixture_id = raw_fixture.get("fixture_id")
        if not isinstance(fixture_id, str) or not fixture_id:
            fixture_id = f"{metric_name}_fixture_{fixture_index}"

        surface_id = raw_fixture.get("surface_id")
        if not isinstance(surface_id, str) or not surface_id:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture surface_id must be a non-empty string",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )

        provider = raw_fixture.get("provider")
        if not isinstance(provider, str) or provider not in _FROZEN_PROVIDER_KIND_SET:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture provider must be a frozen provider kind",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )

        if codex_only and provider != "codex":
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "codex candidate fixtures must use provider='codex'",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                        "provider": provider,
                    },
                )
            )


def _load_vnext_plus14_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(manifest_path, description="vnext+14 stop-gate manifest")
    if payload.get("schema") != VNEXT_PLUS14_MANIFEST_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+14 stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS14_REPLAY_COUNT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+14 replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": VNEXT_PLUS14_REPLAY_COUNT,
                    "observed_replay_count": replay_count,
                },
            )
        )
    for key in (
        "provider_route_contract_parity_fixtures",
        "codex_candidate_contract_valid_fixtures",
        "provider_parity_replay_determinism_fixtures",
    ):
        if not isinstance(payload.get(key), list):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "vnext+14 stop-gate manifest missing required fixture list",
                    context={"manifest_path": str(manifest_path), "key": key},
                )
            )

    _validate_vnext_plus14_surface_provider_fixtures(
        fixtures=cast(list[Any], payload["codex_candidate_contract_valid_fixtures"]),
        manifest_path=manifest_path,
        metric_name="codex_candidate_contract_valid_pct",
        codex_only=True,
    )
    _validate_vnext_plus14_surface_provider_fixtures(
        fixtures=cast(list[Any], payload["provider_parity_replay_determinism_fixtures"]),
        manifest_path=manifest_path,
        metric_name="provider_parity_replay_determinism_pct",
        codex_only=False,
    )

    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+14 stop-gate manifest missing manifest_hash",
                context={"manifest_path": str(manifest_path)},
            )
        )
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ValueError(
            _issue(
                "URM_PROVIDER_PARITY_MANIFEST_HASH_MISMATCH",
                "vnext+14 manifest_hash mismatch",
                context={
                    "manifest_path": str(manifest_path),
                    "embedded_manifest_hash": raw_manifest_hash,
                    "recomputed_manifest_hash": recomputed_manifest_hash,
                },
            )
        )
    return payload, recomputed_manifest_hash


def _compute_vnext_plus14_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS14_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus14_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS14_DEFAULT_METRICS,
            "vnext_plus14_manifest_hash": "",
        }

    try:
        provider_route_fixtures = _manifest_metric_entries(
            metrics={
                "provider_route_contract_parity_pct": manifest.get(
                    "provider_route_contract_parity_fixtures"
                )
            },
            metric_name="provider_route_contract_parity_pct",
            manifest_path=resolved_manifest_path,
        )
        codex_candidate_fixtures = _manifest_metric_entries(
            metrics={
                "codex_candidate_contract_valid_pct": manifest.get(
                    "codex_candidate_contract_valid_fixtures"
                )
            },
            metric_name="codex_candidate_contract_valid_pct",
            manifest_path=resolved_manifest_path,
        )
        replay_fixtures = _manifest_metric_entries(
            metrics={
                "provider_parity_replay_determinism_pct": manifest.get(
                    "provider_parity_replay_determinism_fixtures"
                )
            },
            metric_name="provider_parity_replay_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS14_DEFAULT_METRICS,
            "vnext_plus14_manifest_hash": manifest_hash,
        }

    provider_route_unit_fixtures = _expand_provider_route_unit_fixtures(
        fixtures=provider_route_fixtures,
        manifest_path=resolved_manifest_path,
        metric_name="provider_route_contract_parity_pct",
        issues=issues,
    )
    provider_route_contract_parity_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="provider_route_contract_parity_pct",
        fixtures=provider_route_unit_fixtures,
        replay_count=VNEXT_PLUS14_REPLAY_COUNT,
        required_run_fields=("artifact_ref",),
        run_hash_builder=_provider_parity_fixture_hash,
        issues=issues,
    )
    codex_candidate_contract_valid_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="codex_candidate_contract_valid_pct",
        fixtures=codex_candidate_fixtures,
        replay_count=VNEXT_PLUS14_REPLAY_COUNT,
        required_run_fields=("artifact_ref",),
        run_hash_builder=_provider_parity_fixture_hash,
        issues=issues,
    )
    provider_parity_replay_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="provider_parity_replay_determinism_pct",
        fixtures=replay_fixtures,
        replay_count=VNEXT_PLUS14_REPLAY_COUNT,
        required_run_fields=("artifact_ref",),
        run_hash_builder=_provider_parity_fixture_hash,
        issues=issues,
    )
    return {
        "provider_route_contract_parity_pct": provider_route_contract_parity_pct,
        "codex_candidate_contract_valid_pct": codex_candidate_contract_valid_pct,
        "provider_parity_replay_determinism_pct": provider_parity_replay_determinism_pct,
        "vnext_plus14_manifest_hash": manifest_hash,
    }


def _validate_vnext_plus15_surface_fixtures(
    *,
    fixtures: list[Any],
    manifest_path: Path,
    metric_name: str,
) -> None:
    for fixture_index, raw_fixture in enumerate(fixtures):
        if not isinstance(raw_fixture, dict):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture entry must be an object",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_index": fixture_index,
                    },
                )
            )
        fixture_id = raw_fixture.get("fixture_id")
        if not isinstance(fixture_id, str) or not fixture_id:
            fixture_id = f"{metric_name}_fixture_{fixture_index}"
        surface_id = raw_fixture.get("surface_id")
        if not isinstance(surface_id, str) or surface_id not in _FROZEN_DEPTH_SURFACE_SET:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "manifest fixture surface_id must be a frozen depth surface",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                        "surface_id": surface_id,
                    },
                )
            )


def _load_vnext_plus15_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(manifest_path, description="vnext+15 stop-gate manifest")
    if payload.get("schema") != VNEXT_PLUS15_MANIFEST_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+15 stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS15_REPLAY_COUNT:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+15 replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": VNEXT_PLUS15_REPLAY_COUNT,
                    "observed_replay_count": replay_count,
                },
            )
        )
    for key in (
        "lane_report_replay_fixtures",
        "projection_alignment_fixtures",
        "depth_report_replay_fixtures",
    ):
        if not isinstance(payload.get(key), list):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "vnext+15 stop-gate manifest missing required fixture list",
                    context={"manifest_path": str(manifest_path), "key": key},
                )
            )

    _validate_vnext_plus15_surface_fixtures(
        fixtures=cast(list[Any], payload["lane_report_replay_fixtures"]),
        manifest_path=manifest_path,
        metric_name="adeu_lane_report_replay_determinism_pct",
    )
    _validate_vnext_plus15_surface_fixtures(
        fixtures=cast(list[Any], payload["projection_alignment_fixtures"]),
        manifest_path=manifest_path,
        metric_name="adeu_projection_alignment_determinism_pct",
    )
    _validate_vnext_plus15_surface_fixtures(
        fixtures=cast(list[Any], payload["depth_report_replay_fixtures"]),
        manifest_path=manifest_path,
        metric_name="adeu_depth_report_replay_determinism_pct",
    )

    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "vnext+15 stop-gate manifest missing manifest_hash",
                context={"manifest_path": str(manifest_path)},
            )
        )
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_DEPTH_MANIFEST_HASH_MISMATCH",
                "vnext+15 manifest_hash mismatch",
                context={
                    "manifest_path": str(manifest_path),
                    "embedded_manifest_hash": raw_manifest_hash,
                    "recomputed_manifest_hash": recomputed_manifest_hash,
                },
            )
        )
    return payload, recomputed_manifest_hash


def _compute_vnext_plus15_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS15_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus15_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS15_DEFAULT_METRICS,
            "vnext_plus15_manifest_hash": "",
        }

    try:
        lane_report_fixtures = _manifest_metric_entries(
            metrics={
                "adeu_lane_report_replay_determinism_pct": manifest.get(
                    "lane_report_replay_fixtures"
                )
            },
            metric_name="adeu_lane_report_replay_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        projection_alignment_fixtures = _manifest_metric_entries(
            metrics={
                "adeu_projection_alignment_determinism_pct": manifest.get(
                    "projection_alignment_fixtures"
                )
            },
            metric_name="adeu_projection_alignment_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        depth_report_fixtures = _manifest_metric_entries(
            metrics={
                "adeu_depth_report_replay_determinism_pct": manifest.get(
                    "depth_report_replay_fixtures"
                )
            },
            metric_name="adeu_depth_report_replay_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_STOP_GATE_INPUT_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS15_DEFAULT_METRICS,
            "vnext_plus15_manifest_hash": manifest_hash,
        }

    adeu_lane_report_replay_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="adeu_lane_report_replay_determinism_pct",
        fixtures=lane_report_fixtures,
        replay_count=VNEXT_PLUS15_REPLAY_COUNT,
        required_run_fields=("lane_report_path",),
        run_hash_builder=_adeu_lane_report_fixture_hash,
        issues=issues,
    )
    adeu_projection_alignment_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="adeu_projection_alignment_determinism_pct",
        fixtures=projection_alignment_fixtures,
        replay_count=VNEXT_PLUS15_REPLAY_COUNT,
        required_run_fields=("projection_alignment_path",),
        run_hash_builder=_adeu_projection_alignment_fixture_hash,
        issues=issues,
        drift_issue_code="URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_DRIFT",
        drift_issue_message="vnext+15 projection alignment diagnostic drift",
    )
    adeu_depth_report_replay_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="adeu_depth_report_replay_determinism_pct",
        fixtures=depth_report_fixtures,
        replay_count=VNEXT_PLUS15_REPLAY_COUNT,
        required_run_fields=("lane_report_path", "projection_alignment_path"),
        run_hash_builder=_adeu_depth_report_fixture_hash,
        issues=issues,
    )
    return {
        "adeu_lane_report_replay_determinism_pct": adeu_lane_report_replay_determinism_pct,
        "adeu_projection_alignment_determinism_pct": (
            adeu_projection_alignment_determinism_pct
        ),
        "adeu_depth_report_replay_determinism_pct": adeu_depth_report_replay_determinism_pct,
        "vnext_plus15_manifest_hash": manifest_hash,
    }


_IntegritySurfaceFixtureSpec = tuple[str, str, str, tuple[str, ...]]

_VNEXT_PLUS16_INTEGRITY_SURFACE_SPECS: tuple[_IntegritySurfaceFixtureSpec, ...] = (
    (
        "dangling_reference_fixtures",
        "artifact_dangling_reference_determinism_pct",
        "adeu.integrity.dangling_reference",
        ("dangling_reference_path",),
    ),
    (
        "cycle_policy_fixtures",
        "artifact_cycle_policy_determinism_pct",
        "adeu.integrity.cycle_policy",
        ("cycle_policy_path",),
    ),
    (
        "deontic_conflict_fixtures",
        "artifact_deontic_conflict_determinism_pct",
        "adeu.integrity.deontic_conflict",
        ("deontic_conflict_path",),
    ),
)

_VNEXT_PLUS17_INTEGRITY_SURFACE_SPECS: tuple[_IntegritySurfaceFixtureSpec, ...] = (
    (
        "reference_integrity_extended_fixtures",
        "artifact_reference_integrity_extended_determinism_pct",
        "adeu.integrity.reference_integrity_extended",
        ("reference_integrity_extended_path",),
    ),
    (
        "cycle_policy_extended_fixtures",
        "artifact_cycle_policy_extended_determinism_pct",
        "adeu.integrity.cycle_policy_extended",
        ("cycle_policy_extended_path",),
    ),
    (
        "deontic_conflict_extended_fixtures",
        "artifact_deontic_conflict_extended_determinism_pct",
        "adeu.integrity.deontic_conflict_extended",
        ("deontic_conflict_extended_path",),
    ),
)

_VNEXT_PLUS18_TOOLING_SURFACE_SPECS: tuple[_IntegritySurfaceFixtureSpec, ...] = (
    (
        "validation_parity_fixtures",
        "artifact_validation_consolidation_parity_pct",
        "adeu.tooling.validation_parity",
        ("baseline_path", "candidate_path"),
    ),
    (
        "transfer_report_parity_fixtures",
        "artifact_transfer_report_consolidation_parity_pct",
        "adeu.tooling.transfer_report_parity",
        ("baseline_path", "candidate_path"),
    ),
    (
        "ci_budget_fixtures",
        VNEXT_PLUS18_CI_BUDGET_METRIC_KEY,
        "adeu.tooling.ci_budget",
        ("report_path",),
    ),
)

_VNEXT_PLUS19_READ_SURFACE_SPECS: tuple[_IntegritySurfaceFixtureSpec, ...] = (
    (
        "core_ir_read_surface_fixtures",
        "artifact_core_ir_read_surface_determinism_pct",
        "adeu.read_surface.core_ir",
        ("core_ir_read_surface_path",),
    ),
    (
        "lane_read_surface_fixtures",
        "artifact_lane_read_surface_determinism_pct",
        "adeu.read_surface.lane",
        ("lane_read_surface_path",),
    ),
    (
        "integrity_read_surface_fixtures",
        "artifact_integrity_read_surface_determinism_pct",
        "adeu.read_surface.integrity",
        ("integrity_read_surface_path",),
    ),
)


def _validate_integrity_surface_fixtures(
    *,
    fixtures: list[Any],
    manifest_path: Path,
    metric_name: str,
    expected_surface_id: str,
    required_run_keys: tuple[str, ...],
    frozen_surface_set: frozenset[str],
    surface_description: str,
) -> None:
    seen_fixture_ids: set[str] = set()
    for fixture_index, raw_fixture in enumerate(fixtures):
        if not isinstance(raw_fixture, dict):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "manifest fixture entry must be an object",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_index": fixture_index,
                    },
                )
            )
        fixture_id = raw_fixture.get("fixture_id")
        if not isinstance(fixture_id, str) or not fixture_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "manifest fixture fixture_id must be a non-empty string",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_index": fixture_index,
                    },
                )
            )
        if fixture_id in seen_fixture_ids:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "manifest fixture fixture_id is duplicated in list",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )
        seen_fixture_ids.add(fixture_id)

        surface_id = raw_fixture.get("surface_id")
        if not isinstance(surface_id, str) or surface_id not in frozen_surface_set:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    f"manifest fixture surface_id must be a {surface_description}",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                        "surface_id": surface_id,
                    },
                )
            )
        if surface_id != expected_surface_id:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "manifest fixture surface_id does not match fixture list surface",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                        "surface_id": surface_id,
                        "expected_surface_id": expected_surface_id,
                    },
                )
            )

        runs = raw_fixture.get("runs")
        if not isinstance(runs, list):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "manifest fixture runs must be a list",
                    context={
                        "manifest_path": str(manifest_path),
                        "metric": metric_name,
                        "fixture_id": fixture_id,
                    },
                )
            )
        for run_index, raw_run in enumerate(runs):
            if not isinstance(raw_run, dict):
                raise ValueError(
                    _issue(
                        "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                        "manifest run entry must be an object",
                        context={
                            "manifest_path": str(manifest_path),
                            "metric": metric_name,
                            "fixture_id": fixture_id,
                            "run_index": run_index,
                        },
                    )
                )
            for run_key in required_run_keys:
                run_ref = raw_run.get(run_key)
                if not isinstance(run_ref, str) or not run_ref:
                    raise ValueError(
                        _issue(
                            "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                            "manifest run missing required run-reference key",
                            context={
                                "manifest_path": str(manifest_path),
                                "metric": metric_name,
                                "fixture_id": fixture_id,
                                "run_index": run_index,
                                "required_run_key": run_key,
                            },
                        )
                    )


def _validate_integrity_required_fixture_lists(
    *,
    payload: dict[str, Any],
    manifest_path: Path,
    manifest_label: str,
    fixture_list_keys: tuple[str, ...],
) -> None:
    for key in fixture_list_keys:
        fixtures = payload.get(key)
        if not isinstance(fixtures, list):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    f"{manifest_label} stop-gate manifest missing required fixture list",
                    context={"manifest_path": str(manifest_path), "key": key},
                )
            )
        if not fixtures:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    f"{manifest_label} stop-gate fixture list may not be empty",
                    context={"manifest_path": str(manifest_path), "key": key},
                )
            )


def _build_integrity_fixture_surface_catalog(
    *,
    payload: dict[str, Any],
    manifest_path: Path,
    manifest_label: str,
    fixture_list_keys: tuple[str, ...],
) -> dict[str, str]:
    fixture_surface_catalog: dict[str, str] = {}
    for key in fixture_list_keys:
        fixtures = cast(list[dict[str, Any]], payload[key])
        for fixture in fixtures:
            fixture_id = str(fixture["fixture_id"])
            surface_id = str(fixture["surface_id"])
            if fixture_id in fixture_surface_catalog:
                raise ValueError(
                    _issue(
                        "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                        f"{manifest_label} fixture_id must be unique across fixture lists",
                        context={
                            "manifest_path": str(manifest_path),
                            "fixture_id": fixture_id,
                        },
                    )
                )
            fixture_surface_catalog[fixture_id] = surface_id
    return fixture_surface_catalog


def _validate_integrity_coverage(
    *,
    payload: dict[str, Any],
    manifest_path: Path,
    manifest_label: str,
    frozen_surface_set: frozenset[str],
    frozen_surfaces: tuple[str, ...],
    fixture_surface_catalog: dict[str, str],
    surface_description: str,
    surface_set_description: str,
) -> None:
    coverage = payload.get("coverage")
    if not isinstance(coverage, list) or not coverage:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                f"{manifest_label} stop-gate manifest coverage must be a non-empty list",
                context={"manifest_path": str(manifest_path)},
            )
        )
    seen_coverage_surfaces: set[str] = set()
    for coverage_index, raw_coverage in enumerate(coverage):
        if not isinstance(raw_coverage, dict):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "coverage entry must be an object",
                    context={"manifest_path": str(manifest_path), "coverage_index": coverage_index},
                )
            )
        surface_id = raw_coverage.get("surface_id")
        if not isinstance(surface_id, str) or surface_id not in frozen_surface_set:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    f"coverage surface_id must be a {surface_description}",
                    context={"manifest_path": str(manifest_path), "coverage_index": coverage_index},
                )
            )
        if surface_id in seen_coverage_surfaces:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "coverage surface_id must be unique",
                    context={"manifest_path": str(manifest_path), "surface_id": surface_id},
                )
            )
        fixture_ids = raw_coverage.get("fixture_ids")
        if not isinstance(fixture_ids, list) or not fixture_ids:
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "coverage fixture_ids must be a non-empty list",
                    context={"manifest_path": str(manifest_path), "surface_id": surface_id},
                )
            )
        normalized_fixture_ids: list[str] = []
        for fixture_id in fixture_ids:
            if not isinstance(fixture_id, str) or not fixture_id:
                raise ValueError(
                    _issue(
                        "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                        "coverage fixture_ids contains invalid fixture id",
                        context={"manifest_path": str(manifest_path), "surface_id": surface_id},
                    )
                )
            normalized_fixture_ids.append(fixture_id)
        if len(set(normalized_fixture_ids)) != len(normalized_fixture_ids):
            raise ValueError(
                _issue(
                    "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                    "coverage fixture_ids must be unique within a surface",
                    context={"manifest_path": str(manifest_path), "surface_id": surface_id},
                )
            )
        for fixture_id in normalized_fixture_ids:
            fixture_surface = fixture_surface_catalog.get(fixture_id)
            if fixture_surface is None:
                raise ValueError(
                    _issue(
                        "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                        "coverage references unknown fixture_id",
                        context={
                            "manifest_path": str(manifest_path),
                            "surface_id": surface_id,
                            "fixture_id": fixture_id,
                        },
                    )
                )
            if fixture_surface != surface_id:
                raise ValueError(
                    _issue(
                        "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                        "coverage fixture_id is mapped to a different surface",
                        context={
                            "manifest_path": str(manifest_path),
                            "surface_id": surface_id,
                            "fixture_id": fixture_id,
                            "fixture_surface_id": fixture_surface,
                        },
                    )
                )
        seen_coverage_surfaces.add(surface_id)

    if seen_coverage_surfaces != frozen_surface_set:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                f"coverage surface set must exactly match {surface_set_description}",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_surfaces": sorted(frozen_surfaces),
                    "observed_surfaces": sorted(seen_coverage_surfaces),
                },
            )
        )


def _recompute_integrity_manifest_hash(
    *,
    payload: dict[str, Any],
    manifest_path: Path,
    manifest_label: str,
) -> str:
    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                f"{manifest_label} stop-gate manifest missing manifest_hash",
                context={"manifest_path": str(manifest_path)},
            )
        )
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH",
                f"{manifest_label} manifest_hash mismatch",
                context={
                    "manifest_path": str(manifest_path),
                    "embedded_manifest_hash": raw_manifest_hash,
                    "recomputed_manifest_hash": recomputed_manifest_hash,
                },
            )
        )
    return recomputed_manifest_hash


def _load_integrity_manifest_payload(
    *,
    manifest_path: Path,
    manifest_label: str,
    manifest_schema: str,
    replay_count: int,
    surface_specs: tuple[_IntegritySurfaceFixtureSpec, ...],
    frozen_surface_set: frozenset[str],
    frozen_surfaces: tuple[str, ...],
    surface_description: str,
    surface_set_description: str,
) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(
        manifest_path,
        description=f"{manifest_label} stop-gate manifest",
    )
    if payload.get("schema") != manifest_schema:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                f"{manifest_label} stop-gate manifest has unsupported schema",
                context={
                    "manifest_path": str(manifest_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    observed_replay_count = payload.get("replay_count")
    if observed_replay_count != replay_count:
        raise ValueError(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                f"{manifest_label} replay_count must match frozen replay count",
                context={
                    "manifest_path": str(manifest_path),
                    "expected_replay_count": replay_count,
                    "observed_replay_count": observed_replay_count,
                },
            )
        )

    fixture_list_keys = tuple(list_key for list_key, _, _, _ in surface_specs)
    _validate_integrity_required_fixture_lists(
        payload=payload,
        manifest_path=manifest_path,
        manifest_label=manifest_label,
        fixture_list_keys=fixture_list_keys,
    )
    for list_key, metric_name, expected_surface_id, required_run_keys in surface_specs:
        _validate_integrity_surface_fixtures(
            fixtures=cast(list[Any], payload[list_key]),
            manifest_path=manifest_path,
            metric_name=metric_name,
            expected_surface_id=expected_surface_id,
            required_run_keys=required_run_keys,
            frozen_surface_set=frozen_surface_set,
            surface_description=surface_description,
        )

    fixture_surface_catalog = _build_integrity_fixture_surface_catalog(
        payload=payload,
        manifest_path=manifest_path,
        manifest_label=manifest_label,
        fixture_list_keys=fixture_list_keys,
    )
    _validate_integrity_coverage(
        payload=payload,
        manifest_path=manifest_path,
        manifest_label=manifest_label,
        frozen_surface_set=frozen_surface_set,
        frozen_surfaces=frozen_surfaces,
        fixture_surface_catalog=fixture_surface_catalog,
        surface_description=surface_description,
        surface_set_description=surface_set_description,
    )
    recomputed_manifest_hash = _recompute_integrity_manifest_hash(
        payload=payload,
        manifest_path=manifest_path,
        manifest_label=manifest_label,
    )
    return payload, recomputed_manifest_hash


def _load_vnext_plus16_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    return _load_integrity_manifest_payload(
        manifest_path=manifest_path,
        manifest_label="vnext+16",
        manifest_schema=VNEXT_PLUS16_MANIFEST_SCHEMA,
        replay_count=VNEXT_PLUS16_REPLAY_COUNT,
        surface_specs=_VNEXT_PLUS16_INTEGRITY_SURFACE_SPECS,
        frozen_surface_set=_FROZEN_INTEGRITY_SURFACE_SET,
        frozen_surfaces=_FROZEN_INTEGRITY_SURFACES,
        surface_description="frozen integrity surface",
        surface_set_description="frozen integrity surfaces",
    )


def _compute_vnext_plus16_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS16_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus16_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS16_DEFAULT_METRICS,
            "vnext_plus16_manifest_hash": "",
        }

    try:
        dangling_reference_fixtures = _manifest_metric_entries(
            metrics={
                "artifact_dangling_reference_determinism_pct": manifest.get(
                    "dangling_reference_fixtures"
                )
            },
            metric_name="artifact_dangling_reference_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        cycle_policy_fixtures = _manifest_metric_entries(
            metrics={
                "artifact_cycle_policy_determinism_pct": manifest.get(
                    "cycle_policy_fixtures"
                )
            },
            metric_name="artifact_cycle_policy_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        deontic_conflict_fixtures = _manifest_metric_entries(
            metrics={
                "artifact_deontic_conflict_determinism_pct": manifest.get(
                    "deontic_conflict_fixtures"
                )
            },
            metric_name="artifact_deontic_conflict_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS16_DEFAULT_METRICS,
            "vnext_plus16_manifest_hash": manifest_hash,
        }

    artifact_dangling_reference_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="artifact_dangling_reference_determinism_pct",
        fixtures=dangling_reference_fixtures,
        replay_count=VNEXT_PLUS16_REPLAY_COUNT,
        required_run_fields=("dangling_reference_path",),
        run_hash_builder=_adeu_integrity_dangling_reference_fixture_hash,
        issues=issues,
        drift_issue_code="URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT",
        drift_issue_message="vnext+16 dangling-reference diagnostic drift",
    )
    artifact_cycle_policy_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="artifact_cycle_policy_determinism_pct",
        fixtures=cycle_policy_fixtures,
        replay_count=VNEXT_PLUS16_REPLAY_COUNT,
        required_run_fields=("cycle_policy_path",),
        run_hash_builder=_adeu_integrity_cycle_policy_fixture_hash,
        issues=issues,
        drift_issue_code="URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT",
        drift_issue_message="vnext+16 cycle-policy diagnostic drift",
    )
    artifact_deontic_conflict_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="artifact_deontic_conflict_determinism_pct",
        fixtures=deontic_conflict_fixtures,
        replay_count=VNEXT_PLUS16_REPLAY_COUNT,
        required_run_fields=("deontic_conflict_path",),
        run_hash_builder=_adeu_integrity_deontic_conflict_fixture_hash,
        issues=issues,
        drift_issue_code="URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT",
        drift_issue_message="vnext+16 deontic-conflict diagnostic drift",
    )

    if not _has_non_zero_diagnostic_fixture(
        manifest_path=resolved_manifest_path,
        fixtures=dangling_reference_fixtures,
        required_run_fields=("dangling_reference_path",),
        run_diagnostic_count_builder=_adeu_integrity_dangling_reference_diagnostic_count,
    ):
        artifact_dangling_reference_determinism_pct = 0.0
        issues.append(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "vnext+16 dangling-reference fixtures must include non-zero diagnostics",
                context={"manifest_path": str(resolved_manifest_path)},
            )
        )
    if not _has_non_zero_diagnostic_fixture(
        manifest_path=resolved_manifest_path,
        fixtures=cycle_policy_fixtures,
        required_run_fields=("cycle_policy_path",),
        run_diagnostic_count_builder=_adeu_integrity_cycle_policy_diagnostic_count,
    ):
        artifact_cycle_policy_determinism_pct = 0.0
        issues.append(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "vnext+16 cycle-policy fixtures must include non-zero diagnostics",
                context={"manifest_path": str(resolved_manifest_path)},
            )
        )
    if not _has_non_zero_diagnostic_fixture(
        manifest_path=resolved_manifest_path,
        fixtures=deontic_conflict_fixtures,
        required_run_fields=("deontic_conflict_path",),
        run_diagnostic_count_builder=_adeu_integrity_deontic_conflict_diagnostic_count,
    ):
        artifact_deontic_conflict_determinism_pct = 0.0
        issues.append(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "vnext+16 deontic-conflict fixtures must include non-zero diagnostics",
                context={"manifest_path": str(resolved_manifest_path)},
            )
        )

    return {
        "artifact_dangling_reference_determinism_pct": (
            artifact_dangling_reference_determinism_pct
        ),
        "artifact_cycle_policy_determinism_pct": artifact_cycle_policy_determinism_pct,
        "artifact_deontic_conflict_determinism_pct": (
            artifact_deontic_conflict_determinism_pct
        ),
        "vnext_plus16_manifest_hash": manifest_hash,
    }


def _load_vnext_plus17_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    return _load_integrity_manifest_payload(
        manifest_path=manifest_path,
        manifest_label="vnext+17",
        manifest_schema=VNEXT_PLUS17_MANIFEST_SCHEMA,
        replay_count=VNEXT_PLUS17_REPLAY_COUNT,
        surface_specs=_VNEXT_PLUS17_INTEGRITY_SURFACE_SPECS,
        frozen_surface_set=_FROZEN_INTEGRITY_EXTENDED_SURFACE_SET,
        frozen_surfaces=_FROZEN_INTEGRITY_EXTENDED_SURFACES,
        surface_description="frozen integrity extended surface",
        surface_set_description="frozen integrity extended surfaces",
    )


def _compute_vnext_plus17_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS17_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus17_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS17_DEFAULT_METRICS,
            "vnext_plus17_manifest_hash": "",
            "vnext_plus17_fixture_count_total": 0,
            "vnext_plus17_replay_count_total": 0,
        }

    try:
        reference_integrity_extended_fixtures = _manifest_metric_entries(
            metrics={
                "artifact_reference_integrity_extended_determinism_pct": manifest.get(
                    "reference_integrity_extended_fixtures"
                )
            },
            metric_name="artifact_reference_integrity_extended_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        cycle_policy_extended_fixtures = _manifest_metric_entries(
            metrics={
                "artifact_cycle_policy_extended_determinism_pct": manifest.get(
                    "cycle_policy_extended_fixtures"
                )
            },
            metric_name="artifact_cycle_policy_extended_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
        deontic_conflict_extended_fixtures = _manifest_metric_entries(
            metrics={
                "artifact_deontic_conflict_extended_determinism_pct": manifest.get(
                    "deontic_conflict_extended_fixtures"
                )
            },
            metric_name="artifact_deontic_conflict_extended_determinism_pct",
            manifest_path=resolved_manifest_path,
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS17_DEFAULT_METRICS,
            "vnext_plus17_manifest_hash": manifest_hash,
            "vnext_plus17_fixture_count_total": 0,
            "vnext_plus17_replay_count_total": 0,
        }

    artifact_reference_integrity_extended_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="artifact_reference_integrity_extended_determinism_pct",
        fixtures=reference_integrity_extended_fixtures,
        replay_count=VNEXT_PLUS17_REPLAY_COUNT,
        required_run_fields=("reference_integrity_extended_path",),
        run_hash_builder=_adeu_integrity_reference_integrity_extended_fixture_hash,
        issues=issues,
        drift_issue_code="URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT",
        drift_issue_message="vnext+17 reference-integrity extended diagnostic drift",
    )
    artifact_cycle_policy_extended_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="artifact_cycle_policy_extended_determinism_pct",
        fixtures=cycle_policy_extended_fixtures,
        replay_count=VNEXT_PLUS17_REPLAY_COUNT,
        required_run_fields=("cycle_policy_extended_path",),
        run_hash_builder=_adeu_integrity_cycle_policy_extended_fixture_hash,
        issues=issues,
        drift_issue_code="URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT",
        drift_issue_message="vnext+17 cycle-policy extended diagnostic drift",
    )
    artifact_deontic_conflict_extended_determinism_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="artifact_deontic_conflict_extended_determinism_pct",
        fixtures=deontic_conflict_extended_fixtures,
        replay_count=VNEXT_PLUS17_REPLAY_COUNT,
        required_run_fields=("deontic_conflict_extended_path",),
        run_hash_builder=_adeu_integrity_deontic_conflict_extended_fixture_hash,
        issues=issues,
        drift_issue_code="URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT",
        drift_issue_message="vnext+17 deontic-conflict extended diagnostic drift",
    )

    if not _has_non_zero_diagnostic_fixture(
        manifest_path=resolved_manifest_path,
        fixtures=reference_integrity_extended_fixtures,
        required_run_fields=("reference_integrity_extended_path",),
        run_diagnostic_count_builder=_adeu_integrity_reference_integrity_extended_diagnostic_count,
    ):
        artifact_reference_integrity_extended_determinism_pct = 0.0
        issues.append(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "vnext+17 reference-integrity extended fixtures must include non-zero diagnostics",
                context={"manifest_path": str(resolved_manifest_path)},
            )
        )
    if not _has_non_zero_diagnostic_fixture(
        manifest_path=resolved_manifest_path,
        fixtures=cycle_policy_extended_fixtures,
        required_run_fields=("cycle_policy_extended_path",),
        run_diagnostic_count_builder=_adeu_integrity_cycle_policy_extended_diagnostic_count,
    ):
        artifact_cycle_policy_extended_determinism_pct = 0.0
        issues.append(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "vnext+17 cycle-policy extended fixtures must include non-zero diagnostics",
                context={"manifest_path": str(resolved_manifest_path)},
            )
        )
    if not _has_non_zero_diagnostic_fixture(
        manifest_path=resolved_manifest_path,
        fixtures=deontic_conflict_extended_fixtures,
        required_run_fields=("deontic_conflict_extended_path",),
        run_diagnostic_count_builder=_adeu_integrity_deontic_conflict_extended_diagnostic_count,
    ):
        artifact_deontic_conflict_extended_determinism_pct = 0.0
        issues.append(
            _issue(
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                "vnext+17 deontic-conflict extended fixtures must include non-zero diagnostics",
                context={"manifest_path": str(resolved_manifest_path)},
            )
        )

    fixture_count_total = (
        len(reference_integrity_extended_fixtures)
        + len(cycle_policy_extended_fixtures)
        + len(deontic_conflict_extended_fixtures)
    )
    replay_count_total = sum(
        len(cast(list[Any], fixture.get("runs", [])))
        for fixture in reference_integrity_extended_fixtures
    ) + sum(
        len(cast(list[Any], fixture.get("runs", [])))
        for fixture in cycle_policy_extended_fixtures
    ) + sum(
        len(cast(list[Any], fixture.get("runs", [])))
        for fixture in deontic_conflict_extended_fixtures
    )

    return {
        "artifact_reference_integrity_extended_determinism_pct": (
            artifact_reference_integrity_extended_determinism_pct
        ),
        "artifact_cycle_policy_extended_determinism_pct": (
            artifact_cycle_policy_extended_determinism_pct
        ),
        "artifact_deontic_conflict_extended_determinism_pct": (
            artifact_deontic_conflict_extended_determinism_pct
        ),
        "vnext_plus17_manifest_hash": manifest_hash,
        "vnext_plus17_fixture_count_total": fixture_count_total,
        "vnext_plus17_replay_count_total": replay_count_total,
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


def _runtime_observability_payload(
    *,
    total_fixtures: int,
    total_replays: int,
    runtime_started: float,
) -> dict[str, int]:
    return {
        "total_fixtures": int(total_fixtures),
        "total_replays": int(total_replays),
        "elapsed_ms": max(0, int(round((time.monotonic() - runtime_started) * 1000.0))),
    }


def _runtime_budget_metric_pct(
    *,
    runtime_observability: Mapping[str, Any],
) -> tuple[float, dict[str, Any] | None]:
    elapsed_ms = runtime_observability.get("elapsed_ms")
    if not isinstance(elapsed_ms, int):
        return (
            0.0,
            _issue(
                "URM_ADEU_TOOLING_CI_BUDGET_INVALID",
                "runtime_observability elapsed_ms must be an integer",
                context={"field": "elapsed_ms"},
            ),
        )
    if elapsed_ms <= VNEXT_PLUS18_CI_BUDGET_CEILING_MS:
        return 100.0, None
    return (
        0.0,
        _issue(
            "URM_ADEU_TOOLING_RUNTIME_BUDGET_EXCEEDED",
            "stop-gate runtime budget exceeded frozen ceiling",
            context={
                "elapsed_ms": elapsed_ms,
                "ceiling_ms": VNEXT_PLUS18_CI_BUDGET_CEILING_MS,
            },
        ),
    )


def _tooling_parity_hash_projection(payload: Mapping[str, Any]) -> dict[str, Any]:
    projected = dict(payload)
    projected.pop("runtime_observability", None)
    return projected


def _read_tooling_parity_payload(
    *,
    path: Path,
    description: str,
    invalid_code: str,
) -> dict[str, Any]:
    try:
        return _read_json_object(path, description=description)
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            invalid_code,
            str(exc),
            context={"path": str(path)},
        )
        issue = _map_issue_code(
            issue,
            code_map={"URM_STOP_GATE_INPUT_INVALID": invalid_code},
        )
        raise ValueError(issue) from exc


def _tooling_parity_fixture_hash(
    *,
    baseline_path: Path,
    candidate_path: Path,
    invalid_code: str,
    drift_message: str,
) -> str:
    baseline_payload = _read_tooling_parity_payload(
        path=baseline_path,
        description="tooling parity baseline artifact",
        invalid_code=invalid_code,
    )
    candidate_payload = _read_tooling_parity_payload(
        path=candidate_path,
        description="tooling parity candidate artifact",
        invalid_code=invalid_code,
    )
    baseline_schema = baseline_payload.get("schema")
    candidate_schema = candidate_payload.get("schema")
    if not isinstance(baseline_schema, str) or not isinstance(candidate_schema, str):
        raise ValueError(
            _issue(
                invalid_code,
                "tooling parity artifacts must contain schema field",
                context={
                    "baseline_path": str(baseline_path),
                    "candidate_path": str(candidate_path),
                },
            )
        )
    if baseline_schema != candidate_schema:
        raise ValueError(
            _issue(
                "URM_ADEU_TOOLING_FIXTURE_INVALID",
                "tooling parity fixture baseline/candidate schema mismatch",
                context={
                    "baseline_path": str(baseline_path),
                    "candidate_path": str(candidate_path),
                    "baseline_schema": baseline_schema,
                    "candidate_schema": candidate_schema,
                },
            )
        )

    baseline_hash = sha256_canonical_json(_tooling_parity_hash_projection(baseline_payload))
    candidate_hash = sha256_canonical_json(_tooling_parity_hash_projection(candidate_payload))
    if baseline_hash != candidate_hash:
        raise ValueError(
            _issue(
                "URM_ADEU_TOOLING_PARITY_DRIFT",
                drift_message,
                context={
                    "baseline_path": str(baseline_path),
                    "candidate_path": str(candidate_path),
                    "schema": baseline_schema,
                },
            )
        )
    return candidate_hash


def _tooling_validation_parity_fixture_hash(
    *,
    baseline_path: Path,
    candidate_path: Path,
) -> str:
    return _tooling_parity_fixture_hash(
        baseline_path=baseline_path,
        candidate_path=candidate_path,
        invalid_code="URM_ADEU_TOOLING_VALIDATION_PARITY_INVALID",
        drift_message="vnext+18 validation consolidation parity drift",
    )


def _tooling_transfer_report_parity_fixture_hash(
    *,
    baseline_path: Path,
    candidate_path: Path,
) -> str:
    return _tooling_parity_fixture_hash(
        baseline_path=baseline_path,
        candidate_path=candidate_path,
        invalid_code="URM_ADEU_TOOLING_TRANSFER_REPORT_PARITY_INVALID",
        drift_message="vnext+18 transfer-report consolidation parity drift",
    )


def _validate_vnext_plus18_ci_budget_report_payload(
    *,
    report_payload: Mapping[str, Any],
    report_path: Path,
    manifest_path: Path,
    fixture_id: str,
    issues: list[dict[str, Any]],
) -> bool:
    if report_payload.get("schema") != STOP_GATE_SCHEMA:
        issues.append(
            _issue(
                "URM_ADEU_TOOLING_CI_BUDGET_INVALID",
                "vnext+18 ci-budget evidence report must use stop_gate_metrics@1 schema",
                context={
                    "manifest_path": str(manifest_path),
                    "fixture_id": fixture_id,
                    "path": str(report_path),
                    "schema": report_payload.get("schema"),
                },
            )
        )
        return False
    runtime_observability = report_payload.get("runtime_observability")
    if not isinstance(runtime_observability, dict):
        issues.append(
            _issue(
                "URM_ADEU_TOOLING_CI_BUDGET_INVALID",
                "vnext+18 ci-budget evidence report missing runtime_observability object",
                context={
                    "manifest_path": str(manifest_path),
                    "fixture_id": fixture_id,
                    "path": str(report_path),
                },
            )
        )
        return False
    for field in ("total_fixtures", "total_replays", "elapsed_ms"):
        value = runtime_observability.get(field)
        if not isinstance(value, int) or value < 0:
            issues.append(
                _issue(
                    "URM_ADEU_TOOLING_CI_BUDGET_INVALID",
                    (
                        "vnext+18 ci-budget evidence runtime_observability fields "
                        "must be non-negative integers"
                    ),
                    context={
                        "manifest_path": str(manifest_path),
                        "fixture_id": fixture_id,
                        "path": str(report_path),
                        "field": field,
                    },
                )
            )
            return False
    return True


def _validate_vnext_plus18_ci_budget_evidence(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
    issues: list[dict[str, Any]],
) -> bool:
    if len(fixtures) != 1:
        issues.append(
            _issue(
                "URM_ADEU_TOOLING_FIXTURE_INVALID",
                "vnext+18 ci_budget_fixtures must contain exactly one fixture entry",
                context={
                    "manifest_path": str(manifest_path),
                    "observed_fixture_count": len(fixtures),
                    "expected_fixture_count": 1,
                },
            )
        )
        return False

    fixture = fixtures[0]
    fixture_id = fixture.get("fixture_id")
    if not isinstance(fixture_id, str) or not fixture_id:
        fixture_id = "vnext_plus18_ci_budget_fixture"
    runs = fixture.get("runs")
    if not isinstance(runs, list) or len(runs) != 1:
        issues.append(
            _issue(
                "URM_ADEU_TOOLING_FIXTURE_INVALID",
                "vnext+18 ci_budget fixture must contain exactly one run entry",
                context={
                    "manifest_path": str(manifest_path),
                    "fixture_id": fixture_id,
                    "observed_run_count": 0 if not isinstance(runs, list) else len(runs),
                    "expected_run_count": 1,
                },
            )
        )
        return False
    run = runs[0]
    if not isinstance(run, dict):
        issues.append(
            _issue(
                "URM_ADEU_TOOLING_FIXTURE_INVALID",
                "vnext+18 ci_budget run entry must be an object",
                context={
                    "manifest_path": str(manifest_path),
                    "fixture_id": fixture_id,
                    "run_index": 0,
                },
            )
        )
        return False
    try:
        report_path = _resolve_manifest_relative_path(
            manifest_path=manifest_path,
            raw_path=run.get("report_path"),
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_TOOLING_FIXTURE_INVALID",
            str(exc),
            context={"manifest_path": str(manifest_path), "fixture_id": fixture_id},
        )
        issue = _map_issue_code(
            issue,
            code_map={"URM_STOP_GATE_INPUT_INVALID": "URM_ADEU_TOOLING_FIXTURE_INVALID"},
        )
        issues.append(
            _issue_with_context(
                issue,
                context={"manifest_path": str(manifest_path), "fixture_id": fixture_id},
            )
        )
        return False
    try:
        report_payload = _read_json_object(
            report_path,
            description="vnext+18 ci-budget evidence report",
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_TOOLING_CI_BUDGET_INVALID",
            str(exc),
            context={"path": str(report_path)},
        )
        issue = _map_issue_code(
            issue,
            code_map={"URM_STOP_GATE_INPUT_INVALID": "URM_ADEU_TOOLING_CI_BUDGET_INVALID"},
        )
        issues.append(
            _issue_with_context(
                issue,
                context={"manifest_path": str(manifest_path), "fixture_id": fixture_id},
            )
        )
        return False

    return _validate_vnext_plus18_ci_budget_report_payload(
        report_payload=report_payload,
        report_path=report_path,
        manifest_path=manifest_path,
        fixture_id=fixture_id,
        issues=issues,
    )


def _load_vnext_plus18_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    try:
        return _load_integrity_manifest_payload(
            manifest_path=manifest_path,
            manifest_label="vnext+18",
            manifest_schema=VNEXT_PLUS18_MANIFEST_SCHEMA,
            replay_count=VNEXT_PLUS18_REPLAY_COUNT,
            surface_specs=_VNEXT_PLUS18_TOOLING_SURFACE_SPECS,
            frozen_surface_set=_FROZEN_TOOLING_SURFACE_SET,
            frozen_surfaces=_FROZEN_TOOLING_SURFACES,
            surface_description="frozen tooling surface",
            surface_set_description="frozen tooling surfaces",
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_TOOLING_FIXTURE_INVALID",
            str(exc),
        )
        issue = _map_issue_code(
            issue,
            code_map={
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID": "URM_ADEU_TOOLING_FIXTURE_INVALID",
                "URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH": (
                    "URM_ADEU_TOOLING_MANIFEST_HASH_MISMATCH"
                ),
            },
        )
        raise ValueError(issue) from exc


def _compute_vnext_plus18_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS18_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus18_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_TOOLING_FIXTURE_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS18_DEFAULT_METRICS,
            "vnext_plus18_manifest_hash": "",
            "vnext_plus18_fixture_count_total": 0,
            "vnext_plus18_replay_count_total": 0,
            "vnext_plus18_ci_budget_evidence_valid": False,
        }

    validation_parity_fixtures = cast(list[dict[str, Any]], manifest["validation_parity_fixtures"])
    transfer_report_parity_fixtures = cast(
        list[dict[str, Any]], manifest["transfer_report_parity_fixtures"]
    )
    ci_budget_fixtures = cast(list[dict[str, Any]], manifest["ci_budget_fixtures"])

    artifact_validation_consolidation_parity_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="artifact_validation_consolidation_parity_pct",
        fixtures=validation_parity_fixtures,
        replay_count=VNEXT_PLUS18_REPLAY_COUNT,
        required_run_fields=("baseline_path", "candidate_path"),
        run_hash_builder=_tooling_validation_parity_fixture_hash,
        issues=issues,
        invalid_issue_code="URM_ADEU_TOOLING_FIXTURE_INVALID",
        drift_issue_code="URM_ADEU_TOOLING_PARITY_DRIFT",
        drift_issue_message="vnext+18 validation consolidation parity drift",
    )
    artifact_transfer_report_consolidation_parity_pct = _manifest_metric_pct(
        manifest_path=resolved_manifest_path,
        metric_name="artifact_transfer_report_consolidation_parity_pct",
        fixtures=transfer_report_parity_fixtures,
        replay_count=VNEXT_PLUS18_REPLAY_COUNT,
        required_run_fields=("baseline_path", "candidate_path"),
        run_hash_builder=_tooling_transfer_report_parity_fixture_hash,
        issues=issues,
        invalid_issue_code="URM_ADEU_TOOLING_FIXTURE_INVALID",
        drift_issue_code="URM_ADEU_TOOLING_PARITY_DRIFT",
        drift_issue_message="vnext+18 transfer-report consolidation parity drift",
    )
    ci_budget_evidence_valid = _validate_vnext_plus18_ci_budget_evidence(
        manifest_path=resolved_manifest_path,
        fixtures=ci_budget_fixtures,
        issues=issues,
    )

    fixture_count_total = (
        len(validation_parity_fixtures)
        + len(transfer_report_parity_fixtures)
        + len(ci_budget_fixtures)
    )
    replay_count_total = sum(
        len(cast(list[Any], fixture.get("runs", [])))
        for fixture in (
            *validation_parity_fixtures,
            *transfer_report_parity_fixtures,
            *ci_budget_fixtures,
        )
    )

    return {
        "artifact_validation_consolidation_parity_pct": (
            artifact_validation_consolidation_parity_pct
        ),
        "artifact_transfer_report_consolidation_parity_pct": (
            artifact_transfer_report_consolidation_parity_pct
        ),
        "vnext_plus18_manifest_hash": manifest_hash,
        "vnext_plus18_fixture_count_total": fixture_count_total,
        "vnext_plus18_replay_count_total": replay_count_total,
        "vnext_plus18_ci_budget_evidence_valid": ci_budget_evidence_valid,
    }


def _strip_created_at_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for key in sorted(value.keys()):
            key_str = str(key)
            if key_str == "created_at":
                continue
            normalized[key_str] = _strip_created_at_fields(value[key])
        return normalized
    if isinstance(value, list):
        return [_strip_created_at_fields(item) for item in value]
    return value


def _read_surface_projection_hash(payload: Mapping[str, Any]) -> str:
    return sha256_canonical_json(_strip_created_at_fields(payload))


def _validate_read_surface_envelope_keys(
    *,
    payload: Mapping[str, Any],
    required_keys: set[str],
    optional_keys: set[str],
    path: Path,
    context: Mapping[str, Any] | None = None,
) -> None:
    observed_keys = {str(key) for key in payload.keys()}
    missing_keys = sorted(required_keys - observed_keys)
    unexpected_keys = sorted(observed_keys - (required_keys | optional_keys))
    if missing_keys or unexpected_keys:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "read-surface capture envelope has unexpected key shape",
                context={
                    "path": str(path),
                    "missing_keys": missing_keys,
                    "unexpected_keys": unexpected_keys,
                    **dict(context or {}),
                },
            )
        )


def _validate_read_surface_response_payload(
    *,
    response_payload: Any,
    expected_schema: str,
    expected_payload_field: str,
    expected_artifact_id: str | None,
    path: Path,
    context: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if not isinstance(response_payload, dict):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "read-surface response payload must be an object",
                context={"path": str(path), **dict(context or {})},
            )
        )
    _validate_read_surface_envelope_keys(
        payload=response_payload,
        required_keys={"artifact_id", "schema", expected_payload_field},
        optional_keys={"created_at"},
        path=path,
        context=context,
    )
    artifact_id = response_payload.get("artifact_id")
    if not isinstance(artifact_id, str) or not artifact_id:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "read-surface response artifact_id must be a non-empty string",
                context={"path": str(path), **dict(context or {})},
            )
        )
    if expected_artifact_id is not None and artifact_id != expected_artifact_id:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "read-surface response artifact_id does not match capture artifact_id",
                context={
                    "path": str(path),
                    "expected_artifact_id": expected_artifact_id,
                    "observed_artifact_id": artifact_id,
                    **dict(context or {}),
                },
            )
        )
    schema = response_payload.get("schema")
    if schema != expected_schema:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "read-surface response schema is invalid",
                context={
                    "path": str(path),
                    "expected_schema": expected_schema,
                    "observed_schema": schema,
                    **dict(context or {}),
                },
            )
        )
    created_at = response_payload.get("created_at")
    if "created_at" in response_payload and created_at is not None and not isinstance(
        created_at, str
    ):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "read-surface response created_at must be a string when present",
                context={"path": str(path), **dict(context or {})},
            )
        )
    nested_payload = response_payload.get(expected_payload_field)
    if not isinstance(nested_payload, dict):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "read-surface response payload field must be an object",
                context={
                    "path": str(path),
                    "payload_field": expected_payload_field,
                    **dict(context or {}),
                },
            )
        )
    nested_schema = nested_payload.get("schema")
    if nested_schema != expected_schema:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "read-surface nested payload schema is invalid",
                context={
                    "path": str(path),
                    "payload_field": expected_payload_field,
                    "expected_schema": expected_schema,
                    "observed_schema": nested_schema,
                    **dict(context or {}),
                },
            )
        )
    return response_payload


def _read_surface_core_ir_fixture_hash(*, core_ir_read_surface_path: Path) -> str:
    payload = _read_json_object(
        core_ir_read_surface_path,
        description="core-ir read-surface response fixture",
    )
    _validate_read_surface_response_payload(
        response_payload=payload,
        expected_schema=ADEU_CORE_IR_SCHEMA,
        expected_payload_field="core_ir",
        expected_artifact_id=None,
        path=core_ir_read_surface_path,
    )
    return _read_surface_projection_hash(payload)


def _read_surface_lane_capture_fixture_hash(*, lane_read_surface_path: Path) -> str:
    payload = _read_json_object(
        lane_read_surface_path,
        description="lane read-surface capture fixture",
    )
    _validate_read_surface_envelope_keys(
        payload=payload,
        required_keys={"schema", "artifact_id", "captures"},
        optional_keys=set(),
        path=lane_read_surface_path,
    )
    if payload.get("schema") != _READ_SURFACE_LANE_CAPTURE_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "lane read-surface capture uses unsupported schema",
                context={
                    "path": str(lane_read_surface_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    artifact_id = payload.get("artifact_id")
    if not isinstance(artifact_id, str) or not artifact_id:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "lane read-surface capture artifact_id must be a non-empty string",
                context={"path": str(lane_read_surface_path)},
            )
        )
    captures = payload.get("captures")
    if not isinstance(captures, list) or len(captures) != 2:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "lane read-surface capture must include exactly two endpoint captures",
                context={"path": str(lane_read_surface_path)},
            )
        )
    expected_captures: tuple[tuple[str, str, str], ...] = (
        (
            f"/urm/core-ir/artifacts/{artifact_id}/lane-projection",
            ADEU_LANE_PROJECTION_SCHEMA,
            "lane_projection",
        ),
        (
            f"/urm/core-ir/artifacts/{artifact_id}/lane-report",
            ADEU_LANE_REPORT_SCHEMA,
            "lane_report",
        ),
    )
    for capture_index, expected in enumerate(expected_captures):
        expected_path, expected_schema, expected_field = expected
        capture = captures[capture_index]
        if not isinstance(capture, dict):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "lane read-surface capture entry must be an object",
                    context={
                        "path": str(lane_read_surface_path),
                        "capture_index": capture_index,
                    },
                )
            )
        _validate_read_surface_envelope_keys(
            payload=capture,
            required_keys={"method", "path", "response"},
            optional_keys=set(),
            path=lane_read_surface_path,
            context={"capture_index": capture_index},
        )
        if capture.get("method") != "GET":
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "lane read-surface capture method must be GET",
                    context={
                        "path": str(lane_read_surface_path),
                        "capture_index": capture_index,
                        "method": capture.get("method"),
                    },
                )
            )
        if capture.get("path") != expected_path:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "lane read-surface capture path is invalid",
                    context={
                        "path": str(lane_read_surface_path),
                        "capture_index": capture_index,
                        "expected_path": expected_path,
                        "observed_path": capture.get("path"),
                    },
                )
            )
        _validate_read_surface_response_payload(
            response_payload=capture.get("response"),
            expected_schema=expected_schema,
            expected_payload_field=expected_field,
            expected_artifact_id=artifact_id,
            path=lane_read_surface_path,
            context={
                "capture_index": capture_index,
                "capture_path": expected_path,
            },
        )
    return _read_surface_projection_hash(payload)


def _read_surface_integrity_capture_fixture_hash(
    *, integrity_read_surface_path: Path
) -> str:
    payload = _read_json_object(
        integrity_read_surface_path,
        description="integrity read-surface capture fixture",
    )
    _validate_read_surface_envelope_keys(
        payload=payload,
        required_keys={"schema", "artifact_id", "captures"},
        optional_keys=set(),
        path=integrity_read_surface_path,
    )
    if payload.get("schema") != _READ_SURFACE_INTEGRITY_CAPTURE_SCHEMA:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "integrity read-surface capture uses unsupported schema",
                context={
                    "path": str(integrity_read_surface_path),
                    "schema": payload.get("schema"),
                },
            )
        )
    artifact_id = payload.get("artifact_id")
    if not isinstance(artifact_id, str) or not artifact_id:
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "integrity read-surface capture artifact_id must be a non-empty string",
                context={"path": str(integrity_read_surface_path)},
            )
        )
    captures = payload.get("captures")
    if not isinstance(captures, list) or len(captures) != len(
        _FROZEN_READ_SURFACE_INTEGRITY_FAMILIES
    ):
        raise ValueError(
            _issue(
                "URM_STOP_GATE_INPUT_INVALID",
                "integrity read-surface capture must include one capture per frozen family",
                context={
                    "path": str(integrity_read_surface_path),
                    "expected_family_count": len(_FROZEN_READ_SURFACE_INTEGRITY_FAMILIES),
                    "observed_family_count": (
                        len(captures) if isinstance(captures, list) else None
                    ),
                },
            )
        )
    for capture_index, expected_family in enumerate(_FROZEN_READ_SURFACE_INTEGRITY_FAMILIES):
        capture = captures[capture_index]
        if not isinstance(capture, dict):
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "integrity read-surface capture entry must be an object",
                    context={
                        "path": str(integrity_read_surface_path),
                        "capture_index": capture_index,
                    },
                )
            )
        _validate_read_surface_envelope_keys(
            payload=capture,
            required_keys={"family", "method", "path", "response"},
            optional_keys=set(),
            path=integrity_read_surface_path,
            context={"capture_index": capture_index},
        )
        if capture.get("family") != expected_family:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "integrity read-surface capture family order is invalid",
                    context={
                        "path": str(integrity_read_surface_path),
                        "capture_index": capture_index,
                        "expected_family": expected_family,
                        "observed_family": capture.get("family"),
                    },
                )
            )
        if capture.get("method") != "GET":
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "integrity read-surface capture method must be GET",
                    context={
                        "path": str(integrity_read_surface_path),
                        "capture_index": capture_index,
                        "method": capture.get("method"),
                    },
                )
            )
        expected_path = f"/urm/core-ir/artifacts/{artifact_id}/integrity/{expected_family}"
        if capture.get("path") != expected_path:
            raise ValueError(
                _issue(
                    "URM_STOP_GATE_INPUT_INVALID",
                    "integrity read-surface capture path is invalid",
                    context={
                        "path": str(integrity_read_surface_path),
                        "capture_index": capture_index,
                        "expected_path": expected_path,
                        "observed_path": capture.get("path"),
                    },
                )
            )
        expected_schema = _READ_SURFACE_INTEGRITY_FAMILY_TO_SCHEMA[expected_family]
        _validate_read_surface_response_payload(
            response_payload=capture.get("response"),
            expected_schema=expected_schema,
            expected_payload_field="integrity_artifact",
            expected_artifact_id=artifact_id,
            path=integrity_read_surface_path,
            context={
                "capture_index": capture_index,
                "family": expected_family,
                "capture_path": expected_path,
            },
        )
    return _read_surface_projection_hash(payload)


def _load_vnext_plus19_manifest_payload(
    *,
    manifest_path: Path,
) -> tuple[dict[str, Any], str]:
    try:
        return _load_integrity_manifest_payload(
            manifest_path=manifest_path,
            manifest_label="vnext+19",
            manifest_schema=VNEXT_PLUS19_MANIFEST_SCHEMA,
            replay_count=VNEXT_PLUS19_REPLAY_COUNT,
            surface_specs=_VNEXT_PLUS19_READ_SURFACE_SPECS,
            frozen_surface_set=_FROZEN_READ_SURFACE_SURFACE_SET,
            frozen_surfaces=_FROZEN_READ_SURFACE_SURFACES,
            surface_description="frozen read-surface id",
            surface_set_description="frozen read-surface ids",
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_READ_SURFACE_FIXTURE_INVALID",
            str(exc),
        )
        issue = _map_issue_code(
            issue,
            code_map={
                "URM_STOP_GATE_INPUT_INVALID": "URM_ADEU_READ_SURFACE_FIXTURE_INVALID",
                "URM_ADEU_INTEGRITY_FIXTURE_INVALID": "URM_ADEU_READ_SURFACE_FIXTURE_INVALID",
                "URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH": (
                    "URM_ADEU_READ_SURFACE_MANIFEST_HASH_MISMATCH"
                ),
            },
        )
        raise ValueError(issue) from exc


def _compute_vnext_plus19_metrics(
    *,
    manifest_path: Path | None,
    issues: list[dict[str, Any]],
) -> dict[str, Any]:
    resolved_manifest_path = (
        manifest_path if manifest_path is not None else VNEXT_PLUS19_MANIFEST_PATH
    )
    try:
        manifest, manifest_hash = _load_vnext_plus19_manifest_payload(
            manifest_path=resolved_manifest_path
        )
    except ValueError as exc:
        issue = exc.args[0] if exc.args and isinstance(exc.args[0], dict) else _issue(
            "URM_ADEU_READ_SURFACE_FIXTURE_INVALID",
            str(exc),
        )
        issues.append(issue)
        return {
            **VNEXT_PLUS19_DEFAULT_METRICS,
            "vnext_plus19_manifest_hash": "",
            "vnext_plus19_fixture_count_total": 0,
            "vnext_plus19_replay_count_total": 0,
        }

    surface_hash_builders: dict[str, Callable[..., Any]] = {
        "core_ir_read_surface_fixtures": _read_surface_core_ir_fixture_hash,
        "lane_read_surface_fixtures": _read_surface_lane_capture_fixture_hash,
        "integrity_read_surface_fixtures": _read_surface_integrity_capture_fixture_hash,
    }
    surface_drift_messages = {
        "core_ir_read_surface_fixtures": "vnext+19 core-ir read-surface diagnostic drift",
        "lane_read_surface_fixtures": "vnext+19 lane read-surface diagnostic drift",
        "integrity_read_surface_fixtures": "vnext+19 integrity read-surface diagnostic drift",
    }

    metric_values: dict[str, float] = {}
    fixture_groups: list[list[dict[str, Any]]] = []
    for fixture_key, metric_name, _surface_id, required_run_fields in (
        _VNEXT_PLUS19_READ_SURFACE_SPECS
    ):
        fixtures = cast(list[dict[str, Any]], manifest[fixture_key])
        fixture_groups.append(fixtures)
        metric_values[metric_name] = _manifest_metric_pct(
            manifest_path=resolved_manifest_path,
            metric_name=metric_name,
            fixtures=fixtures,
            replay_count=VNEXT_PLUS19_REPLAY_COUNT,
            required_run_fields=required_run_fields,
            run_hash_builder=surface_hash_builders[fixture_key],
            issues=issues,
            invalid_issue_code="URM_ADEU_READ_SURFACE_FIXTURE_INVALID",
            drift_issue_code="URM_ADEU_READ_SURFACE_DIAGNOSTIC_DRIFT",
            drift_issue_message=surface_drift_messages[fixture_key],
        )

    fixture_count_total = sum(len(fixtures) for fixtures in fixture_groups)
    replay_count_total = sum(
        len(cast(list[Any], fixture.get("runs", [])))
        for fixtures in fixture_groups
        for fixture in fixtures
    )

    return {
        **metric_values,
        "vnext_plus19_manifest_hash": manifest_hash,
        "vnext_plus19_fixture_count_total": fixture_count_total,
        "vnext_plus19_replay_count_total": replay_count_total,
    }


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
    vnext_plus14_manifest_path: Path | None = None,
    vnext_plus15_manifest_path: Path | None = None,
    vnext_plus16_manifest_path: Path | None = None,
    vnext_plus17_manifest_path: Path | None = None,
    vnext_plus18_manifest_path: Path | None = None,
    vnext_plus19_manifest_path: Path | None = None,
) -> dict[str, Any]:
    runtime_started = time.monotonic()
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
            "runtime_observability": _runtime_observability_payload(
                total_fixtures=0,
                total_replays=0,
                runtime_started=runtime_started,
            ),
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
    vnext_plus14_metrics = _compute_vnext_plus14_metrics(
        manifest_path=vnext_plus14_manifest_path,
        issues=issues,
    )
    vnext_plus15_metrics = _compute_vnext_plus15_metrics(
        manifest_path=vnext_plus15_manifest_path,
        issues=issues,
    )
    vnext_plus16_metrics = _compute_vnext_plus16_metrics(
        manifest_path=vnext_plus16_manifest_path,
        issues=issues,
    )
    vnext_plus17_metrics = _compute_vnext_plus17_metrics(
        manifest_path=vnext_plus17_manifest_path,
        issues=issues,
    )
    vnext_plus18_metrics = _compute_vnext_plus18_metrics(
        manifest_path=vnext_plus18_manifest_path,
        issues=issues,
    )
    vnext_plus19_metrics = _compute_vnext_plus19_metrics(
        manifest_path=vnext_plus19_manifest_path,
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

    runtime_observability = _runtime_observability_payload(
        total_fixtures=int(vnext_plus19_metrics["vnext_plus19_fixture_count_total"]),
        total_replays=int(vnext_plus19_metrics["vnext_plus19_replay_count_total"]),
        runtime_started=runtime_started,
    )
    runtime_budget_metric_pct, runtime_budget_issue = _runtime_budget_metric_pct(
        runtime_observability=runtime_observability,
    )
    if runtime_budget_issue is not None:
        issues.append(runtime_budget_issue)
    if not bool(vnext_plus18_metrics["vnext_plus18_ci_budget_evidence_valid"]):
        runtime_budget_metric_pct = 0.0

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
        "provider_route_contract_parity_pct": vnext_plus14_metrics[
            "provider_route_contract_parity_pct"
        ],
        "codex_candidate_contract_valid_pct": vnext_plus14_metrics[
            "codex_candidate_contract_valid_pct"
        ],
        "provider_parity_replay_determinism_pct": vnext_plus14_metrics[
            "provider_parity_replay_determinism_pct"
        ],
        "adeu_lane_report_replay_determinism_pct": vnext_plus15_metrics[
            "adeu_lane_report_replay_determinism_pct"
        ],
        "adeu_projection_alignment_determinism_pct": vnext_plus15_metrics[
            "adeu_projection_alignment_determinism_pct"
        ],
        "adeu_depth_report_replay_determinism_pct": vnext_plus15_metrics[
            "adeu_depth_report_replay_determinism_pct"
        ],
        "artifact_dangling_reference_determinism_pct": vnext_plus16_metrics[
            "artifact_dangling_reference_determinism_pct"
        ],
        "artifact_cycle_policy_determinism_pct": vnext_plus16_metrics[
            "artifact_cycle_policy_determinism_pct"
        ],
        "artifact_deontic_conflict_determinism_pct": vnext_plus16_metrics[
            "artifact_deontic_conflict_determinism_pct"
        ],
        "artifact_reference_integrity_extended_determinism_pct": vnext_plus17_metrics[
            "artifact_reference_integrity_extended_determinism_pct"
        ],
        "artifact_cycle_policy_extended_determinism_pct": vnext_plus17_metrics[
            "artifact_cycle_policy_extended_determinism_pct"
        ],
        "artifact_deontic_conflict_extended_determinism_pct": vnext_plus17_metrics[
            "artifact_deontic_conflict_extended_determinism_pct"
        ],
        "artifact_validation_consolidation_parity_pct": vnext_plus18_metrics[
            "artifact_validation_consolidation_parity_pct"
        ],
        "artifact_transfer_report_consolidation_parity_pct": vnext_plus18_metrics[
            "artifact_transfer_report_consolidation_parity_pct"
        ],
        VNEXT_PLUS18_CI_BUDGET_METRIC_KEY: runtime_budget_metric_pct,
        "artifact_core_ir_read_surface_determinism_pct": vnext_plus19_metrics[
            "artifact_core_ir_read_surface_determinism_pct"
        ],
        "artifact_lane_read_surface_determinism_pct": vnext_plus19_metrics[
            "artifact_lane_read_surface_determinism_pct"
        ],
        "artifact_integrity_read_surface_determinism_pct": vnext_plus19_metrics[
            "artifact_integrity_read_surface_determinism_pct"
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
        "provider_route_contract_parity": metrics["provider_route_contract_parity_pct"]
        >= THRESHOLDS["provider_route_contract_parity_pct"],
        "codex_candidate_contract_valid": metrics["codex_candidate_contract_valid_pct"]
        >= THRESHOLDS["codex_candidate_contract_valid_pct"],
        "provider_parity_replay_determinism": metrics[
            "provider_parity_replay_determinism_pct"
        ]
        >= THRESHOLDS["provider_parity_replay_determinism_pct"],
        "adeu_lane_report_replay_determinism": metrics[
            "adeu_lane_report_replay_determinism_pct"
        ]
        >= THRESHOLDS["adeu_lane_report_replay_determinism_pct"],
        "adeu_projection_alignment_determinism": metrics[
            "adeu_projection_alignment_determinism_pct"
        ]
        >= THRESHOLDS["adeu_projection_alignment_determinism_pct"],
        "adeu_depth_report_replay_determinism": metrics[
            "adeu_depth_report_replay_determinism_pct"
        ]
        >= THRESHOLDS["adeu_depth_report_replay_determinism_pct"],
        "artifact_dangling_reference_determinism": metrics[
            "artifact_dangling_reference_determinism_pct"
        ]
        >= THRESHOLDS["artifact_dangling_reference_determinism_pct"],
        "artifact_cycle_policy_determinism": metrics[
            "artifact_cycle_policy_determinism_pct"
        ]
        >= THRESHOLDS["artifact_cycle_policy_determinism_pct"],
        "artifact_deontic_conflict_determinism": metrics[
            "artifact_deontic_conflict_determinism_pct"
        ]
        >= THRESHOLDS["artifact_deontic_conflict_determinism_pct"],
        "artifact_reference_integrity_extended_determinism": metrics[
            "artifact_reference_integrity_extended_determinism_pct"
        ]
        >= THRESHOLDS["artifact_reference_integrity_extended_determinism_pct"],
        "artifact_cycle_policy_extended_determinism": metrics[
            "artifact_cycle_policy_extended_determinism_pct"
        ]
        >= THRESHOLDS["artifact_cycle_policy_extended_determinism_pct"],
        "artifact_deontic_conflict_extended_determinism": metrics[
            "artifact_deontic_conflict_extended_determinism_pct"
        ]
        >= THRESHOLDS["artifact_deontic_conflict_extended_determinism_pct"],
        "artifact_validation_consolidation_parity": metrics[
            "artifact_validation_consolidation_parity_pct"
        ]
        >= THRESHOLDS["artifact_validation_consolidation_parity_pct"],
        "artifact_transfer_report_consolidation_parity": metrics[
            "artifact_transfer_report_consolidation_parity_pct"
        ]
        >= THRESHOLDS["artifact_transfer_report_consolidation_parity_pct"],
        "artifact_core_ir_read_surface_determinism": metrics[
            "artifact_core_ir_read_surface_determinism_pct"
        ]
        >= THRESHOLDS["artifact_core_ir_read_surface_determinism_pct"],
        "artifact_lane_read_surface_determinism": metrics[
            "artifact_lane_read_surface_determinism_pct"
        ]
        >= THRESHOLDS["artifact_lane_read_surface_determinism_pct"],
        "artifact_integrity_read_surface_determinism": metrics[
            "artifact_integrity_read_surface_determinism_pct"
        ]
        >= THRESHOLDS["artifact_integrity_read_surface_determinism_pct"],
        VNEXT_PLUS18_CI_BUDGET_GATE_KEY: (
            metrics[VNEXT_PLUS18_CI_BUDGET_METRIC_KEY]
            >= THRESHOLDS[VNEXT_PLUS18_CI_BUDGET_METRIC_KEY]
        ),
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
            "vnext_plus14_manifest_path": str(
                vnext_plus14_manifest_path
                if vnext_plus14_manifest_path is not None
                else VNEXT_PLUS14_MANIFEST_PATH
            ),
            "vnext_plus15_manifest_path": str(
                vnext_plus15_manifest_path
                if vnext_plus15_manifest_path is not None
                else VNEXT_PLUS15_MANIFEST_PATH
            ),
            "vnext_plus16_manifest_path": str(
                vnext_plus16_manifest_path
                if vnext_plus16_manifest_path is not None
                else VNEXT_PLUS16_MANIFEST_PATH
            ),
            "vnext_plus17_manifest_path": str(
                vnext_plus17_manifest_path
                if vnext_plus17_manifest_path is not None
                else VNEXT_PLUS17_MANIFEST_PATH
            ),
            "vnext_plus18_manifest_path": str(
                vnext_plus18_manifest_path
                if vnext_plus18_manifest_path is not None
                else VNEXT_PLUS18_MANIFEST_PATH
            ),
            "vnext_plus19_manifest_path": str(
                vnext_plus19_manifest_path
                if vnext_plus19_manifest_path is not None
                else VNEXT_PLUS19_MANIFEST_PATH
            ),
        },
        "vnext_plus8_manifest_hash": vnext_plus8_metrics["vnext_plus8_manifest_hash"],
        "vnext_plus9_manifest_hash": vnext_plus9_metrics["vnext_plus9_manifest_hash"],
        "vnext_plus10_manifest_hash": vnext_plus10_metrics["vnext_plus10_manifest_hash"],
        "vnext_plus11_manifest_hash": vnext_plus11_metrics["vnext_plus11_manifest_hash"],
        "vnext_plus13_manifest_hash": vnext_plus13_metrics["vnext_plus13_manifest_hash"],
        "vnext_plus14_manifest_hash": vnext_plus14_metrics["vnext_plus14_manifest_hash"],
        "vnext_plus15_manifest_hash": vnext_plus15_metrics["vnext_plus15_manifest_hash"],
        "vnext_plus16_manifest_hash": vnext_plus16_metrics["vnext_plus16_manifest_hash"],
        "vnext_plus17_manifest_hash": vnext_plus17_metrics["vnext_plus17_manifest_hash"],
        "vnext_plus18_manifest_hash": vnext_plus18_metrics["vnext_plus18_manifest_hash"],
        "vnext_plus19_manifest_hash": vnext_plus19_metrics["vnext_plus19_manifest_hash"],
        "thresholds": THRESHOLDS,
        "metrics": metrics,
        "gates": gates,
        "all_passed": all(gates.values()),
        "runtime_observability": runtime_observability,
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
    lines.append(f"- vnext+14 manifest hash: `{report.get('vnext_plus14_manifest_hash')}`")
    lines.append(f"- vnext+15 manifest hash: `{report.get('vnext_plus15_manifest_hash')}`")
    lines.append(f"- vnext+16 manifest hash: `{report.get('vnext_plus16_manifest_hash')}`")
    lines.append(f"- vnext+17 manifest hash: `{report.get('vnext_plus17_manifest_hash')}`")
    lines.append(f"- vnext+18 manifest hash: `{report.get('vnext_plus18_manifest_hash')}`")
    lines.append(f"- vnext+19 manifest hash: `{report.get('vnext_plus19_manifest_hash')}`")
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
        "- provider route contract parity pct: "
        f"`{metrics.get('provider_route_contract_parity_pct')}`"
    )
    lines.append(
        "- codex candidate contract valid pct: "
        f"`{metrics.get('codex_candidate_contract_valid_pct')}`"
    )
    lines.append(
        "- provider parity replay determinism pct: "
        f"`{metrics.get('provider_parity_replay_determinism_pct')}`"
    )
    lines.append(
        "- adeu lane report replay determinism pct: "
        f"`{metrics.get('adeu_lane_report_replay_determinism_pct')}`"
    )
    lines.append(
        "- adeu projection alignment determinism pct: "
        f"`{metrics.get('adeu_projection_alignment_determinism_pct')}`"
    )
    lines.append(
        "- adeu depth report replay determinism pct: "
        f"`{metrics.get('adeu_depth_report_replay_determinism_pct')}`"
    )
    lines.append(
        "- artifact dangling-reference determinism pct: "
        f"`{metrics.get('artifact_dangling_reference_determinism_pct')}`"
    )
    lines.append(
        "- artifact cycle-policy determinism pct: "
        f"`{metrics.get('artifact_cycle_policy_determinism_pct')}`"
    )
    lines.append(
        "- artifact deontic-conflict determinism pct: "
        f"`{metrics.get('artifact_deontic_conflict_determinism_pct')}`"
    )
    lines.append(
        "- artifact reference-integrity extended determinism pct: "
        f"`{metrics.get('artifact_reference_integrity_extended_determinism_pct')}`"
    )
    lines.append(
        "- artifact cycle-policy extended determinism pct: "
        f"`{metrics.get('artifact_cycle_policy_extended_determinism_pct')}`"
    )
    lines.append(
        "- artifact deontic-conflict extended determinism pct: "
        f"`{metrics.get('artifact_deontic_conflict_extended_determinism_pct')}`"
    )
    lines.append(
        "- artifact validation consolidation parity pct: "
        f"`{metrics.get('artifact_validation_consolidation_parity_pct')}`"
    )
    lines.append(
        "- artifact transfer-report consolidation parity pct: "
        f"`{metrics.get('artifact_transfer_report_consolidation_parity_pct')}`"
    )
    lines.append(
        "- artifact stop-gate ci budget within ceiling pct: "
        f"`{metrics.get('artifact_stop_gate_ci_budget_within_ceiling_pct')}`"
    )
    lines.append(
        "- artifact core-ir read-surface determinism pct: "
        f"`{metrics.get('artifact_core_ir_read_surface_determinism_pct')}`"
    )
    lines.append(
        "- artifact lane read-surface determinism pct: "
        f"`{metrics.get('artifact_lane_read_surface_determinism_pct')}`"
    )
    lines.append(
        "- artifact integrity read-surface determinism pct: "
        f"`{metrics.get('artifact_integrity_read_surface_determinism_pct')}`"
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
    runtime_observability = report.get("runtime_observability", {})
    if isinstance(runtime_observability, dict) and runtime_observability:
        lines.append("## Runtime Observability")
        lines.append("")
        lines.append(
            "- total fixtures: "
            f"`{runtime_observability.get('total_fixtures')}`"
        )
        lines.append(
            "- total replays: "
            f"`{runtime_observability.get('total_replays')}`"
        )
        lines.append(
            "- elapsed ms: "
            f"`{runtime_observability.get('elapsed_ms')}`"
        )
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
    parser.add_argument(
        "--vnext-plus14-manifest",
        dest="vnext_plus14_manifest_path",
        type=Path,
        default=VNEXT_PLUS14_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus15-manifest",
        dest="vnext_plus15_manifest_path",
        type=Path,
        default=VNEXT_PLUS15_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus16-manifest",
        dest="vnext_plus16_manifest_path",
        type=Path,
        default=VNEXT_PLUS16_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus17-manifest",
        dest="vnext_plus17_manifest_path",
        type=Path,
        default=VNEXT_PLUS17_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus18-manifest",
        dest="vnext_plus18_manifest_path",
        type=Path,
        default=VNEXT_PLUS18_MANIFEST_PATH,
    )
    parser.add_argument(
        "--vnext-plus19-manifest",
        dest="vnext_plus19_manifest_path",
        type=Path,
        default=VNEXT_PLUS19_MANIFEST_PATH,
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
        vnext_plus14_manifest_path=args.vnext_plus14_manifest_path,
        vnext_plus15_manifest_path=args.vnext_plus15_manifest_path,
        vnext_plus16_manifest_path=args.vnext_plus16_manifest_path,
        vnext_plus17_manifest_path=args.vnext_plus17_manifest_path,
        vnext_plus18_manifest_path=args.vnext_plus18_manifest_path,
        vnext_plus19_manifest_path=args.vnext_plus19_manifest_path,
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
