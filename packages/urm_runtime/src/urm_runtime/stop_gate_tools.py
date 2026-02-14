from __future__ import annotations

import argparse
import json
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from adeu_kernel import VALIDATOR_EVIDENCE_HASH_EXCLUDED_FIELDS
from pydantic import ValidationError

from .events_tools import replay_events, validate_events
from .hashing import canonical_json, sha256_canonical_json
from .models import NormalizedEvent

STOP_GATE_SCHEMA = "stop_gate_metrics@1"
POLICY_INCIDENT_SCHEMA = "incident_packet@1"
CONNECTOR_SNAPSHOT_SCHEMA = "connector_snapshot@1"
VALIDATOR_EVIDENCE_PACKET_SCHEMA = "validator_evidence_packet@1"
SEMANTICS_DIAGNOSTICS_SCHEMA = "semantics_diagnostics@1"
QUALITY_DASHBOARD_SCHEMA = "quality.dashboard.v1"
SEMANTICS_DETERMINISM_REPLAY_COUNT = 3
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


def _strip_nonsemantic_validator_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for raw_key, raw_value in sorted(value.items(), key=lambda item: str(item[0])):
            key = str(raw_key)
            if key in VALIDATOR_EVIDENCE_HASH_EXCLUDED_FIELDS:
                continue
            if key.endswith("_raw"):
                continue
            normalized[key] = _strip_nonsemantic_validator_fields(raw_value)
        return normalized
    if isinstance(value, list):
        return [_strip_nonsemantic_validator_fields(item) for item in value]
    return value


def _validator_packet_hash(payload: Mapping[str, Any]) -> str:
    return sha256_canonical_json(_strip_nonsemantic_validator_fields(payload))


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


def _is_three_replay_deterministic(hash_supplier: Any) -> tuple[bool, list[str]]:
    replay_hashes = [str(hash_supplier()) for _ in range(SEMANTICS_DETERMINISM_REPLAY_COUNT)]
    return len(set(replay_hashes)) == 1, replay_hashes


def _issue(code: str, message: str, *, context: dict[str, Any] | None = None) -> dict[str, Any]:
    return {"code": code, "message": message, "context": dict(context or {})}


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

    validator_packet_total = 0
    validator_packet_passed = 0
    witness_total = 0
    witness_passed = 0
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

        validator_packet_total += 1
        packet_deterministic, _ = _is_three_replay_deterministic(
            lambda current_payload=payload: _validator_packet_hash(current_payload)
        )
        if packet_deterministic:
            validator_packet_passed += 1

        witness_total += 1
        witness_deterministic, _ = _is_three_replay_deterministic(
            lambda current_payload=payload: _witness_reconstruction_hash(current_payload)
        )
        if witness_deterministic:
            witness_passed += 1

    validator_packet_determinism_pct = _pct(validator_packet_passed, validator_packet_total)
    witness_reconstruction_determinism_pct = _pct(witness_passed, witness_total)

    semantics_diagnostics_total = 0
    semantics_diagnostics_passed = 0
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

        semantics_diagnostics_total += 1
        diagnostics_deterministic, _ = _is_three_replay_deterministic(
            lambda current_payload=payload: _semantics_diagnostics_hash(current_payload)
        )
        if diagnostics_deterministic:
            semantics_diagnostics_passed += 1

    semantics_diagnostics_determinism_pct = _pct(
        semantics_diagnostics_passed,
        semantics_diagnostics_total,
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
        },
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
