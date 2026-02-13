from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from pydantic import ValidationError

from .errors import URMError
from .hashing import canonical_json, sha256_canonical_json
from .instruction_policy import (
    EvidenceRef,
    EvidenceRefKind,
    InstructionPolicy,
    PolicyContext,
    PolicyDecision,
    compute_policy_hash,
    evaluate_instruction_policy,
    load_instruction_policy,
    policy_semantic_form,
)
from .models import NormalizedEvent

POLICY_VALIDATE_SCHEMA = "instruction-policy-validate@1"
POLICY_EVAL_SCHEMA = "instruction-policy-eval@1"
POLICY_DIFF_SCHEMA = "instruction-policy-diff@1"
POLICY_EXPLAIN_SCHEMA = "policy_explain@1"
POLICY_INCIDENT_SCHEMA = "incident_packet@1"
POLICY_EXPLAIN_INVALID_INPUT = "URM_POLICY_EXPLAIN_INVALID_INPUT"
DEFAULT_EVALUATION_TS = "1970-01-01T00:00:00Z"
_CANONICAL_REF_PREFIX_TO_KIND: dict[str, EvidenceRefKind] = {
    "event:": "event",
    "run:": "run",
    "validator:": "validator",
    "proof:": "proof",
    "artifact:": "artifact",
}
_REDACTED_VALUE = "[REDACTED]"


def _load_json_from_path(path: Path, *, description: str) -> dict[str, Any]:
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{description} file is not readable",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{description} is invalid JSON",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{description} must be a JSON object",
            context={"path": str(path)},
        )
    return payload


def _error_issue(exc: URMError) -> dict[str, Any]:
    return {
        "code": exc.detail.code,
        "message": exc.detail.message,
        "context": exc.detail.context,
    }


def _now_utc_z() -> str:
    return datetime.now(tz=timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _resolve_evaluation_ts(
    *,
    context_doc: dict[str, Any],
    evaluation_ts: str | None,
    use_now: bool,
    invalid_input_code: str,
) -> str:
    if use_now and evaluation_ts is not None:
        raise URMError(
            code=invalid_input_code,
            message="cannot combine --use-now with --evaluation-ts",
        )
    if use_now:
        return _now_utc_z()
    if evaluation_ts is not None:
        return evaluation_ts
    if "evaluation_ts" in context_doc:
        return str(context_doc["evaluation_ts"])
    return DEFAULT_EVALUATION_TS


def _decision_evidence_refs(decision: PolicyDecision) -> list[dict[str, Any]]:
    return [ref.model_dump(mode="json") for ref in decision.evidence_refs]


def _sorted_evidence_refs(evidence_refs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted(
        evidence_refs,
        key=lambda item: (
            str(item.get("kind", "")),
            str(item.get("ref", "")),
            str(item.get("note", "") or ""),
        ),
    )


def _decision_trace_hash(*, decision: PolicyDecision, evidence_refs: list[dict[str, Any]]) -> str:
    trace_payload = {
        "decision": decision.decision,
        "decision_code": decision.decision_code,
        "policy_hash": decision.policy_hash,
        "input_context_hash": decision.input_context_hash,
        "matched_rule_ids": list(decision.matched_rule_ids),
        "required_approval": decision.required_approval,
        "trace_version": decision.trace_version,
        "policy_schema_version": decision.policy_schema_version,
        "policy_ir_version": decision.policy_ir_version,
        "evaluator_version": decision.evaluator_version,
        "advisories": list(decision.advisories),
        "warrant_invalid": decision.warrant_invalid,
        "evidence_refs": evidence_refs,
    }
    return sha256_canonical_json(trace_payload)


def _build_input_manifest(
    *,
    decision: PolicyDecision,
    evaluation_ts: str,
    evidence_refs: list[dict[str, Any]],
) -> dict[str, Any]:
    normalized_refs = _sorted_evidence_refs(evidence_refs)
    return {
        "policy_hash": decision.policy_hash,
        "input_context_hash": decision.input_context_hash,
        "evaluation_ts": evaluation_ts,
        "evidence_refs": normalized_refs,
        "decision_trace_hash": _decision_trace_hash(
            decision=decision,
            evidence_refs=normalized_refs,
        ),
    }


def _normalize_report_advisories(advisories: Any) -> list[dict[str, Any]]:
    if not isinstance(advisories, list):
        return []
    normalized: list[dict[str, Any]] = []
    for advisory in advisories:
        if isinstance(advisory, dict):
            normalized.append(dict(advisory))
    return normalized


def _normalize_report_evidence_refs(evidence_refs: Any) -> list[dict[str, Any]]:
    if evidence_refs is None:
        return []
    if not isinstance(evidence_refs, list):
        raise ValueError("evidence_refs must be a list")
    normalized: list[dict[str, Any]] = []
    for idx, candidate in enumerate(evidence_refs):
        if not isinstance(candidate, dict):
            raise ValueError(f"evidence_refs[{idx}] must be an object")
        normalized_ref = dict(candidate)
        if "kind" not in normalized_ref:
            derived_kind = _canonical_ref_kind(str(normalized_ref.get("ref", "")))
            if derived_kind is None:
                raise ValueError(f"evidence_refs[{idx}] has unknown canonical ref prefix")
            normalized_ref["kind"] = derived_kind
        parsed = EvidenceRef.model_validate(normalized_ref)
        normalized.append(parsed.model_dump(mode="json"))
    return normalized


def _decision_from_payload(
    *,
    payload: dict[str, Any],
    invalid_input_code: str,
) -> PolicyDecision:
    schema = payload.get("schema")
    if schema is not None and schema not in {POLICY_EVAL_SCHEMA, POLICY_EXPLAIN_SCHEMA}:
        raise URMError(
            code=invalid_input_code,
            message="unsupported decision payload schema",
            context={"schema": schema},
        )

    if schema is not None and payload.get("valid") is not True:
        raise URMError(
            code=invalid_input_code,
            message="decision payload must be valid for explain rendering",
            context={"schema": schema},
        )

    try:
        raw_decision = {
            "decision": payload.get("decision"),
            "decision_code": payload.get("decision_code"),
            "policy_hash": payload.get("policy_hash"),
            "input_context_hash": payload.get("input_context_hash"),
            "matched_rule_ids": payload.get("matched_rule_ids"),
            "required_approval": payload.get("required_approval"),
            "trace_version": payload.get("trace_version"),
            "policy_schema_version": payload.get("policy_schema_version"),
            "policy_ir_version": payload.get("policy_ir_version"),
            "evaluator_version": payload.get("evaluator_version"),
            "advisories": _normalize_report_advisories(payload.get("advisories")),
            "warrant_invalid": bool(payload.get("warrant_invalid", False)),
            "evidence_refs": _normalize_report_evidence_refs(payload.get("evidence_refs")),
        }
    except (ValidationError, ValueError) as exc:
        raise URMError(
            code=invalid_input_code,
            message="decision payload contains invalid explain evidence refs",
            context={"error": str(exc), "schema": schema},
        ) from exc

    try:
        return PolicyDecision.model_validate(raw_decision)
    except ValidationError as exc:
        raise URMError(
            code=invalid_input_code,
            message="decision payload is not a valid PolicyDecision trace",
            context={"error": str(exc), "schema": schema},
        ) from exc


def _build_policy_explain_report(
    *,
    decision: PolicyDecision,
    input_policy: str | None,
    input_context: str | None,
    input_decision: str | None,
    strict: bool,
    deterministic_mode: bool,
    evaluation_ts: str,
    matched_rules: list[dict[str, Any]],
) -> dict[str, Any]:
    evidence_refs = _decision_evidence_refs(decision)
    input_manifest = _build_input_manifest(
        decision=decision,
        evaluation_ts=evaluation_ts,
        evidence_refs=evidence_refs,
    )
    report: dict[str, Any] = {
        "schema": POLICY_EXPLAIN_SCHEMA,
        "strict": strict,
        "deterministic_mode": deterministic_mode,
        "valid": True,
        "evaluation_ts": evaluation_ts,
        "policy_hash": decision.policy_hash,
        "input_context_hash": decision.input_context_hash,
        "decision": decision.decision,
        "decision_code": decision.decision_code,
        "matched_rule_ids": list(decision.matched_rule_ids),
        "matched_rules": list(matched_rules),
        "required_approval": decision.required_approval,
        "evaluator_version": decision.evaluator_version,
        "trace_version": decision.trace_version,
        "policy_schema_version": decision.policy_schema_version,
        "policy_ir_version": decision.policy_ir_version,
        "advisories": list(decision.advisories),
        "warrant_invalid": decision.warrant_invalid,
        "evidence_refs": evidence_refs,
        "input_manifest": input_manifest,
        "issues": [],
    }
    if input_policy is not None:
        report["input_policy"] = input_policy
    if input_context is not None:
        report["input_context"] = input_context
    if input_decision is not None:
        report["input_decision"] = input_decision
    return report


def _evaluate_policy_with_context(
    *,
    policy_path: Path,
    context_path: Path,
    strict: bool,
    schema_path: Path | None,
    evaluation_ts: str | None,
    use_now: bool,
    invalid_input_code: str,
) -> tuple[InstructionPolicy, PolicyContext, PolicyDecision]:
    policy = load_instruction_policy(
        policy_path=policy_path,
        schema_path=schema_path,
        strict=strict,
    )
    context_doc = _load_json_from_path(context_path, description="policy context")
    context_doc["evaluation_ts"] = _resolve_evaluation_ts(
        context_doc=context_doc,
        evaluation_ts=evaluation_ts,
        use_now=use_now,
        invalid_input_code=invalid_input_code,
    )
    context = PolicyContext.model_validate(context_doc)
    decision = evaluate_instruction_policy(policy=policy, context=context)
    return policy, context, decision


def _canonical_ref_kind(ref: str) -> EvidenceRefKind | None:
    for prefix, kind in _CANONICAL_REF_PREFIX_TO_KIND.items():
        if ref.startswith(prefix):
            return kind
    return None


def _normalize_artifact_refs(
    *,
    explain_report: dict[str, Any],
    explicit_refs: list[str],
    stream_ranges: list[dict[str, Any]],
) -> list[dict[str, str]]:
    refs: dict[tuple[str, str], dict[str, str]] = {}
    decision_refs = explain_report.get("evidence_refs")
    if isinstance(decision_refs, list):
        for entry in decision_refs:
            if not isinstance(entry, dict):
                continue
            ref_value = entry.get("ref")
            if not isinstance(ref_value, str):
                continue
            kind = _canonical_ref_kind(ref_value)
            if kind is None:
                continue
            refs[(kind, ref_value)] = {"kind": kind, "ref": ref_value}

    for stream in stream_ranges:
        stream_id = stream["stream_id"]
        seq_range = stream["seq_range"]
        start_ref = f"event:{stream_id}#{seq_range['start_seq']}"
        end_ref = f"event:{stream_id}#{seq_range['end_seq']}"
        refs[("event", start_ref)] = {"kind": "event", "ref": start_ref}
        refs[("event", end_ref)] = {"kind": "event", "ref": end_ref}

    for explicit_ref in explicit_refs:
        kind = _canonical_ref_kind(explicit_ref)
        if kind is None:
            raise URMError(
                code="URM_INCIDENT_PACKET_BUILD_FAILED",
                message="artifact ref must use canonical prefix",
                context={"artifact_ref": explicit_ref},
            )
        refs[(kind, explicit_ref)] = {"kind": kind, "ref": explicit_ref}

    return [refs[key] for key in sorted(refs, key=lambda item: (item[0], item[1]))]


def _parse_stream_spec(spec: str) -> tuple[str, Path]:
    stream_id, sep, path_text = spec.partition("=")
    if sep == "" or not stream_id.strip() or not path_text.strip():
        raise URMError(
            code="URM_INCIDENT_PACKET_BUILD_FAILED",
            message="stream spec must be STREAM_ID=PATH",
            context={"stream": spec},
        )
    return stream_id.strip(), Path(path_text.strip())


def _stream_seq_range(*, stream_id: str, stream_path: Path) -> dict[str, Any]:
    try:
        lines = stream_path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError as exc:
        raise URMError(
            code="URM_INCIDENT_PACKET_BUILD_FAILED",
            message="stream file is not readable",
            context={"stream_id": stream_id, "stream_path": str(stream_path), "error": str(exc)},
        ) from exc

    seq_values: list[int] = []
    for idx, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        try:
            payload = json.loads(line)
        except json.JSONDecodeError as exc:
            raise URMError(
                code="URM_INCIDENT_PACKET_BUILD_FAILED",
                message="stream file contains invalid JSON",
                context={
                    "stream_id": stream_id,
                    "stream_path": str(stream_path),
                    "line": idx,
                    "error": str(exc),
                },
            ) from exc
        try:
            event = NormalizedEvent.model_validate(payload)
        except Exception as exc:
            raise URMError(
                code="URM_INCIDENT_PACKET_BUILD_FAILED",
                message="stream file contains invalid urm-events@1 record",
                context={
                    "stream_id": stream_id,
                    "stream_path": str(stream_path),
                    "line": idx,
                    "error": str(exc),
                },
            ) from exc
        if event.stream_id == stream_id:
            seq_values.append(event.seq)
    if not seq_values:
        raise URMError(
            code="URM_INCIDENT_PACKET_BUILD_FAILED",
            message="stream file does not contain matching stream_id events",
            context={"stream_id": stream_id, "stream_path": str(stream_path)},
        )
    return {
        "stream_id": stream_id,
        "seq_range": {"start_seq": min(seq_values), "end_seq": max(seq_values)},
    }


def _collect_redaction_markers(
    value: Any,
    *,
    path: tuple[str, ...] = (),
) -> list[dict[str, str]]:
    markers: list[dict[str, str]] = []
    if isinstance(value, dict):
        for key in sorted(value):
            key_text = str(key)
            lower_key = key_text.lower()
            next_path = path + (key_text,)
            if any(token in lower_key for token in ("secret", "token", "password", "api_key")):
                markers.append({"path": ".".join(next_path), "replacement": _REDACTED_VALUE})
                continue
            markers.extend(_collect_redaction_markers(value[key], path=next_path))
    elif isinstance(value, list):
        for idx, item in enumerate(value):
            markers.extend(_collect_redaction_markers(item, path=path + (str(idx),)))
    return markers


def validate_policy(
    path: Path,
    *,
    strict: bool,
    schema_path: Path | None = None,
) -> dict[str, Any]:
    try:
        policy = load_instruction_policy(policy_path=path, schema_path=schema_path, strict=strict)
    except URMError as exc:
        return {
            "schema": POLICY_VALIDATE_SCHEMA,
            "input": str(path),
            "strict": strict,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    return {
        "schema": POLICY_VALIDATE_SCHEMA,
        "input": str(path),
        "strict": strict,
        "valid": True,
        "policy_hash": compute_policy_hash(policy),
        "rule_count": len(policy.rules),
        "issues": [],
    }


def eval_policy(
    *,
    policy_path: Path,
    context_path: Path,
    strict: bool,
    schema_path: Path | None = None,
    evaluation_ts: str | None = None,
    use_now: bool = False,
) -> dict[str, Any]:
    try:
        _, context, decision = _evaluate_policy_with_context(
            policy_path=policy_path,
            context_path=context_path,
            strict=strict,
            schema_path=schema_path,
            evaluation_ts=evaluation_ts,
            use_now=use_now,
            invalid_input_code="URM_POLICY_INVALID_SCHEMA",
        )
    except URMError as exc:
        return {
            "schema": POLICY_EVAL_SCHEMA,
            "input_policy": str(policy_path),
            "input_context": str(context_path),
            "strict": strict,
            "deterministic_mode": not use_now,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    return {
        "schema": POLICY_EVAL_SCHEMA,
        "input_policy": str(policy_path),
        "input_context": str(context_path),
        "strict": strict,
        "deterministic_mode": not use_now,
        "valid": True,
        "evaluation_ts": context.evaluation_ts,
        "policy_hash": decision.policy_hash,
        "input_context_hash": decision.input_context_hash,
        "decision": decision.decision,
        "decision_code": decision.decision_code,
        "matched_rule_ids": list(decision.matched_rule_ids),
        "required_approval": decision.required_approval,
        "evaluator_version": decision.evaluator_version,
        "trace_version": decision.trace_version,
        "policy_schema_version": decision.policy_schema_version,
        "policy_ir_version": decision.policy_ir_version,
        "issues": [],
    }


def _semantic_rule_map(policy: InstructionPolicy) -> dict[str, dict[str, Any]]:
    semantic_rules = policy_semantic_form(policy)["rules"]
    return {str(rule["rule_id"]): rule for rule in semantic_rules}


def _rule_index(policy: InstructionPolicy) -> dict[str, Any]:
    return {rule.rule_id: rule for rule in policy.rules}


def _matched_rule_summaries(
    *,
    policy: InstructionPolicy,
    decision: PolicyDecision,
) -> list[dict[str, Any]]:
    by_id = _rule_index(policy)
    summaries: list[dict[str, Any]] = []
    for rule_id in decision.matched_rule_ids:
        rule = by_id.get(rule_id)
        if rule is None:
            continue
        summaries.append(
            {
                "rule_id": rule.rule_id,
                "rule_version": rule.rule_version,
                "priority": rule.priority,
                "kind": rule.kind,
                "code": rule.code,
                "effect": rule.then.effect,
                "message": rule.message,
            }
        )
    return summaries


def explain_policy(
    *,
    policy_path: Path,
    context_path: Path,
    strict: bool,
    schema_path: Path | None = None,
    evaluation_ts: str | None = None,
    use_now: bool = False,
) -> dict[str, Any]:
    try:
        policy, context, decision = _evaluate_policy_with_context(
            policy_path=policy_path,
            context_path=context_path,
            strict=strict,
            schema_path=schema_path,
            evaluation_ts=evaluation_ts,
            use_now=use_now,
            invalid_input_code=POLICY_EXPLAIN_INVALID_INPUT,
        )
    except URMError as exc:
        return {
            "schema": POLICY_EXPLAIN_SCHEMA,
            "input_policy": str(policy_path),
            "input_context": str(context_path),
            "strict": strict,
            "deterministic_mode": not use_now,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    return _build_policy_explain_report(
        decision=decision,
        input_policy=str(policy_path),
        matched_rules=_matched_rule_summaries(policy=policy, decision=decision),
        input_context=str(context_path),
        input_decision=None,
        strict=strict,
        deterministic_mode=not use_now,
        evaluation_ts=context.evaluation_ts,
    )


def explain_policy_from_decision(
    *,
    decision_path: Path,
    evaluation_ts: str | None = None,
    use_now: bool = False,
) -> dict[str, Any]:
    try:
        try:
            payload = _load_json_from_path(decision_path, description="policy decision payload")
        except URMError as exc:
            raise URMError(
                code=POLICY_EXPLAIN_INVALID_INPUT,
                message="policy decision payload is unreadable or invalid",
                context={"path": str(decision_path), "cause": exc.detail.context},
            ) from exc
        resolved_ts = _resolve_evaluation_ts(
            context_doc=payload,
            evaluation_ts=evaluation_ts,
            use_now=use_now,
            invalid_input_code=POLICY_EXPLAIN_INVALID_INPUT,
        )
        decision = _decision_from_payload(
            payload=payload,
            invalid_input_code=POLICY_EXPLAIN_INVALID_INPUT,
        )
        matched_rules = payload.get("matched_rules")
        normalized_matched_rules = (
            [rule for rule in matched_rules if isinstance(rule, dict)]
            if isinstance(matched_rules, list)
            else []
        )
        strict = payload.get("strict")
        strict_value = bool(strict) if isinstance(strict, bool) else True
    except URMError as exc:
        return {
            "schema": POLICY_EXPLAIN_SCHEMA,
            "input_decision": str(decision_path),
            "deterministic_mode": not use_now,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    return _build_policy_explain_report(
        decision=decision,
        input_policy=(
            str(payload["input_policy"])
            if isinstance(payload.get("input_policy"), str)
            else None
        ),
        input_context=(
            str(payload["input_context"]) if isinstance(payload.get("input_context"), str) else None
        ),
        input_decision=str(decision_path),
        strict=strict_value,
        deterministic_mode=not use_now,
        evaluation_ts=resolved_ts,
        matched_rules=normalized_matched_rules,
    )


def policy_explain_markdown(report: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Policy Explain Report",
        "",
        f"- Schema: `{report.get('schema', POLICY_EXPLAIN_SCHEMA)}`",
        f"- Valid: `{bool(report.get('valid'))}`",
        f"- Deterministic mode: `{bool(report.get('deterministic_mode'))}`",
    ]
    input_policy = report.get("input_policy")
    if isinstance(input_policy, str):
        lines.append(f"- Input policy: `{input_policy}`")
    input_context = report.get("input_context")
    if isinstance(input_context, str):
        lines.append(f"- Input context: `{input_context}`")
    input_decision = report.get("input_decision")
    if isinstance(input_decision, str):
        lines.append(f"- Input decision: `{input_decision}`")
    lines.append("")

    if report.get("valid") is True:
        lines.extend(
            [
                "## Decision",
                "",
                f"- Decision: `{report.get('decision')}`",
                f"- Decision code: `{report.get('decision_code')}`",
                f"- Required approval: `{bool(report.get('required_approval'))}`",
                "",
            ]
        )
        input_manifest = report.get("input_manifest")
        if isinstance(input_manifest, dict):
            lines.extend(
                [
                    "## Input Manifest",
                    "",
                    f"- `policy_hash`: `{input_manifest.get('policy_hash')}`",
                    f"- `input_context_hash`: `{input_manifest.get('input_context_hash')}`",
                    f"- `evaluation_ts`: `{input_manifest.get('evaluation_ts')}`",
                    f"- `decision_trace_hash`: `{input_manifest.get('decision_trace_hash')}`",
                    "",
                ]
            )
        matched_rule_ids = report.get("matched_rule_ids")
        if isinstance(matched_rule_ids, list):
            lines.append("## Matched Rule IDs")
            lines.append("")
            for rule_id in matched_rule_ids:
                lines.append(f"- `{rule_id}`")
            if not matched_rule_ids:
                lines.append("- _(none)_")
            lines.append("")

        evidence_refs = report.get("evidence_refs")
        if isinstance(evidence_refs, list):
            lines.append("## Evidence Refs")
            lines.append("")
            normalized_refs = _sorted_evidence_refs(
                [ref for ref in evidence_refs if isinstance(ref, dict)]
            )
            if normalized_refs:
                for ref in normalized_refs:
                    note = ref.get("note")
                    if isinstance(note, str) and note:
                        lines.append(f"- `{ref.get('kind')}` `{ref.get('ref')}` ({note})")
                    else:
                        lines.append(f"- `{ref.get('kind')}` `{ref.get('ref')}`")
            else:
                lines.append("- _(none)_")
            lines.append("")

    issues = report.get("issues")
    if isinstance(issues, list) and issues:
        lines.extend(["## Issues", ""])
        for issue in issues:
            if not isinstance(issue, dict):
                continue
            lines.append(
                f"- `{issue.get('code')}`: {issue.get('message')} "
                f"({canonical_json(issue.get('context', {}))})"
            )
        lines.append("")

    return "\n".join(lines)


def diff_policy(
    *,
    old_policy_path: Path,
    new_policy_path: Path,
    strict: bool,
    schema_path: Path | None = None,
) -> dict[str, Any]:
    try:
        old_policy = load_instruction_policy(
            policy_path=old_policy_path,
            schema_path=schema_path,
            strict=strict,
        )
        new_policy = load_instruction_policy(
            policy_path=new_policy_path,
            schema_path=schema_path,
            strict=strict,
        )
        old_by_id = _semantic_rule_map(old_policy)
        new_by_id = _semantic_rule_map(new_policy)
    except URMError as exc:
        return {
            "schema": POLICY_DIFF_SCHEMA,
            "input_old": str(old_policy_path),
            "input_new": str(new_policy_path),
            "strict": strict,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    old_ids = set(old_by_id)
    new_ids = set(new_by_id)
    added_rules = sorted(new_ids - old_ids)
    removed_rules = sorted(old_ids - new_ids)

    modified_rules: list[dict[str, Any]] = []
    changed_fields = ("priority", "when", "then", "code", "kind", "rule_version")
    for rule_id in sorted(old_ids & new_ids):
        old_rule = old_by_id[rule_id]
        new_rule = new_by_id[rule_id]
        changes: dict[str, dict[str, Any]] = {}
        for field in changed_fields:
            if old_rule.get(field) != new_rule.get(field):
                changes[field] = {"old": old_rule.get(field), "new": new_rule.get(field)}
        if changes:
            modified_rules.append(
                {
                    "rule_id": rule_id,
                    "changed_fields": sorted(changes),
                    "changes": changes,
                }
            )

    semantic_equal = not added_rules and not removed_rules and not modified_rules
    return {
        "schema": POLICY_DIFF_SCHEMA,
        "input_old": str(old_policy_path),
        "input_new": str(new_policy_path),
        "strict": strict,
        "valid": True,
        "old_policy_hash": compute_policy_hash(old_policy),
        "new_policy_hash": compute_policy_hash(new_policy),
        "semantic_equal": semantic_equal,
        "added_rules": added_rules,
        "removed_rules": removed_rules,
        "modified_rules": modified_rules,
        "issues": [],
    }


def incident_packet(
    *,
    decision_path: Path,
    stream_specs: list[str],
    artifact_refs: list[str] | None = None,
) -> dict[str, Any]:
    try:
        report = _load_json_from_path(decision_path, description="policy explain report")
        schema = report.get("schema")
        if schema not in {POLICY_EXPLAIN_SCHEMA, POLICY_EVAL_SCHEMA}:
            raise URMError(
                code="URM_INCIDENT_PACKET_BUILD_FAILED",
                message=(
                    "incident packet input must be policy_explain@1 "
                    "or instruction-policy-eval@1"
                ),
                context={"schema": schema},
            )
        if report.get("valid") is not True:
            raise URMError(
                code="URM_INCIDENT_PACKET_BUILD_FAILED",
                message="incident packet input report must be valid",
                context={"schema": schema},
            )

        required_keys = (
            "policy_hash",
            "input_context_hash",
            "decision_code",
            "matched_rule_ids",
        )
        for key in required_keys:
            if key not in report:
                raise URMError(
                    code="URM_INCIDENT_PACKET_BUILD_FAILED",
                    message="incident packet input is missing required fields",
                    context={"missing_key": key},
                )

        parsed_streams: list[tuple[str, Path]] = [_parse_stream_spec(spec) for spec in stream_specs]
        stream_ranges = [
            _stream_seq_range(stream_id=stream_id, stream_path=stream_path)
            for stream_id, stream_path in parsed_streams
        ]
        ordered_streams = sorted(stream_ranges, key=lambda item: item["stream_id"])
        ordered_refs = _normalize_artifact_refs(
            explain_report=report,
            explicit_refs=list(artifact_refs or []),
            stream_ranges=ordered_streams,
        )
        redaction_markers = sorted(
            _collect_redaction_markers(report),
            key=lambda marker: (marker["path"], marker["replacement"]),
        )
    except URMError as exc:
        return {
            "schema": POLICY_INCIDENT_SCHEMA,
            "input_report": str(decision_path),
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    return {
        "schema": POLICY_INCIDENT_SCHEMA,
        "input_report": str(decision_path),
        "valid": True,
        "policy_hash": str(report["policy_hash"]),
        "input_context_hash": str(report["input_context_hash"]),
        "decision_code": str(report["decision_code"]),
        "matched_rule_ids": list(report["matched_rule_ids"]),
        "artifact_refs": ordered_refs,
        "streams": ordered_streams,
        "redaction_markers": redaction_markers,
        "issues": [],
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="policy",
        description=(
            "Instruction policy tooling: validate, eval, explain, and diff policy IR documents."
        ),
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate_parser = subparsers.add_parser(
        "validate",
        help="Validate an ODEU instruction policy document.",
    )
    validate_parser.add_argument("--in", dest="input_path", type=Path, required=True)
    validate_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    validate_parser.add_argument("--strict", action="store_true")

    eval_parser = subparsers.add_parser(
        "eval",
        help="Evaluate a policy decision for a provided context document.",
    )
    eval_parser.add_argument("--policy", dest="policy_path", type=Path, required=True)
    eval_parser.add_argument("--context", dest="context_path", type=Path, required=True)
    eval_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    eval_parser.add_argument("--evaluation-ts", dest="evaluation_ts", type=str, required=False)
    eval_parser.add_argument("--use-now", dest="use_now", action="store_true")
    eval_parser.add_argument("--out", dest="out_path", type=Path, required=False)
    eval_parser.add_argument("--lax", dest="strict", action="store_false")
    eval_parser.set_defaults(strict=True)

    explain_parser = subparsers.add_parser(
        "explain",
        help="Render deterministic explanation view from policy decision output.",
    )
    explain_parser.add_argument("--policy", dest="policy_path", type=Path, required=True)
    explain_parser.add_argument("--context", dest="context_path", type=Path, required=True)
    explain_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    explain_parser.add_argument("--evaluation-ts", dest="evaluation_ts", type=str, required=False)
    explain_parser.add_argument("--use-now", dest="use_now", action="store_true")
    explain_parser.add_argument("--out", dest="out_path", type=Path, required=False)
    explain_parser.add_argument("--out-md", dest="out_md_path", type=Path, required=False)
    explain_parser.add_argument("--lax", dest="strict", action="store_false")
    explain_parser.set_defaults(strict=True)

    explain_from_decision_parser = subparsers.add_parser(
        "explain-from-decision",
        help="Render deterministic explanation view from persisted decision payload.",
    )
    explain_from_decision_parser.add_argument(
        "--decision",
        dest="decision_path",
        type=Path,
        required=True,
    )
    explain_from_decision_parser.add_argument(
        "--evaluation-ts", dest="evaluation_ts", type=str, required=False
    )
    explain_from_decision_parser.add_argument("--use-now", dest="use_now", action="store_true")
    explain_from_decision_parser.add_argument("--out", dest="out_path", type=Path, required=False)
    explain_from_decision_parser.add_argument(
        "--out-md",
        dest="out_md_path",
        type=Path,
        required=False,
    )

    diff_parser = subparsers.add_parser(
        "diff",
        help="Compute semantic diff between two policy documents.",
    )
    diff_parser.add_argument("--old", dest="old_policy_path", type=Path, required=True)
    diff_parser.add_argument("--new", dest="new_policy_path", type=Path, required=True)
    diff_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    diff_parser.add_argument("--out", dest="out_path", type=Path, required=False)
    diff_parser.add_argument("--lax", dest="strict", action="store_false")
    diff_parser.set_defaults(strict=True)

    incident_parser = subparsers.add_parser(
        "incident",
        help="Build deterministic incident packet from policy report + evidence streams.",
    )
    incident_parser.add_argument("--decision", dest="decision_path", type=Path, required=True)
    incident_parser.add_argument("--stream", dest="stream_specs", action="append", required=True)
    incident_parser.add_argument("--artifact-ref", dest="artifact_refs", action="append")
    incident_parser.add_argument("--out", dest="out_path", type=Path, required=False)

    return parser.parse_args(argv)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _emit_report(report: dict[str, Any], *, out_path: Path | None) -> int:
    out_text = canonical_json(report)
    if out_path is not None:
        _write_text(out_path, out_text + "\n")
    else:
        print(out_text)
    return 0 if bool(report.get("valid")) else 1


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    if args.command == "validate":
        report = validate_policy(
            args.input_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
        )
        return _emit_report(report, out_path=None)
    if args.command == "eval":
        report = eval_policy(
            policy_path=args.policy_path,
            context_path=args.context_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
            evaluation_ts=args.evaluation_ts,
            use_now=bool(args.use_now),
        )
        return _emit_report(report, out_path=args.out_path)
    if args.command == "explain":
        report = explain_policy(
            policy_path=args.policy_path,
            context_path=args.context_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
            evaluation_ts=args.evaluation_ts,
            use_now=bool(args.use_now),
        )
        if args.out_md_path is not None:
            _write_text(args.out_md_path, policy_explain_markdown(report))
        return _emit_report(report, out_path=args.out_path)
    if args.command == "explain-from-decision":
        report = explain_policy_from_decision(
            decision_path=args.decision_path,
            evaluation_ts=args.evaluation_ts,
            use_now=bool(args.use_now),
        )
        if args.out_md_path is not None:
            _write_text(args.out_md_path, policy_explain_markdown(report))
        return _emit_report(report, out_path=args.out_path)
    if args.command == "diff":
        report = diff_policy(
            old_policy_path=args.old_policy_path,
            new_policy_path=args.new_policy_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
        )
        return _emit_report(report, out_path=args.out_path)
    if args.command == "incident":
        report = incident_packet(
            decision_path=args.decision_path,
            stream_specs=list(args.stream_specs),
            artifact_refs=list(args.artifact_refs or []),
        )
        return _emit_report(report, out_path=args.out_path)
    return 1  # pragma: no cover


if __name__ == "__main__":
    raise SystemExit(main())
