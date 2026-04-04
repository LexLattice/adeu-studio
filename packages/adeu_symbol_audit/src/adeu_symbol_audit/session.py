from __future__ import annotations

from typing import Any

from .models import (
    ADEU_SYMBOL_AUDIT_SESSION_CONFIG_SCHEMA,
    OutputFormat,
    SemanticVocabularyPosture,
    SessionStatus,
    SymbolAuditCoverageReport,
    SymbolAuditScopeManifest,
    SymbolAuditSession,
    SymbolAuditSessionConfig,
    SymbolCensus,
    SymbolSemanticAudit,
    _dump_canonical_json,
    _sha256_canonical_payload,
    compute_session_config_id,
    compute_session_id,
)

RELEASED_SEMANTIC_VOCABULARY_POSTURE: SemanticVocabularyPosture = (
    "explicit_independence_from_v49"
)


def _build_session_config_payload(
    *,
    session_mode: str,
    output_format: str,
    include_evidence_refs: Any,
) -> dict[str, object]:
    payload: dict[str, object] = {
        "schema": ADEU_SYMBOL_AUDIT_SESSION_CONFIG_SCHEMA,
        "session_mode": session_mode,
        "output_format": output_format,
        "include_evidence_refs": include_evidence_refs,
    }
    payload["semantic_hash"] = _sha256_canonical_payload(payload)
    payload["session_config_id"] = compute_session_config_id(
        {
            "schema": payload["schema"],
            "session_mode": payload["session_mode"],
            "output_format": payload["output_format"],
            "include_evidence_refs": payload["include_evidence_refs"],
            "semantic_hash": payload["semantic_hash"],
        }
    )
    return payload


def build_symbol_audit_session_config(
    *,
    session_mode: str,
    output_format: str,
    include_evidence_refs: bool,
) -> SymbolAuditSessionConfig:
    payload = _build_session_config_payload(
        session_mode=session_mode,
        output_format=output_format,
        include_evidence_refs=include_evidence_refs,
    )
    return SymbolAuditSessionConfig.model_validate(payload)


def _materialize_session_config(
    session_config: SymbolAuditSessionConfig | dict[str, object],
) -> tuple[SymbolAuditSessionConfig | None, str | None, OutputFormat | None]:
    if isinstance(session_config, SymbolAuditSessionConfig):
        return session_config, None, session_config.output_format

    raw_session_mode = session_config.get("session_mode")
    raw_output_format = session_config.get("output_format")
    raw_include_evidence_refs = session_config.get("include_evidence_refs")
    preferred_output_format: OutputFormat | None
    if raw_output_format == "json":
        preferred_output_format = "json"
    elif raw_output_format == "text":
        preferred_output_format = "text"
    else:
        preferred_output_format = None

    if raw_session_mode != "read_only_helper_render":
        return None, "session_mode must equal read_only_helper_render", preferred_output_format
    if raw_output_format not in {"text", "json"}:
        return None, "output_format must equal one of: json, text", preferred_output_format
    if not isinstance(raw_include_evidence_refs, bool):
        return None, "include_evidence_refs must be boolean", preferred_output_format

    config = build_symbol_audit_session_config(
        session_mode=raw_session_mode,
        output_format=raw_output_format,
        include_evidence_refs=raw_include_evidence_refs,
    )
    return config, None, config.output_format


def _project_audit_rows(
    *,
    semantic_audit: SymbolSemanticAudit,
    include_evidence_refs: bool,
) -> list[dict[str, object]]:
    projected_rows: list[dict[str, object]] = []
    for entry in semantic_audit.audit_entries:
        row: dict[str, object] = {
            "symbol_id": entry.symbol_id,
            "audit_status": entry.audit_status,
            "confidence_band": entry.confidence_band,
            "role_summary": entry.role_summary,
            "architectural_purpose": entry.architectural_purpose,
            "local_behavior_summary": entry.local_behavior_summary,
            "inputs_outputs_summary": entry.inputs_outputs_summary,
            "side_effect_profile": entry.side_effect_profile,
            "dependency_position": entry.dependency_position,
            "likely_canonical_family": entry.likely_canonical_family,
            "overlap_candidate_symbol_ids": entry.overlap_candidate_symbol_ids,
            "uncertainty_notes": entry.uncertainty_notes,
        }
        if entry.abstraction_candidate_notes is not None:
            row["abstraction_candidate_notes"] = entry.abstraction_candidate_notes
        if include_evidence_refs:
            row["evidence_refs"] = [
                evidence.model_dump(mode="json") for evidence in entry.evidence_refs
            ]
        projected_rows.append(row)
    return projected_rows


def _render_success_output(
    *,
    semantic_audit: SymbolSemanticAudit,
    output_format: OutputFormat,
    include_evidence_refs: bool,
) -> str:
    projected_rows = _project_audit_rows(
        semantic_audit=semantic_audit,
        include_evidence_refs=include_evidence_refs,
    )
    if output_format == "json":
        return _dump_canonical_json(
            {
                "scope_manifest_ref": semantic_audit.scope_manifest_ref,
                "census_hash": semantic_audit.census_hash,
                "audit_hash": semantic_audit.audit_hash,
                "semantic_vocabulary_posture": semantic_audit.semantic_vocabulary_posture,
                "spu_name": semantic_audit.spu_name,
                "spu_version": semantic_audit.spu_version,
                "include_evidence_refs": include_evidence_refs,
                "audit_entries": projected_rows,
            }
        )

    lines = [
        f"scope_manifest_ref={semantic_audit.scope_manifest_ref}",
        f"census_hash={semantic_audit.census_hash}",
        f"audit_hash={semantic_audit.audit_hash}",
        f"semantic_vocabulary_posture={semantic_audit.semantic_vocabulary_posture}",
        f"spu_name={semantic_audit.spu_name}",
        f"spu_version={semantic_audit.spu_version}",
        f"include_evidence_refs={str(include_evidence_refs).lower()}",
    ]
    for row in projected_rows:
        lines.append(
            " | ".join(
                [
                    f"symbol_id={row['symbol_id']}",
                    f"audit_status={row['audit_status']}",
                    f"confidence_band={row['confidence_band']}",
                    f"likely_canonical_family={row['likely_canonical_family']}",
                    f"role_summary={row['role_summary']}",
                ]
            )
        )
        if include_evidence_refs:
            evidence_parts = [
                f"{item['evidence_kind']}={item['detail']}"
                for item in row["evidence_refs"]  # type: ignore[index]
            ]
            lines.append(f"evidence_refs={' | '.join(evidence_parts)}")
    return "\n".join(lines)


def _render_failure_output(
    *,
    session_status: SessionStatus,
    reason: str,
    output_format: OutputFormat | None,
) -> str:
    if output_format == "json":
        return _dump_canonical_json(
            {
                "session_status": session_status,
                "reason": reason,
            }
        )
    return f"session_status={session_status}\nreason={reason}"


def _build_session_artifact(
    *,
    scope_manifest_ref: str,
    census_hash: str,
    audit_hash: str,
    session_config_ref: str,
    session_status: SessionStatus,
    rendered_output: str,
) -> SymbolAuditSession:
    exit_code = {
        "completed_clean": 0,
        "fail_closed_input_mismatch": 1,
        "fail_closed_invalid_config": 2,
    }[session_status]
    payload: dict[str, object] = {
        "schema": "adeu_symbol_audit_session@1",
        "scope_manifest_ref": scope_manifest_ref,
        "census_hash": census_hash,
        "audit_hash": audit_hash,
        "session_config_ref": session_config_ref,
        "session_status": session_status,
        "rendered_output": rendered_output,
        "exit_code": exit_code,
    }
    payload["session_hash"] = _sha256_canonical_payload(payload)
    payload["session_id"] = compute_session_id(
        {
            "schema": payload["schema"],
            "scope_manifest_ref": payload["scope_manifest_ref"],
            "census_hash": payload["census_hash"],
            "audit_hash": payload["audit_hash"],
            "session_config_ref": payload["session_config_ref"],
            "session_status": payload["session_status"],
            "rendered_output": payload["rendered_output"],
            "exit_code": payload["exit_code"],
            "session_hash": payload["session_hash"],
        }
    )
    return SymbolAuditSession.model_validate(payload)


def _artifact_stack_mismatch_reason(
    *,
    scope_manifest: SymbolAuditScopeManifest,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
    semantic_audit: SymbolSemanticAudit,
) -> str | None:
    if census.scope_manifest_ref != scope_manifest.scope_manifest_id:
        return "census scope_manifest_ref must equal the consumed scope_manifest_id"
    if census.source_files != scope_manifest.source_files:
        return "census source_files must equal the consumed manifest source_files"
    if coverage_report.scope_manifest_ref != census.scope_manifest_ref:
        return "coverage scope_manifest_ref must equal census scope_manifest_ref"
    if coverage_report.census_scope_manifest_ref != census.scope_manifest_ref:
        return "coverage census_scope_manifest_ref must equal census scope_manifest_ref"
    if coverage_report.census_hash != census.census_hash:
        return "coverage census_hash must equal census census_hash"
    if coverage_report.coverage_status != "closed_clean":
        return "coverage coverage_status must equal closed_clean"
    if semantic_audit.scope_manifest_ref != census.scope_manifest_ref:
        return "semantic audit scope_manifest_ref must equal census scope_manifest_ref"
    if semantic_audit.census_hash != census.census_hash:
        return "semantic audit census_hash must equal census census_hash"
    if semantic_audit.semantic_vocabulary_posture != RELEASED_SEMANTIC_VOCABULARY_POSTURE:
        return (
            "semantic audit semantic_vocabulary_posture must equal "
            "explicit_independence_from_v49"
        )
    census_symbol_ids = [entry.symbol_id for entry in census.symbols]
    audit_symbol_ids = [entry.symbol_id for entry in semantic_audit.audit_entries]
    if audit_symbol_ids != census_symbol_ids:
        return "semantic audit entries must remain aligned with census symbol_id order"
    return None


def build_symbol_audit_session(
    *,
    scope_manifest: SymbolAuditScopeManifest,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
    semantic_audit: SymbolSemanticAudit,
    session_config: SymbolAuditSessionConfig | dict[str, object],
) -> SymbolAuditSession:
    materialized_config, config_error, preferred_output_format = _materialize_session_config(
        session_config
    )
    if materialized_config is None:
        attempted_payload = (
            session_config
            if isinstance(session_config, dict)
            else session_config.model_dump(mode="json")
        )
        session_mode = (
            attempted_payload.get("session_mode")
            if isinstance(attempted_payload.get("session_mode"), str)
            else "invalid_session_mode"
        )
        output_format = (
            attempted_payload.get("output_format")
            if isinstance(attempted_payload.get("output_format"), str)
            else "invalid_output_format"
        )
        include_evidence_refs = attempted_payload.get("include_evidence_refs")
        session_config_payload = _build_session_config_payload(
            session_mode=session_mode,
            output_format=output_format,
            include_evidence_refs=include_evidence_refs,
        )
        return _build_session_artifact(
            scope_manifest_ref=scope_manifest.scope_manifest_id,
            census_hash=census.census_hash,
            audit_hash=semantic_audit.audit_hash,
            session_config_ref=str(session_config_payload["session_config_id"]),
            session_status="fail_closed_invalid_config",
            rendered_output=_render_failure_output(
                session_status="fail_closed_invalid_config",
                reason=config_error or "invalid session config",
                output_format=preferred_output_format,
            ),
        )

    mismatch_reason = _artifact_stack_mismatch_reason(
        scope_manifest=scope_manifest,
        census=census,
        coverage_report=coverage_report,
        semantic_audit=semantic_audit,
    )
    if mismatch_reason is not None:
        return _build_session_artifact(
            scope_manifest_ref=scope_manifest.scope_manifest_id,
            census_hash=census.census_hash,
            audit_hash=semantic_audit.audit_hash,
            session_config_ref=materialized_config.session_config_id,
            session_status="fail_closed_input_mismatch",
            rendered_output=_render_failure_output(
                session_status="fail_closed_input_mismatch",
                reason=mismatch_reason,
                output_format=materialized_config.output_format,
            ),
        )

    return _build_session_artifact(
        scope_manifest_ref=scope_manifest.scope_manifest_id,
        census_hash=census.census_hash,
        audit_hash=semantic_audit.audit_hash,
        session_config_ref=materialized_config.session_config_id,
        session_status="completed_clean",
        rendered_output=_render_success_output(
            semantic_audit=semantic_audit,
            output_format=materialized_config.output_format,
            include_evidence_refs=materialized_config.include_evidence_refs,
        ),
    )


__all__ = [
    "RELEASED_SEMANTIC_VOCABULARY_POSTURE",
    "build_symbol_audit_session",
    "build_symbol_audit_session_config",
]
