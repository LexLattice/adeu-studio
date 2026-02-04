from __future__ import annotations

from typing import Any

from adeu_ir import (
    AdeuIR,
    CheckMetrics,
    CheckReason,
    CheckReport,
    ReasonCode,
    ReasonSeverity,
    TraceItem,
)
from pydantic import ValidationError

from .mode import KernelMode

SUPPORTED_SCHEMA_VERSION = "adeu.ir.v0"


def _zero_metrics() -> CheckMetrics:
    return CheckMetrics(
        num_statements=0,
        num_exceptions=0,
        num_bridges=0,
        num_ambiguities=0,
    )


def _metrics(ir: AdeuIR) -> CheckMetrics:
    return CheckMetrics(
        num_statements=len(ir.D_norm.statements),
        num_exceptions=len(ir.D_norm.exceptions),
        num_bridges=len(ir.bridges),
        num_ambiguities=len(ir.ambiguity),
    )


def _finalize_report(
    *,
    metrics: CheckMetrics,
    reasons: list[CheckReason],
    trace: list[TraceItem],
) -> CheckReport:
    has_error = any(r.severity == ReasonSeverity.ERROR for r in reasons)
    has_warn = any(r.severity == ReasonSeverity.WARN for r in reasons)

    if has_error:
        status: str = "REFUSE"
    elif has_warn:
        status = "WARN"
    else:
        status = "PASS"

    return CheckReport(status=status, reason_codes=reasons, trace=trace, metrics=metrics)


def _check_time_scope(ir: AdeuIR, *, mode: KernelMode) -> tuple[list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []

    for stmt in ir.D_norm.statements:
        jurisdiction = (stmt.scope.jurisdiction or "").strip()
        if not jurisdiction:
            reasons.append(
                CheckReason(
                    code=ReasonCode.SCOPE_JURISDICTION_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="scope.jurisdiction is required",
                    object_id=stmt.id,
                )
            )

        ts = stmt.scope.time_about
        if ts.kind == "unspecified":
            time_severity = (
                ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
            )
            reasons.append(
                CheckReason(
                    code=ReasonCode.SCOPE_TIME_MISSING,
                    severity=time_severity,
                    message="scope.time_about.kind='unspecified'",
                    object_id=stmt.id,
                )
            )
            if ts.start is not None or ts.end is not None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message="unspecified time_about must not include start/end",
                        object_id=stmt.id,
                    )
                )
            continue

        if ts.kind in ("between", "during"):
            if ts.start is None or ts.end is None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_MISSING,
                        severity=ReasonSeverity.ERROR,
                        message=f"time_about.kind={ts.kind!r} requires start and end",
                        object_id=stmt.id,
                    )
                )
            elif ts.start >= ts.end:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message="time_about.start must be < time_about.end",
                        object_id=stmt.id,
                    )
                )
            continue

        if ts.kind == "at":
            if ts.start is None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_MISSING,
                        severity=ReasonSeverity.ERROR,
                        message="time_about.kind='at' requires start",
                        object_id=stmt.id,
                    )
                )
            if ts.end is not None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message="time_about.kind='at' must not include end",
                        object_id=stmt.id,
                    )
                )
            continue

        if ts.kind in ("before", "after"):
            if ts.start is None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_MISSING,
                        severity=ReasonSeverity.ERROR,
                        message=f"time_about.kind={ts.kind!r} requires start reference point",
                        object_id=stmt.id,
                    )
                )
            if ts.end is not None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message=f"time_about.kind={ts.kind!r} must not include end",
                        object_id=stmt.id,
                    )
                )
            continue

        reasons.append(
            CheckReason(
                code=ReasonCode.SCOPE_TIME_INVALID,
                severity=ReasonSeverity.ERROR,
                message=f"Unrecognized time_about.kind: {ts.kind!r}",
                object_id=stmt.id,
            )
        )

    return reasons, TraceItem(
        rule_id="time_scope/validate",
        because=[r.code for r in reasons],
        affected_ids=[s.id for s in ir.D_norm.statements],
    )


def _check_bridges(ir: AdeuIR) -> tuple[list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []

    for b in ir.bridges:
        if b.status == "certified" and b.validator is None:
            reasons.append(
                CheckReason(
                    code=ReasonCode.BRIDGE_CERTIFIED_VALIDATOR_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="certified bridge requires validator",
                    object_id=b.id,
                )
            )

        if b.bridge_type == "u_to_dnorm":
            if not (b.from_channel == "U" and b.to_channel == "D_norm"):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.BRIDGE_INVALID_CHANNEL_PAIR,
                        severity=ReasonSeverity.ERROR,
                        message="u_to_dnorm requires from_channel='U' and to_channel='D_norm'",
                        object_id=b.id,
                    )
                )
            if not (b.authority_ref or (b.validator and b.validator.kind == "authority_doc")):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.BRIDGE_U_TO_DNORM_AUTHORITY_MISSING,
                        severity=ReasonSeverity.ERROR,
                        message=(
                            "u_to_dnorm requires authority_ref "
                            "(or validator.kind='authority_doc')"
                        ),
                        object_id=b.id,
                    )
                )

        if b.bridge_type == "u_to_e":
            if not (b.from_channel == "U" and b.to_channel == "E"):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.BRIDGE_INVALID_CHANNEL_PAIR,
                        severity=ReasonSeverity.ERROR,
                        message="u_to_e requires from_channel='U' and to_channel='E'",
                        object_id=b.id,
                    )
                )
            if not (b.calibration_tag or (b.validator and b.validator.kind == "calibration")):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.BRIDGE_U_TO_E_CALIBRATION_MISSING,
                        severity=ReasonSeverity.ERROR,
                        message="u_to_e requires calibration_tag (or validator.kind='calibration')",
                        object_id=b.id,
                    )
                )

        if b.bridge_type == "e_to_dnorm":
            if not (b.from_channel == "E" and b.to_channel == "D_norm"):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.BRIDGE_INVALID_CHANNEL_PAIR,
                        severity=ReasonSeverity.ERROR,
                        message="e_to_dnorm requires from_channel='E' and to_channel='D_norm'",
                        object_id=b.id,
                    )
                )

        if b.bridge_type == "o_to_dnorm":
            if not (b.from_channel == "O" and b.to_channel == "D_norm"):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.BRIDGE_INVALID_CHANNEL_PAIR,
                        severity=ReasonSeverity.ERROR,
                        message="o_to_dnorm requires from_channel='O' and to_channel='D_norm'",
                        object_id=b.id,
                    )
                )

    return reasons, TraceItem(
        rule_id="bridges/gating",
        because=[r.code for r in reasons],
        affected_ids=[b.id for b in ir.bridges],
    )


def _check_norm_completeness(
    ir: AdeuIR, *, mode: KernelMode
) -> tuple[list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []

    for stmt in ir.D_norm.statements:
        if stmt.subject.ref_type == "text" and not stmt.subject.text.strip():
            reasons.append(
                CheckReason(
                    code=ReasonCode.NORM_SUBJECT_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="subject must not be empty",
                    object_id=stmt.id,
                )
            )

        if not stmt.action.verb.strip():
            reasons.append(
                CheckReason(
                    code=ReasonCode.NORM_ACTION_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="action.verb is required",
                    object_id=stmt.id,
                )
            )

        prov = stmt.provenance
        has_prov = bool(
            (prov.doc_ref and prov.doc_ref.strip())
            or prov.span
            or (prov.quote and prov.quote.strip())
        )
        if not has_prov:
            reasons.append(
                CheckReason(
                    code=ReasonCode.PROVENANCE_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="provenance requires doc_ref and/or span and/or quote",
                    object_id=stmt.id,
                )
            )

        if stmt.condition is not None:
            if stmt.condition.kind == "text_only":
                condition_severity = (
                    ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
                )
                reasons.append(
                    CheckReason(
                        code=ReasonCode.CONDITION_UNDISCHARGED,
                        severity=condition_severity,
                        message="condition.kind='text_only' is not machine-checkable",
                        object_id=stmt.id,
                    )
                )
            if stmt.condition.kind == "predicate" and not (
                stmt.condition.predicate and stmt.condition.predicate.strip()
            ):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.CONDITION_UNDISCHARGED,
                        severity=ReasonSeverity.ERROR,
                        message="condition.kind='predicate' requires condition.predicate",
                        object_id=stmt.id,
                    )
                )

    return reasons, TraceItem(
        rule_id="dnorm/completeness",
        because=[r.code for r in reasons],
        affected_ids=[s.id for s in ir.D_norm.statements],
        notes="Checks required fields and provenance for D_norm statements.",
    )


def _check_exceptions(ir: AdeuIR, *, mode: KernelMode) -> tuple[list[CheckReason], TraceItem]:
    del mode  # reserved for future: predicate validation and strict exception reasoning.

    reasons: list[CheckReason] = []
    statement_ids = {s.id for s in ir.D_norm.statements}

    applies_index: dict[str, list[str]] = {sid: [] for sid in statement_ids}

    for ex in ir.D_norm.exceptions:
        prov = ex.provenance
        has_prov = bool(
            (prov.doc_ref and prov.doc_ref.strip())
            or prov.span
            or (prov.quote and prov.quote.strip())
        )
        if not has_prov:
            reasons.append(
                CheckReason(
                    code=ReasonCode.PROVENANCE_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="exception provenance requires doc_ref and/or span and/or quote",
                    object_id=ex.id,
                )
            )

        if not ex.applies_to:
            reasons.append(
                CheckReason(
                    code=ReasonCode.EXCEPTION_ORPHANED,
                    severity=ReasonSeverity.ERROR,
                    message="exception.applies_to must not be empty",
                    object_id=ex.id,
                )
            )
            continue

        for target_id in ex.applies_to:
            if target_id not in statement_ids:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.EXCEPTION_ORPHANED,
                        severity=ReasonSeverity.ERROR,
                        message=f"exception references unknown statement id: {target_id!r}",
                        object_id=ex.id,
                    )
                )
                continue
            applies_index[target_id].append(ex.id)

    for stmt_id, ex_ids in applies_index.items():
        if len(ex_ids) > 1:
            reasons.append(
                CheckReason(
                    code=ReasonCode.EXCEPTION_PRECEDENCE_UNDETERMINED,
                    severity=ReasonSeverity.WARN,
                    message="multiple exceptions apply; precedence is not determined in v0",
                    object_id=stmt_id,
                )
            )

    return reasons, TraceItem(
        rule_id="dnorm/exceptions",
        because=[r.code for r in reasons],
        affected_ids=[e.id for e in ir.D_norm.exceptions],
        notes="Validates exception attachment and basic precedence flags.",
    )


def _ref_key(ref: object) -> tuple:
    ref_type = getattr(ref, "ref_type", None)
    if ref_type == "text":
        return ("text", ref.text)  # type: ignore[attr-defined]
    if ref_type == "entity":
        return ("entity", ref.entity_id)  # type: ignore[attr-defined]
    if ref_type == "def":
        return ("def", ref.def_id)  # type: ignore[attr-defined]
    if ref_type == "doc":
        return ("doc", ref.doc_ref)  # type: ignore[attr-defined]
    return ("unknown",)


def _time_interval(ts) -> tuple[object | None, object | None, bool]:
    """
    Returns (start, end, unknown). None start means -inf, None end means +inf.
    """
    if ts.kind == "unspecified":
        return None, None, True

    if ts.kind in ("between", "during"):
        if ts.start is None or ts.end is None:
            return None, None, True
        return ts.start, ts.end, False

    if ts.kind == "at":
        if ts.start is None:
            return None, None, True
        return ts.start, ts.start, False

    if ts.kind == "before":
        if ts.start is None:
            return None, None, True
        return None, ts.start, False

    if ts.kind == "after":
        if ts.start is None:
            return None, None, True
        return ts.start, None, False

    return None, None, True


def _intervals_overlap(a_start, a_end, b_start, b_end) -> bool:
    def max_start(x, y):
        if x is None:
            return y
        if y is None:
            return x
        return max(x, y)

    def min_end(x, y):
        if x is None:
            return y
        if y is None:
            return x
        return min(x, y)

    latest_start = max_start(a_start, b_start)
    earliest_end = min_end(a_end, b_end)

    if earliest_end is None or latest_start is None:
        return True
    return latest_start <= earliest_end


def _check_conflicts(ir: AdeuIR) -> tuple[list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []
    statements = ir.D_norm.statements

    for i in range(len(statements)):
        a = statements[i]
        for j in range(i + 1, len(statements)):
            b = statements[j]

            kinds = {a.kind, b.kind}
            if kinds != {"obligation", "prohibition"}:
                continue

            if (a.scope.jurisdiction or "").strip() != (b.scope.jurisdiction or "").strip():
                continue

            if _ref_key(a.subject) != _ref_key(b.subject):
                continue

            a_obj = _ref_key(a.action.object) if a.action.object is not None else None
            b_obj = _ref_key(b.action.object) if b.action.object is not None else None
            if (a.action.verb, a_obj) != (b.action.verb, b_obj):
                continue

            a_start, a_end, a_unknown = _time_interval(a.scope.time_about)
            b_start, b_end, b_unknown = _time_interval(b.scope.time_about)
            if a_unknown or b_unknown:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.CONFLICT_OVERLAPPING_SCOPE_UNRESOLVED,
                        severity=ReasonSeverity.WARN,
                        message="Potential conflict, but scope overlap is unresolved (time_about).",
                        object_id=a.id,
                    )
                )
                continue

            if _intervals_overlap(a_start, a_end, b_start, b_end):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.CONFLICT_OBLIGATION_VS_PROHIBITION,
                        severity=ReasonSeverity.ERROR,
                        message=f"Conflict between {a.id!r} and {b.id!r} in overlapping scope.",
                        object_id=a.id,
                    )
                )

    return reasons, TraceItem(
        rule_id="dnorm/conflicts",
        because=[r.code for r in reasons],
        affected_ids=[s.id for s in statements],
        notes="Detects obligation vs prohibition conflicts in overlapping scope.",
    )


def _check_resolution(ir: AdeuIR) -> tuple[list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []

    entity_ids = {e.id for e in ir.O.entities}
    def_ids = {d.id for d in ir.O.definitions}

    def check_ref(ref, *, owner_id: str) -> None:
        if ref.ref_type == "entity" and ref.entity_id not in entity_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.DEF_ENTITY_UNRESOLVED,
                    severity=ReasonSeverity.WARN,
                    message=f"Unresolved EntityRef: {ref.entity_id!r}",
                    object_id=owner_id,
                )
            )
        if ref.ref_type == "def" and ref.def_id not in def_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.DEF_TERM_UNRESOLVED,
                    severity=ReasonSeverity.WARN,
                    message=f"Unresolved DefinitionRef: {ref.def_id!r}",
                    object_id=owner_id,
                )
            )

    for stmt in ir.D_norm.statements:
        check_ref(stmt.subject, owner_id=stmt.id)
        if stmt.action.object is not None:
            check_ref(stmt.action.object, owner_id=stmt.id)

    return reasons, TraceItem(
        rule_id="refs/resolve",
        because=[r.code for r in reasons],
        affected_ids=[s.id for s in ir.D_norm.statements],
        notes="Flags unresolved EntityRef/DefinitionRef usages.",
    )


def check(raw: Any, *, mode: KernelMode = KernelMode.STRICT) -> CheckReport:
    if isinstance(raw, dict):
        schema_version = raw.get("schema_version")
        if schema_version is not None and schema_version != SUPPORTED_SCHEMA_VERSION:
            return CheckReport(
                status="REFUSE",
                reason_codes=[
                    CheckReason(
                        code=ReasonCode.UNSUPPORTED_SCHEMA_VERSION,
                        severity=ReasonSeverity.ERROR,
                        message=f"Unsupported schema_version: {schema_version!r}",
                        json_path="/schema_version",
                    )
                ],
                trace=[TraceItem(rule_id="parse/schema_version")],
                metrics=_zero_metrics(),
            )

    try:
        ir = AdeuIR.model_validate(raw)
    except ValidationError as e:
        return CheckReport(
            status="REFUSE",
            reason_codes=[
                CheckReason(
                    code=ReasonCode.SCHEMA_INVALID,
                    severity=ReasonSeverity.ERROR,
                    message=str(e),
                )
            ],
            trace=[TraceItem(rule_id="parse/validation_error")],
            metrics=_zero_metrics(),
        )

    metrics = _metrics(ir)
    reasons: list[CheckReason] = []
    trace: list[TraceItem] = [TraceItem(rule_id="parse/ok")]

    time_reasons, time_trace = _check_time_scope(ir, mode=mode)
    reasons.extend(time_reasons)
    trace.append(time_trace)

    bridge_reasons, bridge_trace = _check_bridges(ir)
    reasons.extend(bridge_reasons)
    trace.append(bridge_trace)

    completeness_reasons, completeness_trace = _check_norm_completeness(ir, mode=mode)
    reasons.extend(completeness_reasons)
    trace.append(completeness_trace)

    exception_reasons, exception_trace = _check_exceptions(ir, mode=mode)
    reasons.extend(exception_reasons)
    trace.append(exception_trace)

    conflict_reasons, conflict_trace = _check_conflicts(ir)
    reasons.extend(conflict_reasons)
    trace.append(conflict_trace)

    resolution_reasons, resolution_trace = _check_resolution(ir)
    reasons.extend(resolution_reasons)
    trace.append(resolution_trace)

    return _finalize_report(metrics=metrics, reasons=reasons, trace=trace)
