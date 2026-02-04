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

    return _finalize_report(metrics=metrics, reasons=reasons, trace=trace)
