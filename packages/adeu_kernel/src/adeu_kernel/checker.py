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


def check(raw: Any, *, mode: KernelMode = KernelMode.STRICT) -> CheckReport:
    del mode  # mode gates later checks; parse is always strict about shape/types.

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

    return CheckReport(
        status="PASS",
        reason_codes=[],
        trace=[TraceItem(rule_id="parse/ok")],
        metrics=_metrics(ir),
    )
