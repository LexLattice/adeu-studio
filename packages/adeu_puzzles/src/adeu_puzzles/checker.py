from __future__ import annotations

from typing import Any

from adeu_ir import CheckMetrics, CheckReason, CheckReport, ReasonCode, ReasonSeverity, TraceItem
from adeu_kernel import KernelMode, ValidatorBackend, ValidatorRunRecord, build_validator_backend
from pydantic import ValidationError

from .models import KnightsKnavesPuzzle, _iter_expr_person_ids
from .solver import build_knights_knaves_request

SUPPORTED_PUZZLE_SCHEMA_VERSION = "adeu.puzzle.v0"


def _path(*parts: str | int) -> str:
    return "/" + "/".join(str(p).strip("/") for p in parts)


def _metrics(puzzle: KnightsKnavesPuzzle) -> CheckMetrics:
    return CheckMetrics(
        num_statements=len(puzzle.statements) + len(puzzle.assumptions),
        num_exceptions=0,
        num_bridges=0,
        num_ambiguities=0,
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
        status = "REFUSE"
    elif has_warn:
        status = "WARN"
    else:
        status = "PASS"
    return CheckReport(status=status, reason_codes=reasons, trace=trace, metrics=metrics)


def _validate_puzzle_hygiene(
    puzzle: KnightsKnavesPuzzle,
    *,
    mode: KernelMode,
) -> tuple[list[CheckReason], list[TraceItem]]:
    reasons: list[CheckReason] = []
    trace: list[TraceItem] = []

    for idx, statement in enumerate(puzzle.statements):
        if statement.text and (statement.provenance is None or statement.provenance.span is None):
            reasons.append(
                CheckReason(
                    code=ReasonCode.PUZZLE_PROVENANCE_MISSING,
                    severity=ReasonSeverity.WARN,
                    message="statement has text but no provenance span",
                    object_id=statement.id,
                    json_path=_path("statements", idx, "provenance"),
                )
            )

    for idx, assumption in enumerate(puzzle.assumptions):
        if assumption.text and (
            assumption.provenance is None or assumption.provenance.span is None
        ):
            reasons.append(
                CheckReason(
                    code=ReasonCode.PUZZLE_PROVENANCE_MISSING,
                    severity=ReasonSeverity.WARN,
                    message="assumption has text but no provenance span",
                    object_id=assumption.id,
                    json_path=_path("assumptions", idx, "provenance"),
                )
            )

    trace.append(
        TraceItem(
            rule_id="puzzle/provenance",
            because=[r.code for r in reasons if r.code == ReasonCode.PUZZLE_PROVENANCE_MISSING],
            affected_ids=[s.id for s in puzzle.statements] + [a.id for a in puzzle.assumptions],
            notes="Encourages span provenance for text-derived puzzle statements.",
        )
    )

    known_people = {person.id for person in puzzle.people}
    for idx, statement in enumerate(puzzle.statements):
        if statement.speaker_id not in known_people:
            reasons.append(
                CheckReason(
                    code=ReasonCode.PUZZLE_ENTITY_UNRESOLVED,
                    severity=ReasonSeverity.ERROR,
                    message=f"statement references unknown speaker_id {statement.speaker_id!r}",
                    object_id=statement.id,
                    json_path=_path("statements", idx, "speaker_id"),
                )
            )
        for person_id in sorted(set(_iter_expr_person_ids(statement.claim))):
            if person_id not in known_people:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.PUZZLE_ENTITY_UNRESOLVED,
                        severity=ReasonSeverity.ERROR,
                        message=f"statement claim references unknown person_id {person_id!r}",
                        object_id=statement.id,
                        json_path=_path("statements", idx, "claim"),
                    )
                )

    for idx, assumption in enumerate(puzzle.assumptions):
        for person_id in sorted(set(_iter_expr_person_ids(assumption.claim))):
            if person_id not in known_people:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.PUZZLE_ENTITY_UNRESOLVED,
                        severity=ReasonSeverity.ERROR,
                        message=f"assumption claim references unknown person_id {person_id!r}",
                        object_id=assumption.id,
                        json_path=_path("assumptions", idx, "claim"),
                    )
                )

    if not puzzle.statements and not puzzle.assumptions:
        severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.PUZZLE_STATEMENT_UNRESOLVED,
                severity=severity,
                message="puzzle has no statements or assumptions",
                object_id=puzzle.puzzle_id,
                json_path=_path("statements"),
            )
        )

    trace.append(
        TraceItem(
            rule_id="puzzle/well_formedness",
            because=[
                r.code
                for r in reasons
                if r.code
                in {
                    ReasonCode.PUZZLE_ENTITY_UNRESOLVED,
                    ReasonCode.PUZZLE_STATEMENT_UNRESOLVED,
                }
            ],
            affected_ids=[puzzle.puzzle_id],
            notes="Checks puzzle entity and statement reference integrity.",
        )
    )
    return reasons, trace


def check_with_validator_runs(
    raw: Any,
    *,
    mode: KernelMode = KernelMode.STRICT,
    validator_backend: ValidatorBackend | None = None,
) -> tuple[CheckReport, list[ValidatorRunRecord]]:
    if isinstance(raw, dict):
        schema_version = raw.get("schema_version")
        if schema_version is not None and schema_version != SUPPORTED_PUZZLE_SCHEMA_VERSION:
            object_id = raw.get("puzzle_id") if isinstance(raw.get("puzzle_id"), str) else None
            return (
                CheckReport(
                    status="REFUSE",
                    reason_codes=[
                        CheckReason(
                            code=ReasonCode.PUZZLE_SCHEMA_INVALID,
                            severity=ReasonSeverity.ERROR,
                            message=f"Unsupported puzzle schema_version: {schema_version!r}",
                            object_id=object_id,
                            json_path=_path("schema_version"),
                        )
                    ],
                    trace=[TraceItem(rule_id="puzzle/parse_schema_version")],
                    metrics=CheckMetrics(
                        num_statements=0,
                        num_exceptions=0,
                        num_bridges=0,
                        num_ambiguities=0,
                    ),
                ),
                [],
            )

    try:
        puzzle = KnightsKnavesPuzzle.model_validate(raw)
    except ValidationError as exc:
        errors = exc.errors()
        chosen = errors[0] if errors else None
        json_path = None
        if chosen is not None:
            loc = chosen.get("loc", ())
            if isinstance(loc, (list, tuple)) and loc:
                json_path = "/" + "/".join(str(p) for p in loc)
        message = str(exc)
        if chosen is not None and isinstance(chosen.get("msg"), str):
            message = chosen["msg"]
        object_id = (
            raw.get("puzzle_id")
            if isinstance(raw, dict) and isinstance(raw.get("puzzle_id"), str)
            else None
        )
        return (
            CheckReport(
                status="REFUSE",
                reason_codes=[
                    CheckReason(
                        code=ReasonCode.PUZZLE_SCHEMA_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message=message,
                        object_id=object_id,
                        json_path=json_path,
                    )
                ],
                trace=[TraceItem(rule_id="puzzle/parse_validation_error")],
                metrics=CheckMetrics(
                    num_statements=0,
                    num_exceptions=0,
                    num_bridges=0,
                    num_ambiguities=0,
                ),
            ),
            [],
        )

    reasons: list[CheckReason] = []
    trace: list[TraceItem] = [TraceItem(rule_id="puzzle/parse_ok", affected_ids=[puzzle.puzzle_id])]
    metrics = _metrics(puzzle)

    hygiene_reasons, hygiene_trace = _validate_puzzle_hygiene(puzzle, mode=mode)
    reasons.extend(hygiene_reasons)
    trace.extend(hygiene_trace)

    has_structural_error = any(r.severity == ReasonSeverity.ERROR for r in reasons)
    if has_structural_error:
        return _finalize_report(metrics=metrics, reasons=reasons, trace=trace), []

    backend = validator_backend
    if backend is None:
        try:
            backend = build_validator_backend("z3")
        except RuntimeError as exc:
            severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
            reasons.append(
                CheckReason(
                    code=ReasonCode.PUZZLE_SOLVER_UNKNOWN,
                    severity=severity,
                    message=str(exc),
                    object_id=puzzle.puzzle_id,
                    json_path=_path("statements"),
                )
            )
            trace.append(
                TraceItem(
                    rule_id="puzzle/solver",
                    because=[ReasonCode.PUZZLE_SOLVER_UNKNOWN],
                    affected_ids=[puzzle.puzzle_id],
                )
            )
            return _finalize_report(metrics=metrics, reasons=reasons, trace=trace), []

    request = build_knights_knaves_request(puzzle)
    result = backend.run(request)
    run = ValidatorRunRecord(request=request, result=result)

    solver_because = [f"solver:{result.status}"]
    if result.status == "UNSAT":
        severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.PUZZLE_UNSAT,
                severity=severity,
                message=(
                    "puzzle constraints are UNSAT"
                    + (
                        f"; unsat core={','.join(sorted(result.evidence.unsat_core))}"
                        if result.evidence.unsat_core
                        else ""
                    )
                ),
                object_id=puzzle.puzzle_id,
                json_path=_path("statements"),
            )
        )
        solver_because.append(ReasonCode.PUZZLE_UNSAT)
    elif result.status == "INVALID_REQUEST":
        reasons.append(
            CheckReason(
                code=ReasonCode.PUZZLE_SOLVER_INVALID_REQUEST,
                severity=ReasonSeverity.ERROR,
                message=result.evidence.error or "puzzle solver rejected the request",
                object_id=puzzle.puzzle_id,
                json_path=_path("statements"),
            )
        )
        solver_because.append(ReasonCode.PUZZLE_SOLVER_INVALID_REQUEST)
    elif result.status == "TIMEOUT":
        severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.PUZZLE_SOLVER_TIMEOUT,
                severity=severity,
                message=result.evidence.error or "puzzle solver timed out",
                object_id=puzzle.puzzle_id,
                json_path=_path("statements"),
            )
        )
        solver_because.append(ReasonCode.PUZZLE_SOLVER_TIMEOUT)
    elif result.status == "UNKNOWN":
        severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.PUZZLE_SOLVER_UNKNOWN,
                severity=severity,
                message=result.evidence.error or "puzzle solver returned UNKNOWN",
                object_id=puzzle.puzzle_id,
                json_path=_path("statements"),
            )
        )
        solver_because.append(ReasonCode.PUZZLE_SOLVER_UNKNOWN)
    elif result.status == "ERROR":
        severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.VALIDATOR_BACKEND_ERROR,
                severity=severity,
                message=result.evidence.error or "puzzle solver backend error",
                object_id=puzzle.puzzle_id,
                json_path=_path("statements"),
            )
        )
        solver_because.append(ReasonCode.VALIDATOR_BACKEND_ERROR)

    trace.append(
        TraceItem(
            rule_id="puzzle/solver",
            because=solver_because,
            affected_ids=[puzzle.puzzle_id],
            notes="Runs SMT solver for Knights/Knaves consistency and assignments.",
        )
    )
    return _finalize_report(metrics=metrics, reasons=reasons, trace=trace), [run]


def check(
    raw: Any,
    *,
    mode: KernelMode = KernelMode.STRICT,
    validator_backend: ValidatorBackend | None = None,
) -> CheckReport:
    report, _ = check_with_validator_runs(raw, mode=mode, validator_backend=validator_backend)
    return report
