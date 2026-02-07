from __future__ import annotations

from typing import Any

from adeu_ir import CheckMetrics, CheckReason, CheckReport, ReasonCode, ReasonSeverity, TraceItem
from adeu_kernel import KernelMode, ValidatorBackend, ValidatorRunRecord, build_validator_backend
from pydantic import ValidationError

from .models import ConceptIR
from .solver import build_concept_coherence_request

SUPPORTED_CONCEPT_SCHEMA_VERSION = "adeu.concepts.v0"

_LAX_DOWNGRADABLE_CODES = {
    ReasonCode.CONCEPT_PROVENANCE_MISSING,
    ReasonCode.CONCEPT_SOLVER_INVALID_REQUEST,
}


def _path(*parts: str | int) -> str:
    return "/" + "/".join(str(part).strip("/") for part in parts)


def _metrics(concept: ConceptIR) -> CheckMetrics:
    return CheckMetrics(
        num_statements=len(concept.claims),
        num_exceptions=0,
        num_bridges=len(concept.links),
        num_ambiguities=len(concept.ambiguity),
    )


def _finalize_report(
    *,
    mode: KernelMode,
    metrics: CheckMetrics,
    reasons: list[CheckReason],
    trace: list[TraceItem],
) -> CheckReport:
    if not reasons:
        return CheckReport(status="PASS", reason_codes=[], trace=trace, metrics=metrics)

    has_error = any(reason.severity == ReasonSeverity.ERROR for reason in reasons)
    has_warn = any(reason.severity == ReasonSeverity.WARN for reason in reasons)

    if has_error:
        if mode == KernelMode.LAX:
            blocking_errors = [
                reason
                for reason in reasons
                if reason.severity == ReasonSeverity.ERROR
                and reason.code not in _LAX_DOWNGRADABLE_CODES
            ]
            status = "REFUSE" if blocking_errors else "WARN"
        else:
            status = "REFUSE"
    elif has_warn:
        status = "WARN"
    else:
        status = "PASS"

    return CheckReport(status=status, reason_codes=reasons, trace=trace, metrics=metrics)


def _parse_or_schema_error(raw: Any) -> tuple[ConceptIR | None, CheckReport | None]:
    if isinstance(raw, dict):
        schema_version = raw.get("schema_version")
        if schema_version is not None and schema_version != SUPPORTED_CONCEPT_SCHEMA_VERSION:
            object_id = raw.get("concept_id") if isinstance(raw.get("concept_id"), str) else None
            return None, CheckReport(
                status="REFUSE",
                reason_codes=[
                    CheckReason(
                        code=ReasonCode.CONCEPT_SCHEMA_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message=f"Unsupported concept schema_version: {schema_version!r}",
                        object_id=object_id,
                        json_path=_path("schema_version"),
                    )
                ],
                trace=[TraceItem(rule_id="concept/parse_schema_version")],
                metrics=CheckMetrics(
                    num_statements=0,
                    num_exceptions=0,
                    num_bridges=0,
                    num_ambiguities=0,
                ),
            )

    try:
        return ConceptIR.model_validate(raw), None
    except ValidationError as exc:
        errors = exc.errors()
        chosen = errors[0] if errors else None
        json_path = None
        if chosen is not None:
            loc = chosen.get("loc", ())
            if isinstance(loc, (list, tuple)) and loc:
                json_path = "/" + "/".join(str(part) for part in loc)
        message = chosen.get("msg") if isinstance(chosen, dict) else str(exc)
        object_id = (
            raw.get("concept_id")
            if isinstance(raw, dict) and isinstance(raw.get("concept_id"), str)
            else None
        )
        return None, CheckReport(
            status="REFUSE",
            reason_codes=[
                CheckReason(
                    code=ReasonCode.CONCEPT_SCHEMA_INVALID,
                    severity=ReasonSeverity.ERROR,
                    message=str(message),
                    object_id=object_id,
                    json_path=json_path,
                )
            ],
            trace=[TraceItem(rule_id="concept/parse_validation_error")],
            metrics=CheckMetrics(
                num_statements=0,
                num_exceptions=0,
                num_bridges=0,
                num_ambiguities=0,
            ),
        )


def _collect_hygiene_reasons(concept: ConceptIR, *, source_text: str | None) -> list[CheckReason]:
    reasons: list[CheckReason] = []
    term_ids = {term.id for term in concept.terms}
    sense_ids = {sense.id for sense in concept.senses}
    sense_term_by_id = {sense.id: sense.term_id for sense in concept.senses}
    senses_by_term: dict[str, list[str]] = {}

    for idx, sense in enumerate(concept.senses):
        senses_by_term.setdefault(sense.term_id, []).append(sense.id)
        if sense.term_id not in term_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_ENDPOINT_UNRESOLVED,
                    severity=ReasonSeverity.ERROR,
                    message=f"sense references unknown term_id {sense.term_id!r}",
                    object_id=sense.id,
                    json_path=_path("senses", idx, "term_id"),
                )
            )

    for idx, claim in enumerate(concept.claims):
        if claim.sense_id not in sense_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_ENDPOINT_UNRESOLVED,
                    severity=ReasonSeverity.ERROR,
                    message=f"claim references unknown sense_id {claim.sense_id!r}",
                    object_id=claim.id,
                    json_path=_path("claims", idx, "sense_id"),
                )
            )
        span = claim.provenance.span if claim.provenance is not None else None
        if span is None:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_PROVENANCE_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="claim requires provenance span",
                    object_id=claim.id,
                    json_path=_path("claims", idx, "provenance"),
                )
            )
            continue

        if span.start < 0 or span.end <= span.start:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_PROVENANCE_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="claim provenance span must satisfy 0 <= start < end",
                    object_id=claim.id,
                    json_path=_path("claims", idx, "provenance", "span"),
                )
            )

        elif source_text is not None and span.end > len(source_text):
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_PROVENANCE_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message=(
                        "claim provenance span end is out of bounds for provided source_text "
                        f"(end={span.end}, len={len(source_text)})"
                    ),
                    object_id=claim.id,
                    json_path=_path("claims", idx, "provenance", "span"),
                )
            )

    for idx, link in enumerate(concept.links):
        if link.src_sense_id not in sense_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_ENDPOINT_UNRESOLVED,
                    severity=ReasonSeverity.ERROR,
                    message=f"link source sense_id unresolved: {link.src_sense_id!r}",
                    object_id=link.id,
                    json_path=_path("links", idx, "src_sense_id"),
                )
            )
        if link.dst_sense_id not in sense_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_ENDPOINT_UNRESOLVED,
                    severity=ReasonSeverity.ERROR,
                    message=f"link destination sense_id unresolved: {link.dst_sense_id!r}",
                    object_id=link.id,
                    json_path=_path("links", idx, "dst_sense_id"),
                )
            )
        if link.kind == "incompatibility" and link.src_sense_id == link.dst_sense_id:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_SENSE_SELECTION_INVALID,
                    severity=ReasonSeverity.ERROR,
                    message="incompatibility self-loop is invalid",
                    object_id=link.id,
                    json_path=_path("links", idx),
                )
            )

    ambiguous_term_ids: set[str] = set()
    for idx, ambiguity in enumerate(concept.ambiguity):
        ambiguous_term_ids.add(ambiguity.term_id)
        if ambiguity.term_id not in term_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_ENDPOINT_UNRESOLVED,
                    severity=ReasonSeverity.ERROR,
                    message=f"ambiguity references unknown term_id {ambiguity.term_id!r}",
                    object_id=ambiguity.id,
                    json_path=_path("ambiguity", idx, "term_id"),
                )
            )

        option_set = set(ambiguity.options)
        if len(option_set) != len(ambiguity.options):
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_SENSE_SELECTION_INVALID,
                    severity=ReasonSeverity.ERROR,
                    message="ambiguity options must be unique",
                    object_id=ambiguity.id,
                    json_path=_path("ambiguity", idx, "options"),
                )
            )

        for option_idx, sense_id in enumerate(ambiguity.options):
            if sense_id not in sense_ids:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.CONCEPT_ENDPOINT_UNRESOLVED,
                        severity=ReasonSeverity.ERROR,
                        message=f"ambiguity option references unknown sense_id {sense_id!r}",
                        object_id=ambiguity.id,
                        json_path=_path("ambiguity", idx, "options", option_idx),
                    )
                )
                continue
            if sense_term_by_id.get(sense_id) != ambiguity.term_id:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.CONCEPT_SENSE_SELECTION_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message=(
                            "ambiguity options must reference senses belonging to "
                            "the ambiguity term"
                        ),
                        object_id=ambiguity.id,
                        json_path=_path("ambiguity", idx, "options", option_idx),
                    )
                )

    for idx, term in enumerate(concept.terms):
        has_sense = bool(senses_by_term.get(term.id))
        is_ambiguous = term.id in ambiguous_term_ids
        if not has_sense and not is_ambiguous:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_SENSE_SELECTION_INVALID,
                    severity=ReasonSeverity.ERROR,
                    message=f"term has no resolved sense and no ambiguity marker: {term.id!r}",
                    object_id=term.id,
                    json_path=_path("terms", idx),
                )
            )

    return reasons


def _apply_solver_result(
    *,
    concept: ConceptIR,
    status: str | None,
    error_message: str | None,
    unsat_core: list[str] | None,
    reasons: list[CheckReason],
    trace: list[TraceItem],
) -> None:
    if status is None:
        trace.append(
            TraceItem(
                rule_id="concept/solver",
                because=["solver:UNAVAILABLE"],
                affected_ids=[concept.concept_id],
                notes="Uses provided solver status when available.",
            )
        )
        return

    normalized_status = status.upper()
    solver_because = [f"solver:{normalized_status}"]
    if normalized_status == "UNSAT":
        core_msg = ",".join(sorted(unsat_core or []))
        reasons.append(
            CheckReason(
                code=ReasonCode.CONCEPT_INCOHERENT_UNSAT,
                severity=ReasonSeverity.ERROR,
                message=(
                    "concept composition constraints are UNSAT"
                    + (f"; unsat core={core_msg}" if core_msg else "")
                ),
                object_id=concept.concept_id,
                json_path=_path("links"),
            )
        )
        solver_because.append(ReasonCode.CONCEPT_INCOHERENT_UNSAT)
    elif normalized_status == "TIMEOUT":
        reasons.append(
            CheckReason(
                code=ReasonCode.CONCEPT_SOLVER_TIMEOUT,
                severity=ReasonSeverity.ERROR,
                message=error_message or "concept solver timed out",
                object_id=concept.concept_id,
                json_path=_path("links"),
            )
        )
        solver_because.append(ReasonCode.CONCEPT_SOLVER_TIMEOUT)
    elif normalized_status == "UNKNOWN":
        reasons.append(
            CheckReason(
                code=ReasonCode.CONCEPT_SOLVER_UNKNOWN,
                severity=ReasonSeverity.ERROR,
                message=error_message or "concept solver returned UNKNOWN",
                object_id=concept.concept_id,
                json_path=_path("links"),
            )
        )
        solver_because.append(ReasonCode.CONCEPT_SOLVER_UNKNOWN)
    elif normalized_status == "INVALID_REQUEST":
        reasons.append(
            CheckReason(
                code=ReasonCode.CONCEPT_SOLVER_INVALID_REQUEST,
                severity=ReasonSeverity.ERROR,
                message=error_message or "concept solver rejected request",
                object_id=concept.concept_id,
                json_path=_path("links"),
            )
        )
        solver_because.append(ReasonCode.CONCEPT_SOLVER_INVALID_REQUEST)
    elif normalized_status == "ERROR":
        reasons.append(
            CheckReason(
                code=ReasonCode.CONCEPT_SOLVER_ERROR,
                severity=ReasonSeverity.ERROR,
                message=error_message or "concept solver backend error",
                object_id=concept.concept_id,
                json_path=_path("links"),
            )
        )
        solver_because.append(ReasonCode.CONCEPT_SOLVER_ERROR)

    trace.append(
        TraceItem(
            rule_id="concept/solver",
            because=solver_because,
            affected_ids=[concept.concept_id],
            notes="Runs SMT coherence checks over sense selections and inferential links.",
        )
    )


def check_with_solver_status(
    raw: Any,
    *,
    solver_status: str | None,
    solver_error: str | None = None,
    solver_unsat_core: list[str] | None = None,
    mode: KernelMode = KernelMode.STRICT,
    source_text: str | None = None,
) -> CheckReport:
    concept, parse_error = _parse_or_schema_error(raw)
    if parse_error is not None:
        return parse_error
    assert concept is not None

    reasons = _collect_hygiene_reasons(concept, source_text=source_text)
    trace: list[TraceItem] = [
        TraceItem(rule_id="concept/parse_ok", affected_ids=[concept.concept_id]),
        TraceItem(
            rule_id="concept/hygiene",
            because=sorted({reason.code for reason in reasons}),
            affected_ids=[concept.concept_id],
            notes="Validates provenance, endpoint references, and sense selection constraints.",
        ),
    ]
    metrics = _metrics(concept)

    has_structural_error = any(reason.severity == ReasonSeverity.ERROR for reason in reasons)
    if has_structural_error:
        return _finalize_report(mode=mode, metrics=metrics, reasons=reasons, trace=trace)

    _apply_solver_result(
        concept=concept,
        status=solver_status,
        error_message=solver_error,
        unsat_core=solver_unsat_core,
        reasons=reasons,
        trace=trace,
    )
    return _finalize_report(mode=mode, metrics=metrics, reasons=reasons, trace=trace)


def check_with_validator_runs(
    raw: Any,
    *,
    mode: KernelMode = KernelMode.STRICT,
    source_text: str | None = None,
    validator_backend: ValidatorBackend | None = None,
) -> tuple[CheckReport, list[ValidatorRunRecord]]:
    concept, parse_error = _parse_or_schema_error(raw)
    if parse_error is not None:
        return parse_error, []
    assert concept is not None

    reasons = _collect_hygiene_reasons(concept, source_text=source_text)
    trace: list[TraceItem] = [
        TraceItem(rule_id="concept/parse_ok", affected_ids=[concept.concept_id]),
        TraceItem(
            rule_id="concept/hygiene",
            because=sorted({reason.code for reason in reasons}),
            affected_ids=[concept.concept_id],
            notes="Validates provenance, endpoint references, and sense selection constraints.",
        ),
    ]
    metrics = _metrics(concept)

    has_structural_error = any(reason.severity == ReasonSeverity.ERROR for reason in reasons)
    if has_structural_error:
        return _finalize_report(mode=mode, metrics=metrics, reasons=reasons, trace=trace), []

    backend = validator_backend
    if backend is None:
        try:
            backend = build_validator_backend("z3")
        except RuntimeError as exc:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONCEPT_SOLVER_ERROR,
                    severity=ReasonSeverity.ERROR,
                    message=str(exc),
                    object_id=concept.concept_id,
                    json_path=_path("links"),
                )
            )
            trace.append(
                TraceItem(
                    rule_id="concept/solver",
                    because=[ReasonCode.CONCEPT_SOLVER_ERROR],
                    affected_ids=[concept.concept_id],
                )
            )
            return _finalize_report(mode=mode, metrics=metrics, reasons=reasons, trace=trace), []

    request = build_concept_coherence_request(concept)
    result = backend.run(request)
    run = ValidatorRunRecord(request=request, result=result)

    _apply_solver_result(
        concept=concept,
        status=result.status,
        error_message=result.evidence.error,
        unsat_core=result.evidence.unsat_core,
        reasons=reasons,
        trace=trace,
    )
    return _finalize_report(mode=mode, metrics=metrics, reasons=reasons, trace=trace), [run]


def check(
    raw: Any,
    *,
    mode: KernelMode = KernelMode.STRICT,
    source_text: str | None = None,
    validator_backend: ValidatorBackend | None = None,
) -> CheckReport:
    report, _ = check_with_validator_runs(
        raw,
        mode=mode,
        source_text=source_text,
        validator_backend=validator_backend,
    )
    return report
