from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any

from adeu_ir import (
    AdeuIR,
    CheckMetrics,
    CheckReason,
    CheckReport,
    ExceptionClause,
    NormStatement,
    ReasonCode,
    ReasonSeverity,
    Ref,
    TraceItem,
    ValidatorAtomRef,
    ValidatorOrigin,
    ValidatorPayload,
    ValidatorRequest,
    ValidatorResult,
)
from pydantic import ValidationError

from .mode import KernelMode
from .predicate import (
    PredAnd,
    PredDefined,
    Predicate,
    PredicateParseError,
    PredNot,
    PredOr,
    PredRefersToDoc,
    evaluate_predicate,
    parse_predicate,
    referenced_def_ids,
)
from .validator import ValidatorBackend, build_validator_backend

SUPPORTED_SCHEMA_VERSION = "adeu.ir.v0"
MODALITY_AMBIGUITY_ISSUES = frozenset({"modality_ambiguity"})

def _path(*parts: str | int) -> str:
    return "/" + "/".join(str(p).strip("/") for p in parts)


@dataclass(frozen=True)
class EffectiveNorm:
    statement: NormStatement
    statement_idx: int
    defeated_by: tuple[str, ...] = ()
    narrowed_by: tuple[str, ...] = ()
    clarified_by: tuple[str, ...] = ()

    @property
    def is_defeated(self) -> bool:
        return bool(self.defeated_by)


@dataclass(frozen=True)
class ValidatorRunRecord:
    request: ValidatorRequest
    result: ValidatorResult


@dataclass(frozen=True)
class ConflictPair:
    assertion_name: str
    object_id: str
    json_path: str
    stmt_a_id: str
    stmt_a_idx: int
    stmt_b_id: str


def _json_path_hash(json_path: str) -> str:
    return hashlib.sha256(json_path.encode("utf-8")).hexdigest()[:12]


def _assertion_name(*, object_id: str, json_path: str) -> str:
    return f"a:{object_id}:{_json_path_hash(json_path)}"


def _smt_quote_symbol(symbol: str) -> str:
    safe = symbol.replace("|", "_")
    return f"|{safe}|"


def _sorted_duplicate_values(values: list[str]) -> list[str]:
    seen: set[str] = set()
    duplicates: set[str] = set()
    for value in values:
        if value in seen:
            duplicates.add(value)
        else:
            seen.add(value)
    return sorted(duplicates)


def _predicate_atom_symbol(*, kind: str, value: str) -> str:
    digest = hashlib.sha256(f"{kind}:{value}".encode("utf-8")).hexdigest()[:12]
    return f"p_{kind}_{digest}"


def _predicate_to_smt(
    predicate: Predicate,
    *,
    def_ids: set[str],
    doc_refs: set[str],
    atom_values: dict[str, bool],
) -> str:
    if isinstance(predicate, PredDefined):
        symbol = _predicate_atom_symbol(kind="def", value=predicate.def_id)
        atom_values[symbol] = predicate.def_id in def_ids
        return symbol
    if isinstance(predicate, PredRefersToDoc):
        symbol = _predicate_atom_symbol(kind="doc", value=predicate.doc_ref)
        atom_values[symbol] = predicate.doc_ref in doc_refs
        return symbol
    if isinstance(predicate, PredNot):
        inner = _predicate_to_smt(
            predicate.arg,
            def_ids=def_ids,
            doc_refs=doc_refs,
            atom_values=atom_values,
        )
        return f"(not {inner})"
    if isinstance(predicate, PredAnd):
        args = [
            _predicate_to_smt(arg, def_ids=def_ids, doc_refs=doc_refs, atom_values=atom_values)
            for arg in predicate.args
        ]
        return f"(and {' '.join(args)})"
    if isinstance(predicate, PredOr):
        args = [
            _predicate_to_smt(arg, def_ids=def_ids, doc_refs=doc_refs, atom_values=atom_values)
            for arg in predicate.args
        ]
        return f"(or {' '.join(args)})"
    raise AssertionError(f"unknown predicate node: {predicate!r}")


def _collect_doc_refs(ir: AdeuIR) -> set[str]:
    doc_refs: set[str] = set()

    doc_id = (ir.context.doc_id or "").strip()
    if doc_id:
        doc_refs.add(doc_id)

    def add_doc_ref(value: str | None) -> None:
        if value is None:
            return
        v = value.strip()
        if v:
            doc_refs.add(v)

    for e in ir.O.entities:
        if e.provenance is not None:
            add_doc_ref(e.provenance.doc_ref)

    for d in ir.O.definitions:
        if d.provenance is not None:
            add_doc_ref(d.provenance.doc_ref)

    for stmt in ir.D_norm.statements:
        add_doc_ref(stmt.provenance.doc_ref)

    for ex in ir.D_norm.exceptions:
        add_doc_ref(ex.provenance.doc_ref)

    for c in ir.D_phys.constraints:
        if c.provenance is not None:
            add_doc_ref(c.provenance.doc_ref)

    for e in ir.E.claims:
        if e.provenance is not None:
            add_doc_ref(e.provenance.doc_ref)

    for g in ir.U.goals:
        if g.provenance is not None:
            add_doc_ref(g.provenance.doc_ref)

    for b in ir.bridges:
        add_doc_ref(b.provenance.doc_ref)

    # Include typed DocRef values anywhere in the IR payload.
    def walk_doc_refs(value: object) -> None:
        if isinstance(value, dict):
            ref_type = value.get("ref_type")
            doc_ref = value.get("doc_ref")
            if ref_type == "doc" and isinstance(doc_ref, str):
                add_doc_ref(doc_ref)
            for nested in value.values():
                walk_doc_refs(nested)
            return
        if isinstance(value, list):
            for nested in value:
                walk_doc_refs(nested)

    walk_doc_refs(ir.model_dump(mode="json", exclude_none=True))

    return doc_refs

def _zero_metrics() -> CheckMetrics:
    return CheckMetrics(
        num_statements=0,
        num_exceptions=0,
        num_bridges=0,
        num_ambiguities=0,
    )


def _metrics(ir: AdeuIR) -> CheckMetrics:
    return ir.calculate_metrics()


def _validate_predicate_condition(
    *,
    condition_kind: str,
    condition_predicate: str | None,
    owner_id: str,
    missing_predicate_message: str,
    predicate_json_path: str,
    def_ids: set[str],
    mode: KernelMode,
) -> list[CheckReason]:
    if condition_kind != "predicate":
        return []

    reasons: list[CheckReason] = []
    if not (condition_predicate and condition_predicate.strip()):
        reasons.append(
            CheckReason(
                code=ReasonCode.CONDITION_UNDISCHARGED,
                severity=ReasonSeverity.ERROR,
                message=missing_predicate_message,
                object_id=owner_id,
                json_path=predicate_json_path,
            )
        )
        return reasons

    try:
        predicate = parse_predicate(condition_predicate)
    except PredicateParseError as e:
        pred_severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.CONDITION_PREDICATE_INVALID,
                severity=pred_severity,
                message=str(e),
                object_id=owner_id,
                json_path=predicate_json_path,
            )
        )
        return reasons

    pred_def_severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
    for def_id in sorted(referenced_def_ids(predicate)):
        if def_id not in def_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.DEF_TERM_UNRESOLVED,
                    severity=pred_def_severity,
                    message=f"Predicate references unknown def_id: {def_id!r}",
                    object_id=owner_id,
                    json_path=predicate_json_path,
                )
            )

    return reasons


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

    for idx, stmt in enumerate(ir.D_norm.statements):
        jurisdiction = (stmt.scope.jurisdiction or "").strip()
        if not jurisdiction:
            reasons.append(
                CheckReason(
                    code=ReasonCode.SCOPE_JURISDICTION_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="scope.jurisdiction is required",
                    object_id=stmt.id,
                    json_path=_path("D_norm", "statements", idx, "scope", "jurisdiction"),
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
                    json_path=_path("D_norm", "statements", idx, "scope", "time_about", "kind"),
                )
            )
            if ts.start is not None or ts.end is not None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message="unspecified time_about must not include start/end",
                        object_id=stmt.id,
                        json_path=_path("D_norm", "statements", idx, "scope", "time_about"),
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
                        json_path=_path("D_norm", "statements", idx, "scope", "time_about"),
                    )
                )
            elif ts.start >= ts.end:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message="time_about.start must be < time_about.end",
                        object_id=stmt.id,
                        json_path=_path(
                            "D_norm", "statements", idx, "scope", "time_about", "start"
                        ),
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
                        json_path=_path(
                            "D_norm", "statements", idx, "scope", "time_about", "start"
                        ),
                    )
                )
            if ts.end is not None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message="time_about.kind='at' must not include end",
                        object_id=stmt.id,
                        json_path=_path("D_norm", "statements", idx, "scope", "time_about", "end"),
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
                        json_path=_path(
                            "D_norm", "statements", idx, "scope", "time_about", "start"
                        ),
                    )
                )
            if ts.end is not None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.SCOPE_TIME_INVALID,
                        severity=ReasonSeverity.ERROR,
                        message=f"time_about.kind={ts.kind!r} must not include end",
                        object_id=stmt.id,
                        json_path=_path("D_norm", "statements", idx, "scope", "time_about", "end"),
                    )
                )
            continue

        reasons.append(
            CheckReason(
                code=ReasonCode.SCOPE_TIME_INVALID,
                severity=ReasonSeverity.ERROR,
                message=f"Unrecognized time_about.kind: {ts.kind!r}",
                object_id=stmt.id,
                json_path=_path("D_norm", "statements", idx, "scope", "time_about", "kind"),
            )
        )

    return reasons, TraceItem(
        rule_id="time_scope/validate",
        because=[r.code for r in reasons],
        affected_ids=[s.id for s in ir.D_norm.statements],
    )


def _check_bridges(ir: AdeuIR) -> tuple[list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []

    for idx, b in enumerate(ir.bridges):
        if b.status == "certified" and b.validator is None:
            reasons.append(
                CheckReason(
                    code=ReasonCode.BRIDGE_CERTIFIED_VALIDATOR_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="certified bridge requires validator",
                    object_id=b.id,
                    json_path=_path("bridges", idx, "validator"),
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
                        json_path=_path("bridges", idx, "bridge_type"),
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
                        json_path=_path("bridges", idx, "authority_ref"),
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
                        json_path=_path("bridges", idx, "bridge_type"),
                    )
                )
            if not (b.calibration_tag or (b.validator and b.validator.kind == "calibration")):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.BRIDGE_U_TO_E_CALIBRATION_MISSING,
                        severity=ReasonSeverity.ERROR,
                        message="u_to_e requires calibration_tag (or validator.kind='calibration')",
                        object_id=b.id,
                        json_path=_path("bridges", idx, "calibration_tag"),
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
                        json_path=_path("bridges", idx, "bridge_type"),
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
                        json_path=_path("bridges", idx, "bridge_type"),
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
    def_ids = {d.id for d in ir.O.definitions}

    for idx, stmt in enumerate(ir.D_norm.statements):
        if stmt.subject.ref_type == "text" and not stmt.subject.text.strip():
            reasons.append(
                CheckReason(
                    code=ReasonCode.NORM_SUBJECT_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="subject must not be empty",
                    object_id=stmt.id,
                    json_path=_path("D_norm", "statements", idx, "subject", "text"),
                )
            )

        if not stmt.action.verb.strip():
            reasons.append(
                CheckReason(
                    code=ReasonCode.NORM_ACTION_MISSING,
                    severity=ReasonSeverity.ERROR,
                    message="action.verb is required",
                    object_id=stmt.id,
                    json_path=_path("D_norm", "statements", idx, "action", "verb"),
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
                    json_path=_path("D_norm", "statements", idx, "provenance"),
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
                        json_path=_path("D_norm", "statements", idx, "condition", "kind"),
                    )
                )
            reasons.extend(
                _validate_predicate_condition(
                    condition_kind=stmt.condition.kind,
                    condition_predicate=stmt.condition.predicate,
                    owner_id=stmt.id,
                    missing_predicate_message=(
                        "condition.kind='predicate' requires condition.predicate"
                    ),
                    predicate_json_path=_path(
                        "D_norm", "statements", idx, "condition", "predicate"
                    ),
                    def_ids=def_ids,
                    mode=mode,
                )
            )

    return reasons, TraceItem(
        rule_id="dnorm/completeness",
        because=[r.code for r in reasons],
        affected_ids=[s.id for s in ir.D_norm.statements],
        notes="Checks required fields and provenance for D_norm statements.",
    )


def _check_exceptions(ir: AdeuIR, *, mode: KernelMode) -> tuple[list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []
    statement_ids = {s.id for s in ir.D_norm.statements}
    def_ids = {d.id for d in ir.O.definitions}

    for ex_idx, ex in enumerate(ir.D_norm.exceptions):
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
                    json_path=_path("D_norm", "exceptions", ex_idx, "provenance"),
                )
            )

        if not ex.applies_to:
            reasons.append(
                CheckReason(
                    code=ReasonCode.EXCEPTION_ORPHANED,
                    severity=ReasonSeverity.ERROR,
                    message="exception.applies_to must not be empty",
                    object_id=ex.id,
                    json_path=_path("D_norm", "exceptions", ex_idx, "applies_to"),
                )
            )
            continue

        reasons.extend(
            _validate_predicate_condition(
                condition_kind=ex.condition.kind,
                condition_predicate=ex.condition.predicate,
                owner_id=ex.id,
                missing_predicate_message=(
                    "exception.condition.kind='predicate' requires exception.condition.predicate"
                ),
                predicate_json_path=_path(
                    "D_norm", "exceptions", ex_idx, "condition", "predicate"
                ),
                def_ids=def_ids,
                mode=mode,
            )
        )

        for target_idx, target_id in enumerate(ex.applies_to):
            if target_id not in statement_ids:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.EXCEPTION_ORPHANED,
                        severity=ReasonSeverity.ERROR,
                        message=f"exception references unknown statement id: {target_id!r}",
                        object_id=ex.id,
                        json_path=_path(
                            "D_norm", "exceptions", ex_idx, "applies_to", target_idx
                        ),
                    )
                )
                continue

    return reasons, TraceItem(
        rule_id="dnorm/exceptions",
        because=[r.code for r in reasons],
        affected_ids=[e.id for e in ir.D_norm.exceptions],
        notes="Validates exception attachment and predicate shape.",
    )


def _compute_effective_norms(
    ir: AdeuIR, *, mode: KernelMode
) -> tuple[list[EffectiveNorm], list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []

    def_ids = {d.id for d in ir.O.definitions}
    doc_refs = _collect_doc_refs(ir)

    stmt_idx_by_id = {s.id: i for i, s in enumerate(ir.D_norm.statements)}
    attachments: dict[str, list[tuple[int, ExceptionClause]]] = {sid: [] for sid in stmt_idx_by_id}

    for ex_idx, ex in enumerate(ir.D_norm.exceptions):
        for target_id in ex.applies_to:
            if target_id in attachments:
                attachments[target_id].append((ex_idx, ex))

    applied_exception_ids: list[str] = []
    effective_norms: list[EffectiveNorm] = []

    uneval_severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
    precedence_severity = uneval_severity

    for stmt_idx, stmt in enumerate(ir.D_norm.statements):
        attached = attachments.get(stmt.id, [])

        applicable: list[tuple[int, ExceptionClause]] = []
        for ex_idx, ex in attached:
            if ex.condition.kind != "predicate":
                reasons.append(
                    CheckReason(
                        code=ReasonCode.EXCEPTION_CONDITION_UNEVALUATED,
                        severity=uneval_severity,
                        message=(
                            "exception.condition.kind is not IR-evaluatable "
                            "(requires predicate)"
                        ),
                        object_id=ex.id,
                        json_path=_path("D_norm", "exceptions", ex_idx, "condition", "kind"),
                    )
                )
                continue

            predicate_text = ex.condition.predicate
            if not (predicate_text and predicate_text.strip()):
                reasons.append(
                    CheckReason(
                        code=ReasonCode.EXCEPTION_CONDITION_UNEVALUATED,
                        severity=uneval_severity,
                        message="exception.condition.predicate is missing/blank",
                        object_id=ex.id,
                        json_path=_path("D_norm", "exceptions", ex_idx, "condition", "predicate"),
                    )
                )
                continue

            try:
                predicate = parse_predicate(predicate_text)
            except PredicateParseError:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.EXCEPTION_CONDITION_UNEVALUATED,
                        severity=uneval_severity,
                        message="exception.condition.predicate is not parseable",
                        object_id=ex.id,
                        json_path=_path("D_norm", "exceptions", ex_idx, "condition", "predicate"),
                    )
                )
                continue

            value = evaluate_predicate(predicate, def_ids=def_ids, doc_refs=doc_refs)
            if value is None:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.EXCEPTION_CONDITION_UNEVALUATED,
                        severity=uneval_severity,
                        message="exception.condition.predicate is not evaluatable from IR alone",
                        object_id=ex.id,
                        json_path=_path("D_norm", "exceptions", ex_idx, "condition", "predicate"),
                    )
                )
                continue

            if value is True:
                applicable.append((ex_idx, ex))

        applied: tuple[int, ExceptionClause] | None = None
        if len(applicable) == 1:
            applied = applicable[0]
        elif len(applicable) > 1:
            priorities = [
                (ex.priority if ex.priority is not None else 0) for _, ex in applicable
            ]
            has_strict_order = len(set(priorities)) == len(priorities)
            if not has_strict_order:
                reasons.append(
                    CheckReason(
                        code=ReasonCode.EXCEPTION_PRECEDENCE_UNDETERMINED,
                        severity=precedence_severity,
                        message=(
                            "multiple applicable exceptions; precedence requires strict priority "
                            "ordering"
                        ),
                        object_id=stmt.id,
                        json_path=_path("D_norm", "statements", stmt_idx),
                    )
                )
            else:
                applied = max(
                    applicable,
                    key=lambda item: (
                        item[1].priority if item[1].priority is not None else 0
                    ),
                )

        if applied is None:
            effective_norms.append(EffectiveNorm(statement=stmt, statement_idx=stmt_idx))
            continue

        ex_idx, ex = applied
        applied_exception_ids.append(ex.id)

        if ex.effect == "defeats":
            effective_norms.append(
                EffectiveNorm(statement=stmt, statement_idx=stmt_idx, defeated_by=(ex.id,))
            )
            continue

        if ex.effect == "narrows":
            effective_norms.append(
                EffectiveNorm(statement=stmt, statement_idx=stmt_idx, narrowed_by=(ex.id,))
            )
            continue

        if ex.effect == "clarifies":
            effective_norms.append(
                EffectiveNorm(statement=stmt, statement_idx=stmt_idx, clarified_by=(ex.id,))
            )
            continue

        effective_norms.append(EffectiveNorm(statement=stmt, statement_idx=stmt_idx))

    trace = TraceItem(
        rule_id="effective_norms",
        because=applied_exception_ids,
        affected_ids=[s.id for s in ir.D_norm.statements],
    )
    return effective_norms, reasons, trace


def _ref_key(ref: Ref) -> tuple:
    if ref.ref_type == "text":
        return ("text", ref.text)
    if ref.ref_type == "entity":
        return ("entity", ref.entity_id)
    if ref.ref_type == "def":
        return ("def", ref.def_id)
    if ref.ref_type == "doc":
        return ("doc", ref.doc_ref)
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


def _build_conflict_validator_request(
    ir: AdeuIR,
    effective_norms: list[EffectiveNorm],
    *,
    mode: KernelMode,
) -> tuple[ValidatorRequest | None, list[ConflictPair], list[CheckReason], list[str]]:
    reasons: list[CheckReason] = []
    active = [n for n in effective_norms if not n.is_defeated]
    candidates: list[ConflictPair] = []

    for i in range(len(active)):
        a_norm = active[i]
        a = a_norm.statement
        a_idx = a_norm.statement_idx
        for j in range(i + 1, len(active)):
            b_norm = active[j]
            b = b_norm.statement

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
                        json_path=_path("D_norm", "statements", a_idx, "scope", "time_about"),
                    )
                )
                continue

            if not _intervals_overlap(a_start, a_end, b_start, b_end):
                continue

            has_modifier = bool(
                a_norm.narrowed_by
                or a_norm.clarified_by
                or b_norm.narrowed_by
                or b_norm.clarified_by
            )
            if has_modifier:
                conflict_severity = (
                    ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
                )
                reasons.append(
                    CheckReason(
                        code=ReasonCode.CONFLICT_OVERLAPPING_SCOPE_UNRESOLVED,
                        severity=conflict_severity,
                        message=(
                            "Potential conflict, but one or more norms are modified by an "
                            "applicable exception."
                        ),
                        object_id=a.id,
                        json_path=_path("D_norm", "statements", a_idx),
                    )
                )
                continue

            pair_path = _path("D_norm", "statements", a_idx, "conflicts", b_norm.statement_idx)
            candidates.append(
                ConflictPair(
                    assertion_name=_assertion_name(object_id=a.id, json_path=pair_path),
                    object_id=a.id,
                    json_path=pair_path,
                    stmt_a_id=a.id,
                    stmt_a_idx=a_idx,
                    stmt_b_id=b.id,
                )
            )

    doc_refs = _collect_doc_refs(ir)
    def_ids = {d.id for d in ir.O.definitions}
    atom_values: dict[str, bool] = {}
    predicate_terms: list[tuple[str, str]] = []

    for stmt in ir.D_norm.statements:
        if stmt.condition is None:
            continue
        if stmt.condition.kind != "predicate":
            continue
        predicate_text = stmt.condition.predicate
        if not (predicate_text and predicate_text.strip()):
            continue
        try:
            predicate = parse_predicate(predicate_text)
        except PredicateParseError:
            continue
        expr = _predicate_to_smt(
            predicate,
            def_ids=def_ids,
            doc_refs=doc_refs,
            atom_values=atom_values,
        )
        predicate_terms.append((f"pred_stmt_{len(predicate_terms)}", expr))

    for ex in ir.D_norm.exceptions:
        if ex.condition.kind != "predicate":
            continue
        predicate_text = ex.condition.predicate
        if not (predicate_text and predicate_text.strip()):
            continue
        try:
            predicate = parse_predicate(predicate_text)
        except PredicateParseError:
            continue
        expr = _predicate_to_smt(
            predicate,
            def_ids=def_ids,
            doc_refs=doc_refs,
            atom_values=atom_values,
        )
        predicate_terms.append((f"pred_ex_{len(predicate_terms)}", expr))

    lines: list[str] = [
        "(set-logic QF_UF)",
        "(set-option :produce-models true)",
        "(set-option :produce-unsat-cores true)",
    ]

    for symbol, value in sorted(atom_values.items()):
        lines.append(f"(declare-fun {symbol} () Bool)")
        lines.append(f"(assert (= {symbol} {'true' if value else 'false'}))")

    for symbol, expr in predicate_terms:
        lines.append(f"(declare-fun {symbol} () Bool)")
        lines.append(f"(assert (= {symbol} {expr}))")

    atom_map: list[ValidatorAtomRef] = []
    origins: list[ValidatorOrigin] = []
    if candidates:
        collisions = _sorted_duplicate_values([pair.assertion_name for pair in candidates])
        if collisions:
            reasons.append(
                CheckReason(
                    code=ReasonCode.VALIDATOR_INVALID_REQUEST,
                    severity=ReasonSeverity.ERROR,
                    message=(
                        "assertion_name collision detected; collision_set="
                        + json.dumps(collisions, ensure_ascii=False, separators=(",", ":"))
                    ),
                    object_id=ir.ir_id,
                    json_path=_path("D_norm", "statements"),
                )
            )
            return None, candidates, reasons, [n.statement.id for n in active]
        for pair in candidates:
            atom_map.append(
                ValidatorAtomRef(
                    assertion_name=pair.assertion_name,
                    object_id=pair.object_id,
                    json_path=pair.json_path,
                )
            )
            origins.append(ValidatorOrigin(object_id=pair.object_id, json_path=pair.json_path))
            # Encode conflict candidates as named UNSAT witnesses (placeholder evidence).
            lines.append(f"(assert (! false :named {_smt_quote_symbol(pair.assertion_name)}))")
    else:
        # SAT when there are no conflict candidates.
        pass

    payload = ValidatorPayload(
        formula_smt2="\n".join(lines) + "\n",
        atom_map=atom_map,
        metadata={
            "rule_id": "dnorm_conflicts",
            "assertion_name_format": "a:<object_id>:<json_path_hash>",
        },
    )
    request = ValidatorRequest(kind="smt_check", logic="QF_UF", payload=payload, origin=origins)
    return request, candidates, reasons, [n.statement.id for n in active]


def _normalize_conflict_validator_result(
    *,
    request: ValidatorRequest,
    result: ValidatorResult,
) -> ValidatorResult:
    normalized = result.model_copy(deep=True)
    atom_map_by_name = {atom.assertion_name: atom for atom in request.payload.atom_map}

    if normalized.status == "UNSAT":
        canonical_unsat_core = sorted(normalized.evidence.unsat_core)
        normalized.evidence.unsat_core = canonical_unsat_core
        normalized.trace = [
            atom_map_by_name[name]
            for name in canonical_unsat_core
            if name in atom_map_by_name
        ]
        return normalized

    normalized.trace = sorted(normalized.trace, key=lambda item: item.assertion_name)
    return normalized


def _check_conflicts(
    ir: AdeuIR,
    effective_norms: list[EffectiveNorm],
    *,
    mode: KernelMode,
    validator_backend: ValidatorBackend | None = None,
) -> tuple[list[CheckReason], TraceItem, ValidatorRunRecord | None]:
    request, candidates, reasons, active_ids = _build_conflict_validator_request(
        ir,
        effective_norms,
        mode=mode,
    )
    if request is None:
        return reasons, TraceItem(
            rule_id="dnorm/conflicts",
            because=[r.code for r in reasons] + ["solver:INVALID_REQUEST"],
            affected_ids=active_ids,
            notes=(
                "Detects obligation vs prohibition conflicts in overlapping scope; "
                "request construction failed before backend execution."
            ),
        ), None

    backend = validator_backend
    if backend is None:
        try:
            backend = build_validator_backend("z3")
        except RuntimeError as exc:
            severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
            reasons.append(
                CheckReason(
                    code=ReasonCode.VALIDATOR_BACKEND_ERROR,
                    severity=severity,
                    message=str(exc),
                    object_id=ir.ir_id,
                    json_path=_path("D_norm", "statements"),
                )
            )
            return reasons, TraceItem(
                rule_id="dnorm/conflicts",
                because=[r.code for r in reasons],
                affected_ids=active_ids,
                notes="Detects obligation vs prohibition conflicts in overlapping scope.",
            ), None

    result = _normalize_conflict_validator_result(request=request, result=backend.run(request))
    run = ValidatorRunRecord(request=request, result=result)

    if result.status == "UNSAT" and candidates:
        # Fail-closed: conflicts are kernel-derived; UNSAT provides solver evidence + unsat core.
        for pair in candidates:
            reasons.append(
                CheckReason(
                    code=ReasonCode.CONFLICT_OBLIGATION_VS_PROHIBITION,
                    severity=ReasonSeverity.ERROR,
                    message=(
                        f"Conflict between {pair.stmt_a_id!r} and {pair.stmt_b_id!r} in "
                        f"overlapping scope (solver atom {pair.assertion_name})."
                    ),
                    object_id=pair.object_id,
                    json_path=_path("D_norm", "statements", pair.stmt_a_idx),
                )
            )
    elif result.status == "UNKNOWN":
        severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.VALIDATOR_UNKNOWN,
                severity=severity,
                message=result.evidence.error or "validator returned UNKNOWN",
                object_id=ir.ir_id,
                json_path=_path("D_norm", "statements"),
            )
        )
    elif result.status == "TIMEOUT":
        severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.VALIDATOR_TIMEOUT,
                severity=severity,
                message=result.evidence.error or "validator timed out",
                object_id=ir.ir_id,
                json_path=_path("D_norm", "statements"),
            )
        )
    elif result.status == "INVALID_REQUEST":
        reasons.append(
            CheckReason(
                code=ReasonCode.VALIDATOR_INVALID_REQUEST,
                severity=ReasonSeverity.ERROR,
                message=result.evidence.error or "validator request is invalid",
                object_id=ir.ir_id,
                json_path=_path("D_norm", "statements"),
            )
        )
    elif result.status == "ERROR":
        severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
        reasons.append(
            CheckReason(
                code=ReasonCode.VALIDATOR_BACKEND_ERROR,
                severity=severity,
                message=result.evidence.error or "validator backend error",
                object_id=ir.ir_id,
                json_path=_path("D_norm", "statements"),
            )
        )

    if not candidates:
        return reasons, TraceItem(
            rule_id="dnorm/conflicts",
            because=[r.code for r in reasons] + [f"solver:{result.status}"],
            affected_ids=active_ids,
            notes="Detects obligation vs prohibition conflicts in overlapping scope.",
        ), run

    summary_bits = [f"solver={result.backend}:{result.status}"]
    if result.evidence.unsat_core:
        summary_bits.append(f"unsat_core={','.join(result.evidence.unsat_core)}")
    summary_bits.append(f"formula_hash={result.formula_hash[:12]}")
    notes = "Detects obligation vs prohibition conflicts in overlapping scope; " + "; ".join(
        summary_bits
    )

    return reasons, TraceItem(
        rule_id="dnorm/conflicts",
        because=[r.code for r in reasons] + [f"solver:{result.status}"],
        affected_ids=active_ids,
        notes=notes,
    ), run


def _check_resolution(ir: AdeuIR) -> tuple[list[CheckReason], TraceItem]:
    reasons: list[CheckReason] = []

    entity_ids = {e.id for e in ir.O.entities}
    def_ids = {d.id for d in ir.O.definitions}

    def check_ref(ref: Ref, *, owner_id: str, json_path: str) -> None:
        if ref.ref_type == "entity" and ref.entity_id not in entity_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.DEF_ENTITY_UNRESOLVED,
                    severity=ReasonSeverity.WARN,
                    message=f"Unresolved EntityRef: {ref.entity_id!r}",
                    object_id=owner_id,
                    json_path=json_path,
                )
            )
        if ref.ref_type == "def" and ref.def_id not in def_ids:
            reasons.append(
                CheckReason(
                    code=ReasonCode.DEF_TERM_UNRESOLVED,
                    severity=ReasonSeverity.WARN,
                    message=f"Unresolved DefinitionRef: {ref.def_id!r}",
                    object_id=owner_id,
                    json_path=json_path,
                )
            )

    for idx, stmt in enumerate(ir.D_norm.statements):
        check_ref(
            stmt.subject,
            owner_id=stmt.id,
            json_path=_path("D_norm", "statements", idx, "subject"),
        )
        if stmt.action.object is not None:
            check_ref(
                stmt.action.object,
                owner_id=stmt.id,
                json_path=_path("D_norm", "statements", idx, "action", "object"),
            )

    return reasons, TraceItem(
        rule_id="refs/resolve",
        because=[r.code for r in reasons],
        affected_ids=[s.id for s in ir.D_norm.statements],
        notes="Flags unresolved EntityRef/DefinitionRef usages.",
    )


def check_with_validator_runs(
    raw: Any,
    *,
    mode: KernelMode = KernelMode.STRICT,
    validator_backend: ValidatorBackend | None = None,
) -> tuple[CheckReport, list[ValidatorRunRecord]]:
    if isinstance(raw, dict):
        schema_version = raw.get("schema_version")
        if schema_version is not None and schema_version != SUPPORTED_SCHEMA_VERSION:
            object_id = raw.get("ir_id") if isinstance(raw.get("ir_id"), str) else None
            return (
                CheckReport(
                    status="REFUSE",
                    reason_codes=[
                        CheckReason(
                            code=ReasonCode.UNSUPPORTED_SCHEMA_VERSION,
                            severity=ReasonSeverity.ERROR,
                            message=f"Unsupported schema_version: {schema_version!r}",
                            object_id=object_id,
                            json_path="/schema_version",
                        )
                    ],
                    trace=[TraceItem(rule_id="parse/schema_version")],
                    metrics=_zero_metrics(),
                ),
                [],
            )

    try:
        ir = AdeuIR.model_validate(raw)
    except ValidationError as e:
        errors = e.errors()
        code = ReasonCode.SCHEMA_INVALID
        chosen = errors[0] if errors else None
        object_id = None
        if isinstance(raw, dict) and isinstance(raw.get("ir_id"), str):
            object_id = raw["ir_id"]

        for err in errors:
            loc = err.get("loc", ())
            if "ambiguity" in loc:
                code = ReasonCode.AMBIGUITY_OPTION_INVALID
                chosen = err
                break

        json_path = None
        if chosen is not None:
            loc = chosen.get("loc", ())
            if isinstance(loc, (list, tuple)) and loc:
                json_path = "/" + "/".join(str(p) for p in loc)

        message = str(e)
        if chosen is not None and isinstance(chosen.get("msg"), str):
            message = chosen["msg"]

        return (
            CheckReport(
                status="REFUSE",
                reason_codes=[
                    CheckReason(
                        code=code,
                        severity=ReasonSeverity.ERROR,
                        message=message,
                        object_id=object_id,
                        json_path=json_path,
                    )
                ],
                trace=[TraceItem(rule_id="parse/validation_error")],
                metrics=_zero_metrics(),
            ),
            [],
        )

    metrics = _metrics(ir)
    reasons: list[CheckReason] = []
    trace: list[TraceItem] = [TraceItem(rule_id="parse/ok")]
    validator_runs: list[ValidatorRunRecord] = []

    if ir.context.source_features.modals:
        has_marker = any(a.issue in MODALITY_AMBIGUITY_ISSUES for a in ir.ambiguity)
        if not has_marker:
            severity = ReasonSeverity.ERROR if mode == KernelMode.STRICT else ReasonSeverity.WARN
            reasons.append(
                CheckReason(
                    code=ReasonCode.MODALITY_AMBIGUOUS_UNRESOLVED,
                    severity=severity,
                    message=(
                        "context.source_features.modals is non-empty but no ambiguity.issue "
                        "indicates modality ambiguity"
                    ),
                    object_id=ir.ir_id,
                    json_path="/context/source_features/modals",
                )
            )
        trace.append(
            TraceItem(
                rule_id="source_features/modality_ambiguity",
                because=[
                    r.code
                    for r in reasons
                    if r.code == ReasonCode.MODALITY_AMBIGUOUS_UNRESOLVED
                ],
                affected_ids=[ir.ir_id],
            )
        )

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

    effective_norms, effective_reasons, effective_trace = _compute_effective_norms(ir, mode=mode)
    reasons.extend(effective_reasons)
    trace.append(effective_trace)

    conflict_reasons, conflict_trace, conflict_run = _check_conflicts(
        ir,
        effective_norms,
        mode=mode,
        validator_backend=validator_backend,
    )
    reasons.extend(conflict_reasons)
    trace.append(conflict_trace)
    if conflict_run is not None:
        validator_runs.append(conflict_run)

    resolution_reasons, resolution_trace = _check_resolution(ir)
    reasons.extend(resolution_reasons)
    trace.append(resolution_trace)

    return _finalize_report(metrics=metrics, reasons=reasons, trace=trace), validator_runs


def check(
    raw: Any,
    *,
    mode: KernelMode = KernelMode.STRICT,
    validator_backend: ValidatorBackend | None = None,
) -> CheckReport:
    report, _ = check_with_validator_runs(raw, mode=mode, validator_backend=validator_backend)
    return report
