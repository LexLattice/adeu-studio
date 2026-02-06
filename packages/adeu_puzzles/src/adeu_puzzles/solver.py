from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass

from adeu_ir import ValidatorAtomRef, ValidatorOrigin, ValidatorPayload, ValidatorRequest
from adeu_kernel import ValidatorBackend, build_validator_backend

from .models import (
    ExprAnd,
    ExprIsRole,
    ExprNot,
    ExprOr,
    KnightsKnavesPuzzle,
    PuzzleAssignment,
    PuzzleExpr,
    PuzzleSolveResult,
)


@dataclass(frozen=True)
class _Assertion:
    object_id: str
    json_path: str
    smt_expr: str


def _sanitize_symbol(value: str) -> str:
    cleaned = re.sub(r"[^a-zA-Z0-9_]+", "_", value).strip("_")
    if not cleaned:
        cleaned = "person"
    if cleaned[0].isdigit():
        cleaned = f"p_{cleaned}"
    return cleaned


def _person_symbol(*, person_id: str, index: int) -> str:
    return f"k_{_sanitize_symbol(person_id)}_{index}"


def _sanitize_smt_quoted_symbol_content(value: str) -> str:
    cleaned = (
        value.replace("\\", "_")
        .replace("|", "_")
        .replace("\n", "_")
        .replace("\r", "_")
        .replace("\t", "_")
    )
    return cleaned.strip() or "anon"


def _assertion_name(*, object_id: str, json_path: str) -> str:
    path_hash = hashlib.sha256(json_path.encode("utf-8")).hexdigest()[:12]
    safe_object_id = _sanitize_smt_quoted_symbol_content(object_id)
    return f"a:{safe_object_id}:{path_hash}"


def _smt_quote_symbol(value: str) -> str:
    return f"|{_sanitize_smt_quoted_symbol_content(value)}|"


def _expr_to_smt(expr: PuzzleExpr, *, symbol_by_person: dict[str, str]) -> str:
    if isinstance(expr, ExprIsRole):
        symbol = symbol_by_person[expr.person_id]
        if expr.role == "knight":
            return symbol
        return f"(not {symbol})"

    if isinstance(expr, ExprNot):
        return f"(not {_expr_to_smt(expr.arg, symbol_by_person=symbol_by_person)})"

    if isinstance(expr, ExprAnd):
        terms = [_expr_to_smt(item, symbol_by_person=symbol_by_person) for item in expr.args]
        return f"(and {' '.join(terms)})"

    if isinstance(expr, ExprOr):
        terms = [_expr_to_smt(item, symbol_by_person=symbol_by_person) for item in expr.args]
        return f"(or {' '.join(terms)})"

    raise TypeError(f"Unsupported puzzle expression type: {type(expr)!r}")


def build_knights_knaves_request(puzzle: KnightsKnavesPuzzle) -> ValidatorRequest:
    symbol_by_person: dict[str, str] = {}
    for idx, person in enumerate(puzzle.people):
        symbol_by_person[person.id] = _person_symbol(person_id=person.id, index=idx)

    assertions: list[_Assertion] = []
    for idx, statement in enumerate(puzzle.statements):
        claim_expr = _expr_to_smt(statement.claim, symbol_by_person=symbol_by_person)
        speaker_symbol = symbol_by_person[statement.speaker_id]
        assertions.append(
            _Assertion(
                object_id=statement.id,
                json_path=f"/statements/{idx}",
                smt_expr=f"(= {speaker_symbol} {claim_expr})",
            )
        )

    for idx, assumption in enumerate(puzzle.assumptions):
        assumption_expr = _expr_to_smt(assumption.claim, symbol_by_person=symbol_by_person)
        assertions.append(
            _Assertion(
                object_id=assumption.id,
                json_path=f"/assumptions/{idx}",
                smt_expr=assumption_expr,
            )
        )

    lines: list[str] = [
        "(set-logic QF_UF)",
        "(set-option :produce-models true)",
        "(set-option :produce-unsat-cores true)",
    ]
    for symbol in symbol_by_person.values():
        lines.append(f"(declare-fun {symbol} () Bool)")

    atom_map: list[ValidatorAtomRef] = []
    origin: list[ValidatorOrigin] = []
    if assertions:
        for assertion in assertions:
            assertion_name = _assertion_name(
                object_id=assertion.object_id,
                json_path=assertion.json_path,
            )
            lines.append(
                f"(assert (! {assertion.smt_expr} :named {_smt_quote_symbol(assertion_name)}))"
            )
            atom_map.append(
                ValidatorAtomRef(
                    assertion_name=assertion_name,
                    object_id=assertion.object_id,
                    json_path=assertion.json_path,
                )
            )
            origin.append(
                ValidatorOrigin(
                    object_id=assertion.object_id,
                    json_path=assertion.json_path,
                )
            )
    else:
        fallback_path = "/constraints/empty"
        fallback_name = _assertion_name(object_id=puzzle.puzzle_id, json_path=fallback_path)
        lines.append(f"(assert (! true :named {_smt_quote_symbol(fallback_name)}))")
        atom_map.append(
            ValidatorAtomRef(
                assertion_name=fallback_name,
                object_id=puzzle.puzzle_id,
                json_path=fallback_path,
            )
        )
        origin.append(ValidatorOrigin(object_id=puzzle.puzzle_id, json_path=fallback_path))

    payload = ValidatorPayload(
        formula_smt2="\n".join(lines) + "\n",
        atom_map=atom_map,
        metadata={
            "family": puzzle.family,
            "person_symbols": symbol_by_person,
            "assertion_name_format": "a:<object_id>:<json_path_hash>",
        },
    )
    return ValidatorRequest(
        kind="puzzle_solve",
        logic="QF_UF",
        payload=payload,
        origin=origin,
    )


def _assignment_role(raw_value: str | None) -> str:
    if raw_value is None:
        return "unknown"
    normalized = raw_value.strip().lower()
    if normalized == "true":
        return "knight"
    if normalized == "false":
        return "knave"
    return "unknown"


def solve_knights_knaves(
    puzzle: KnightsKnavesPuzzle,
    *,
    validator_backend: ValidatorBackend | None = None,
) -> PuzzleSolveResult:
    request = build_knights_knaves_request(puzzle)
    backend = validator_backend or build_validator_backend("z3")
    result = backend.run(request)

    symbol_by_person = request.payload.metadata.get("person_symbols", {})
    assignments: list[PuzzleAssignment] = []
    for person in puzzle.people:
        symbol = str(symbol_by_person.get(person.id, ""))
        raw_value = result.evidence.model.get(symbol) if symbol else None
        assignments.append(
            PuzzleAssignment(
                person_id=person.id,
                role=_assignment_role(raw_value),
                symbol=symbol,
            )
        )

    return PuzzleSolveResult(
        puzzle_id=puzzle.puzzle_id,
        validator_result=result,
        assignments=assignments,
    )
