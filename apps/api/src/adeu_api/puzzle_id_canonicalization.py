from __future__ import annotations

from typing import Any

from adeu_puzzles import KnightsKnavesPuzzle


def _rewrite_expr_person_ids(expr: dict[str, Any], person_map: dict[str, str]) -> None:
    op = expr.get("op")
    if op == "is_role":
        person_id = expr.get("person_id")
        if isinstance(person_id, str) and person_id in person_map:
            expr["person_id"] = person_map[person_id]
        return
    if op == "not":
        nested = expr.get("arg")
        if isinstance(nested, dict):
            _rewrite_expr_person_ids(nested, person_map)
        return
    args = expr.get("args")
    if isinstance(args, list):
        for nested in args:
            if isinstance(nested, dict):
                _rewrite_expr_person_ids(nested, person_map)


def canonicalize_puzzle_ids(puzzle: KnightsKnavesPuzzle) -> KnightsKnavesPuzzle:
    payload = puzzle.model_dump(mode="json", exclude_none=True)

    people = payload.get("people", [])
    person_map: dict[str, str] = {}
    for idx, person in enumerate(people):
        old_id = str(person.get("id", ""))
        new_id = f"p{idx + 1}"
        person["id"] = new_id
        if old_id:
            person_map[old_id] = new_id

    statements = payload.get("statements", [])
    for idx, statement in enumerate(statements):
        old_statement_id = str(statement.get("id", ""))
        statement["id"] = f"s{idx + 1}"
        speaker_id = statement.get("speaker_id")
        if isinstance(speaker_id, str):
            statement["speaker_id"] = person_map.get(speaker_id, speaker_id)
        claim = statement.get("claim")
        if isinstance(claim, dict):
            _rewrite_expr_person_ids(claim, person_map)
        if not old_statement_id:
            statement["id"] = f"s{idx + 1}"

    assumptions = payload.get("assumptions", [])
    for idx, assumption in enumerate(assumptions):
        assumption["id"] = f"a{idx + 1}"
        claim = assumption.get("claim")
        if isinstance(claim, dict):
            _rewrite_expr_person_ids(claim, person_map)

    return KnightsKnavesPuzzle.model_validate(payload)
