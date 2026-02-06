from __future__ import annotations

import pytest
from adeu_puzzles import KnightsKnavesPuzzle, build_knights_knaves_request, solve_knights_knaves


def _sat_puzzle() -> KnightsKnavesPuzzle:
    return KnightsKnavesPuzzle.model_validate(
        {
            "schema_version": "adeu.puzzle.v0",
            "puzzle_id": "puzzle_sat",
            "family": "knights_knaves",
            "people": [
                {"id": "a", "name": "A"},
                {"id": "b", "name": "B"},
            ],
            "statements": [
                {
                    "id": "stmt_a",
                    "speaker_id": "a",
                    "text": "B is a knave.",
                    "claim": {"op": "is_role", "person_id": "b", "role": "knave"},
                },
                {
                    "id": "stmt_b",
                    "speaker_id": "b",
                    "text": "A is a knave.",
                    "claim": {"op": "is_role", "person_id": "a", "role": "knave"},
                },
            ],
            "assumptions": [
                {
                    "id": "asm_1",
                    "text": "A is a knight.",
                    "claim": {"op": "is_role", "person_id": "a", "role": "knight"},
                }
            ],
        }
    )


def _unsat_puzzle() -> KnightsKnavesPuzzle:
    return KnightsKnavesPuzzle.model_validate(
        {
            "schema_version": "adeu.puzzle.v0",
            "puzzle_id": "puzzle_unsat",
            "family": "knights_knaves",
            "people": [{"id": "a", "name": "A"}],
            "statements": [
                {
                    "id": "stmt_self",
                    "speaker_id": "a",
                    "text": "I am a knave.",
                    "claim": {"op": "is_role", "person_id": "a", "role": "knave"},
                }
            ],
        }
    )


def test_build_knights_knaves_request_is_deterministic() -> None:
    request = build_knights_knaves_request(_sat_puzzle())
    assert request.kind == "puzzle_solve"
    assert request.logic == "QF_UF"
    assert request.payload.metadata["family"] == "knights_knaves"
    assert "person_symbols" in request.payload.metadata
    assert request.payload.atom_map
    first_atom = request.payload.atom_map[0]
    assert first_atom.assertion_name.startswith("a:")


def test_solve_knights_knaves_sat_returns_assignments() -> None:
    result = solve_knights_knaves(_sat_puzzle())
    assert result.validator_result.status == "SAT"
    assignments = {item.person_id: item.role for item in result.assignments}
    assert assignments == {"a": "knight", "b": "knave"}


def test_solve_knights_knaves_unsat_returns_unsat_core() -> None:
    result = solve_knights_knaves(_unsat_puzzle())
    assert result.validator_result.status == "UNSAT"
    assert result.validator_result.evidence.unsat_core


def test_solver_sanitizes_assertion_names_for_quoted_symbols() -> None:
    puzzle = KnightsKnavesPuzzle.model_validate(
        {
            "schema_version": "adeu.puzzle.v0",
            "puzzle_id": "puzzle_pipe_id",
            "family": "knights_knaves",
            "people": [{"id": "a", "name": "A"}],
            "statements": [
                {
                    "id": "stmt|bad\\id",
                    "speaker_id": "a",
                    "claim": {"op": "is_role", "person_id": "a", "role": "knight"},
                }
            ],
        }
    )

    request = build_knights_knaves_request(puzzle)
    assertion_name = request.payload.atom_map[0].assertion_name
    assert "|" not in assertion_name
    assert "\\" not in assertion_name
    assert f":named |{assertion_name}|" in request.payload.formula_smt2

    result = solve_knights_knaves(puzzle)
    assert result.validator_result.status == "SAT"


def test_knights_knaves_model_rejects_unknown_person_references() -> None:
    with pytest.raises(ValueError, match="unknown person_id"):
        KnightsKnavesPuzzle.model_validate(
            {
                "schema_version": "adeu.puzzle.v0",
                "puzzle_id": "bad_ref",
                "family": "knights_knaves",
                "people": [{"id": "a", "name": "A"}],
                "statements": [
                    {
                        "id": "stmt_bad",
                        "speaker_id": "a",
                        "claim": {"op": "is_role", "person_id": "missing", "role": "knight"},
                    }
                ],
            }
        )
