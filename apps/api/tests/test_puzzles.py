from __future__ import annotations

from adeu_api.main import PuzzleSolveRequest, solve_puzzle_endpoint
from adeu_puzzles import KnightsKnavesPuzzle


def _sat_puzzle() -> KnightsKnavesPuzzle:
    return KnightsKnavesPuzzle.model_validate(
        {
            "schema_version": "adeu.puzzle.v0",
            "puzzle_id": "api_puzzle_sat",
            "family": "knights_knaves",
            "people": [{"id": "a", "name": "A"}, {"id": "b", "name": "B"}],
            "statements": [
                {
                    "id": "stmt_a",
                    "speaker_id": "a",
                    "claim": {"op": "is_role", "person_id": "b", "role": "knave"},
                },
                {
                    "id": "stmt_b",
                    "speaker_id": "b",
                    "claim": {"op": "is_role", "person_id": "a", "role": "knave"},
                },
            ],
            "assumptions": [
                {
                    "id": "asm_1",
                    "claim": {"op": "is_role", "person_id": "a", "role": "knight"},
                }
            ],
        }
    )


def test_solve_puzzle_endpoint_z3_returns_assignments() -> None:
    resp = solve_puzzle_endpoint(PuzzleSolveRequest(puzzle=_sat_puzzle(), backend="z3"))
    assert resp.puzzle_id == "api_puzzle_sat"
    assert resp.validator_result.backend == "z3"
    assert resp.validator_result.status == "SAT"
    assignments = {item.person_id: item.role for item in resp.assignments}
    assert assignments == {"a": "knight", "b": "knave"}


def test_solve_puzzle_endpoint_mock_backend_returns_invalid_request() -> None:
    resp = solve_puzzle_endpoint(PuzzleSolveRequest(puzzle=_sat_puzzle(), backend="mock"))
    assert resp.validator_result.backend == "mock"
    assert resp.validator_result.status == "INVALID_REQUEST"
