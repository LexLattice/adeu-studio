from __future__ import annotations

from adeu_api.main import (
    PuzzleCheckRequest,
    PuzzleSolveRequest,
    check_puzzle_variant,
    solve_puzzle_endpoint,
)
from adeu_kernel import KernelMode
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


def _unsat_puzzle() -> KnightsKnavesPuzzle:
    return KnightsKnavesPuzzle.model_validate(
        {
            "schema_version": "adeu.puzzle.v0",
            "puzzle_id": "api_puzzle_unsat",
            "family": "knights_knaves",
            "people": [{"id": "a", "name": "A"}],
            "statements": [
                {
                    "id": "stmt_self",
                    "speaker_id": "a",
                    "claim": {"op": "is_role", "person_id": "a", "role": "knave"},
                }
            ],
            "assumptions": [],
        }
    )


def test_check_puzzle_endpoint_strict_unsat_refuses() -> None:
    report = check_puzzle_variant(
        PuzzleCheckRequest(puzzle=_unsat_puzzle(), mode=KernelMode.STRICT)
    )
    assert report.status == "REFUSE"
    assert any(reason.code == "PUZZLE_UNSAT" for reason in report.reason_codes)


def test_check_puzzle_endpoint_lax_unsat_warns() -> None:
    report = check_puzzle_variant(PuzzleCheckRequest(puzzle=_unsat_puzzle(), mode=KernelMode.LAX))
    assert report.status == "WARN"
    assert any(reason.code == "PUZZLE_UNSAT" for reason in report.reason_codes)


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
