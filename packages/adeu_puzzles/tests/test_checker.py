from __future__ import annotations

from dataclasses import dataclass

from adeu_ir import SolverEvidence, ValidatorRequest, ValidatorResult
from adeu_kernel import KernelMode
from adeu_puzzles import check, check_with_validator_runs


def _sat_puzzle(*, include_text: bool) -> dict:
    return {
        "schema_version": "adeu.puzzle.v0",
        "puzzle_id": "puzzle_sat_checker",
        "family": "knights_knaves",
        "people": [
            {"id": "a", "name": "A"},
            {"id": "b", "name": "B"},
        ],
        "statements": [
            {
                "id": "stmt_a",
                "speaker_id": "a",
                "text": "B is a knave." if include_text else None,
                "claim": {"op": "is_role", "person_id": "b", "role": "knave"},
            },
            {
                "id": "stmt_b",
                "speaker_id": "b",
                "text": "A is a knave." if include_text else None,
                "claim": {"op": "is_role", "person_id": "a", "role": "knave"},
            },
        ],
        "assumptions": [
            {
                "id": "asm_1",
                "text": "A is a knight." if include_text else None,
                "claim": {"op": "is_role", "person_id": "a", "role": "knight"},
            }
        ],
    }


def _unsat_puzzle() -> dict:
    return {
        "schema_version": "adeu.puzzle.v0",
        "puzzle_id": "puzzle_unsat_checker",
        "family": "knights_knaves",
        "people": [{"id": "a", "name": "A"}],
        "statements": [
            {
                "id": "stmt_self",
                "speaker_id": "a",
                "text": None,
                "claim": {"op": "is_role", "person_id": "a", "role": "knave"},
            }
        ],
    }


@dataclass(frozen=True)
class _TimeoutBackend:
    def run(self, request: ValidatorRequest) -> ValidatorResult:
        return ValidatorResult(
            status="TIMEOUT",
            assurance="solver_backed",
            backend="mock",
            backend_version="0",
            timeout_ms=3000,
            options={},
            request_hash="r",
            formula_hash="f",
            evidence=SolverEvidence(error="forced timeout"),
            trace=[],
        )


def test_check_sat_passes_without_text_provenance_requirement() -> None:
    report, runs = check_with_validator_runs(_sat_puzzle(include_text=False), mode=KernelMode.LAX)
    assert report.status == "PASS"
    assert runs
    assert runs[0].result.status == "SAT"


def test_check_warns_when_text_has_no_provenance() -> None:
    report = check(_sat_puzzle(include_text=True), mode=KernelMode.LAX)
    assert report.status == "WARN"
    reasons = [r for r in report.reason_codes if r.code == "PUZZLE_PROVENANCE_MISSING"]
    assert reasons
    assert all(r.severity == "WARN" for r in reasons)


def test_check_unsat_maps_to_strict_refuse_and_lax_warn() -> None:
    strict_report = check(_unsat_puzzle(), mode=KernelMode.STRICT)
    lax_report = check(_unsat_puzzle(), mode=KernelMode.LAX)
    assert strict_report.status == "REFUSE"
    assert lax_report.status == "WARN"
    strict_reason = [r for r in strict_report.reason_codes if r.code == "PUZZLE_UNSAT"][0]
    lax_reason = [r for r in lax_report.reason_codes if r.code == "PUZZLE_UNSAT"][0]
    assert strict_reason.severity == "ERROR"
    assert lax_reason.severity == "WARN"


def test_check_schema_invalid_uses_puzzle_reason_code() -> None:
    raw = _sat_puzzle(include_text=False)
    raw["schema_version"] = "adeu.puzzle.vX"
    report = check(raw, mode=KernelMode.STRICT)
    assert report.status == "REFUSE"
    assert report.reason_codes[0].code == "PUZZLE_SCHEMA_INVALID"


def test_check_timeout_mapping_matches_mode_policy() -> None:
    strict_report = check(
        _sat_puzzle(include_text=False),
        mode=KernelMode.STRICT,
        validator_backend=_TimeoutBackend(),
    )
    lax_report = check(
        _sat_puzzle(include_text=False),
        mode=KernelMode.LAX,
        validator_backend=_TimeoutBackend(),
    )
    strict_reason = [r for r in strict_report.reason_codes if r.code == "PUZZLE_SOLVER_TIMEOUT"][0]
    lax_reason = [r for r in lax_report.reason_codes if r.code == "PUZZLE_SOLVER_TIMEOUT"][0]
    assert strict_reason.severity == "ERROR"
    assert lax_reason.severity == "WARN"
