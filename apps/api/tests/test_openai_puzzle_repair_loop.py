from __future__ import annotations

from typing import Any

import adeu_api.openai_puzzle_provider as openai_puzzle_provider
from adeu_api.main import PuzzleProposeRequest, propose_puzzle
from adeu_api.openai_backends import BackendMeta, BackendResult
from adeu_api.scoring import is_strict_improvement, score_key
from adeu_ir import CheckMetrics, CheckReason, CheckReport, ReasonSeverity
from adeu_ir.reason_codes import ReasonCode
from adeu_kernel import KernelMode


def _report_refuse(code: ReasonCode) -> CheckReport:
    return CheckReport(
        status="REFUSE",
        reason_codes=[
            CheckReason(code=code, severity=ReasonSeverity.ERROR, message=f"synthetic {code.value}")
        ],
        trace=[],
        metrics=CheckMetrics(num_statements=0, num_exceptions=0, num_bridges=0, num_ambiguities=0),
    )


def _report_warn(code: ReasonCode) -> CheckReport:
    return CheckReport(
        status="WARN",
        reason_codes=[
            CheckReason(code=code, severity=ReasonSeverity.WARN, message=f"synthetic {code.value}")
        ],
        trace=[],
        metrics=CheckMetrics(num_statements=0, num_exceptions=0, num_bridges=0, num_ambiguities=0),
    )


def _report_pass() -> CheckReport:
    return CheckReport(
        status="PASS",
        reason_codes=[],
        trace=[],
        metrics=CheckMetrics(num_statements=0, num_exceptions=0, num_bridges=0, num_ambiguities=0),
    )


def _minimal_puzzle_payload(*, puzzle_id: str) -> dict[str, Any]:
    return {
        "schema_version": "adeu.puzzle.v0",
        "puzzle_id": puzzle_id,
        "family": "knights_knaves",
        "people": [{"id": "a", "name": "A"}],
        "statements": [
            {
                "id": "stmt_1",
                "speaker_id": "a",
                "claim": {"op": "is_role", "person_id": "a", "role": "knight"},
            }
        ],
        "assumptions": [],
    }


class _FakeBackend:
    def __init__(self, results: list[BackendResult]):
        self._results = list(results)
        self.calls = 0

    def generate_ir_json(
        self,
        *,
        system_prompt: str,
        user_prompt: str,
        json_schema: dict[str, Any],
        model: str,
        temperature: float | None,
        extra: dict[str, Any] | None = None,
    ) -> BackendResult:
        self.calls += 1
        return self._results.pop(0)


def _ok_result(payload: dict[str, Any]) -> BackendResult:
    return BackendResult(
        provider_meta=BackendMeta(api="responses", model="gpt-5.2", response_mode="json_schema"),
        parsed_json=payload,
        raw_prompt="{}",
        raw_text="{}",
        error=None,
        prompt_hash="p",
        response_hash="r",
    )


def test_propose_puzzle_openai_stops_after_non_improving_repeat(monkeypatch) -> None:
    reports = [
        _report_refuse(ReasonCode.PUZZLE_UNSAT),
        _report_warn(ReasonCode.PUZZLE_PROVENANCE_MISSING),
        _report_warn(ReasonCode.PUZZLE_PROVENANCE_MISSING),
    ]
    fake_backend = _FakeBackend(
        [
            _ok_result(_minimal_puzzle_payload(puzzle_id="pz_attempt_1")),
            _ok_result(_minimal_puzzle_payload(puzzle_id="pz_attempt_2")),
            _ok_result(_minimal_puzzle_payload(puzzle_id="pz_attempt_3")),
        ]
    )

    def fake_check(*args: object, **kwargs: object) -> tuple[CheckReport, list[Any]]:
        return reports.pop(0), []

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(
        openai_puzzle_provider, "build_openai_backend", lambda **kwargs: fake_backend
    )
    monkeypatch.setattr(openai_puzzle_provider, "puzzle_check_with_validator_runs", fake_check)

    proposals, log, _ = openai_puzzle_provider.propose_puzzle_openai(
        puzzle_text="A says: I am a knight.",
        mode=KernelMode.LAX,
        max_candidates=1,
        max_repairs=4,
        source_features={},
        context_override=None,
    )

    assert fake_backend.calls == 3
    assert len(log.attempts) == 3
    assert len(proposals) == 1

    expected_scores = [
        _report_refuse(ReasonCode.PUZZLE_UNSAT),
        _report_warn(ReasonCode.PUZZLE_PROVENANCE_MISSING),
        _report_warn(ReasonCode.PUZZLE_PROVENANCE_MISSING),
    ]
    expected_keys = [score_key(report) for report in expected_scores]
    assert [attempt.score_key for attempt in log.attempts] == expected_keys

    accepted_baseline: tuple[int, int, int, int] | None = None
    for attempt in log.attempts:
        assert attempt.score_key is not None
        expected_accept = is_strict_improvement(attempt.score_key, accepted_baseline)
        assert attempt.accepted_by_gate is expected_accept
        if expected_accept:
            accepted_baseline = attempt.score_key


def test_propose_puzzle_openai_assigns_candidate_ranks(monkeypatch) -> None:
    fake_backend = _FakeBackend(
        [
            _ok_result(_minimal_puzzle_payload(puzzle_id="pz_warn")),
            _ok_result(_minimal_puzzle_payload(puzzle_id="pz_pass")),
        ]
    )
    checks = [_report_warn(ReasonCode.PUZZLE_PROVENANCE_MISSING), _report_pass()]

    def fake_check(*args: object, **kwargs: object) -> tuple[CheckReport, list[Any]]:
        return checks.pop(0), []

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(
        openai_puzzle_provider, "build_openai_backend", lambda **kwargs: fake_backend
    )
    monkeypatch.setattr(openai_puzzle_provider, "puzzle_check_with_validator_runs", fake_check)

    resp = propose_puzzle(
        PuzzleProposeRequest(
            puzzle_text="A says: B is a knave.",
            provider="openai",
            mode=KernelMode.LAX,
            max_candidates=2,
            max_repairs=0,
        )
    )

    assert resp.provider.kind == "openai"
    assert resp.provider.api == "responses"
    assert [candidate.check_report.status for candidate in resp.candidates] == ["PASS", "WARN"]
    assert [candidate.rank for candidate in resp.candidates] == [0, 1]
    assert [attempt.candidate_rank for attempt in resp.proposer_log.attempts] == [1, 0]
    assert all(attempt.score_key is not None for attempt in resp.proposer_log.attempts)
