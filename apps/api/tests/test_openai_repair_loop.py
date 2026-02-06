from __future__ import annotations

from datetime import datetime, timezone
from typing import Any

import adeu_api.openai_provider as openai_provider
from adeu_api.main import ProposeRequest, propose
from adeu_api.openai_backends import BackendMeta, BackendResult
from adeu_api.scoring import is_strict_improvement, score_key
from adeu_ir import CheckMetrics, CheckReason, CheckReport, Context, ReasonSeverity
from adeu_ir.reason_codes import ReasonCode
from adeu_kernel import KernelMode


def _context() -> Context:
    return Context(
        doc_id="doc:test:openai",
        jurisdiction="US-CA",
        time_eval=datetime(2026, 2, 6, tzinfo=timezone.utc),
    )


def _report_refuse(code: ReasonCode) -> CheckReport:
    return CheckReport(
        status="REFUSE",
        reason_codes=[
            CheckReason(
                code=code,
                severity=ReasonSeverity.ERROR,
                message=f"synthetic {code.value}",
            )
        ],
        trace=[],
        metrics=CheckMetrics(
            num_statements=0,
            num_exceptions=0,
            num_bridges=0,
            num_ambiguities=0,
        ),
    )


def _report_warn() -> CheckReport:
    return CheckReport(
        status="WARN",
        reason_codes=[
            CheckReason(
                code=ReasonCode.CONDITION_UNDISCHARGED,
                severity=ReasonSeverity.WARN,
                message="synthetic warning",
            )
        ],
        trace=[],
        metrics=CheckMetrics(
            num_statements=0,
            num_exceptions=0,
            num_bridges=0,
            num_ambiguities=0,
        ),
    )


def _report_pass() -> CheckReport:
    return CheckReport(
        status="PASS",
        reason_codes=[],
        trace=[],
        metrics=CheckMetrics(
            num_statements=0,
            num_exceptions=0,
            num_bridges=0,
            num_ambiguities=0,
        ),
    )


def _minimal_payload(*, ir_id: str, verb: str) -> dict[str, Any]:
    return {
        "schema_version": "adeu.ir.v0",
        "ir_id": ir_id,
        "context": {
            "doc_id": "doc:test:openai",
            "jurisdiction": "US-CA",
            "time_eval": "2026-02-06T00:00:00Z",
        },
        "D_norm": {
            "statements": [
                {
                    "id": f"dn_{verb}",
                    "kind": "obligation",
                    "subject": {"ref_type": "text", "text": "Supplier"},
                    "action": {"verb": verb},
                    "scope": {
                        "jurisdiction": "US-CA",
                        "time_about": {"kind": "unspecified"},
                    },
                    "provenance": {
                        "doc_ref": "doc:test:openai#sec1",
                        "span": {"start": 0, "end": 10},
                    },
                }
            ]
        },
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


def test_propose_openai_stops_when_repair_progress_stalls(monkeypatch) -> None:
    source_reports = [
        _report_refuse(ReasonCode.NORM_ACTION_MISSING),
        _report_refuse(ReasonCode.NORM_SCOPE_MISSING),
        _report_pass(),
    ]
    fake_backend = _FakeBackend(
        [
            _ok_result(_minimal_payload(ir_id="ir_attempt_1", verb="suspend")),
            _ok_result(_minimal_payload(ir_id="ir_attempt_2", verb="terminate")),
            _ok_result(_minimal_payload(ir_id="ir_attempt_3", verb="notify")),
        ]
    )
    checks = list(source_reports)

    def fake_check(*args: object, **kwargs: object) -> CheckReport:
        return checks.pop(0)

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(openai_provider, "build_openai_backend", lambda **kwargs: fake_backend)
    monkeypatch.setattr(openai_provider, "check", fake_check)

    proposals, log, _ = openai_provider.propose_openai(
        clause_text="Supplier may suspend service.",
        context=_context(),
        mode=KernelMode.LAX,
        max_candidates=1,
        max_repairs=5,
    )

    assert fake_backend.calls == 2
    assert len(log.attempts) == 2
    assert len(proposals) == 1, "expected exactly one candidate"

    expected_scores = [score_key(report) for report in source_reports[:2]]
    assert [attempt.score_key for attempt in log.attempts] == expected_scores

    accepted_baseline: tuple[int, int, int, int] | None = None
    for attempt in log.attempts:
        assert attempt.score_key is not None
        expected_accept = is_strict_improvement(attempt.score_key, accepted_baseline)
        assert attempt.accepted_by_gate is expected_accept
        if expected_accept:
            accepted_baseline = attempt.score_key


def test_propose_openai_assigns_candidate_rank_in_attempt_log(monkeypatch) -> None:
    fake_backend = _FakeBackend(
        [
            _ok_result(_minimal_payload(ir_id="ir_c0", verb="notify")),
            _ok_result(_minimal_payload(ir_id="ir_c1", verb="cure")),
        ]
    )
    checks = [_report_warn(), _report_pass()]

    def fake_check(*args: object, **kwargs: object) -> CheckReport:
        return checks.pop(0)

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(openai_provider, "build_openai_backend", lambda **kwargs: fake_backend)
    monkeypatch.setattr(openai_provider, "check", fake_check)

    resp = propose(
        ProposeRequest(
            clause_text="Supplier shall cure any breach.",
            provider="openai",
            mode=KernelMode.LAX,
            context=_context(),
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


def test_propose_openai_responses_backend_error_aborts_without_chat_fallback(
    monkeypatch,
) -> None:
    fake_backend = _FakeBackend(
        [
            BackendResult(
                provider_meta=BackendMeta(
                    api="responses",
                    model="gpt-5.2",
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt="{}",
                raw_text=None,
                error="OpenAI responses error: HTTP 500: upstream failure",
                prompt_hash="p",
                response_hash=None,
            )
        ]
    )

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(openai_provider, "build_openai_backend", lambda **kwargs: fake_backend)

    resp = propose(
        ProposeRequest(
            clause_text="Supplier shall deliver goods.",
            provider="openai",
            mode=KernelMode.LAX,
            context=_context(),
            max_candidates=2,
            max_repairs=2,
        )
    )

    assert fake_backend.calls == 1
    assert resp.provider.api == "responses"
    assert resp.candidates == []
    assert resp.proposer_log.attempts
    assert resp.proposer_log.attempts[0].status == "PARSE_ERROR"
    assert resp.proposer_log.attempts[0].accepted_by_gate is False
