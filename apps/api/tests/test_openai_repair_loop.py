from __future__ import annotations

import json
from datetime import datetime, timezone

import adeu_api.openai_provider as openai_provider
from adeu_api.main import ProposeRequest, propose
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


def _minimal_payload(*, ir_id: str, verb: str) -> str:
    payload = {
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
    return json.dumps(payload)


def test_propose_openai_stops_when_repair_progress_stalls(monkeypatch) -> None:
    calls = 0
    responses = [
        _minimal_payload(ir_id="ir_attempt_1", verb="suspend"),
        _minimal_payload(ir_id="ir_attempt_2", verb="terminate"),
        _minimal_payload(ir_id="ir_attempt_3", verb="notify"),
    ]
    checks = [
        _report_refuse(ReasonCode.NORM_ACTION_MISSING),
        _report_refuse(ReasonCode.NORM_SCOPE_MISSING),
        _report_pass(),
    ]

    def fake_chat_completion_json(*, model: str, messages: list[dict[str, str]]) -> tuple[str, str]:
        nonlocal calls
        calls += 1
        return "{}", responses.pop(0)

    def fake_check(*args: object, **kwargs: object) -> CheckReport:
        return checks.pop(0)

    monkeypatch.setattr(openai_provider, "_chat_completion_json", fake_chat_completion_json)
    monkeypatch.setattr(openai_provider, "check", fake_check)

    proposals, log, _ = openai_provider.propose_openai(
        clause_text="Supplier may suspend service.",
        context=_context(),
        mode=KernelMode.LAX,
        max_candidates=1,
        max_repairs=5,
    )

    assert calls == 2
    assert len(log.attempts) == 2
    assert proposals, "expected at least one candidate"


def test_propose_openai_assigns_candidate_rank_in_attempt_log(monkeypatch) -> None:
    responses = [
        _minimal_payload(ir_id="ir_c0", verb="notify"),
        _minimal_payload(ir_id="ir_c1", verb="cure"),
    ]
    checks = [_report_warn(), _report_pass()]

    def fake_chat_completion_json(*, model: str, messages: list[dict[str, str]]) -> tuple[str, str]:
        return "{}", responses.pop(0)

    def fake_check(*args: object, **kwargs: object) -> CheckReport:
        return checks.pop(0)

    monkeypatch.setattr(openai_provider, "_chat_completion_json", fake_chat_completion_json)
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

    assert [candidate.check_report.status for candidate in resp.candidates] == ["PASS", "WARN"]
    assert [candidate.rank for candidate in resp.candidates] == [0, 1]
    assert [attempt.candidate_rank for attempt in resp.proposer_log.attempts] == [1, 0]
