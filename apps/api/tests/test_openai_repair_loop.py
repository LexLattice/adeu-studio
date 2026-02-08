from __future__ import annotations

from datetime import datetime, timezone
from typing import Any

import adeu_api.openai_provider as openai_provider
from adeu_api.main import ProposeRequest, propose
from adeu_api.openai_backends import BackendMeta, BackendResult
from adeu_api.scoring import is_strict_improvement, score_key
from adeu_ir import CheckMetrics, CheckReason, CheckReport, Context, ReasonSeverity
from adeu_ir import (
    SolverEvidence,
    ValidatorAtomRef,
    ValidatorPayload,
    ValidatorRequest,
    ValidatorResult,
)
from adeu_ir.reason_codes import ReasonCode
from adeu_kernel import KernelMode, ValidatorRunRecord


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


def _run_record(
    *,
    request_hash: str,
    formula_hash: str,
    status: str,
    unsat_core: list[str],
    model: dict[str, str],
    atom_names: list[str],
) -> ValidatorRunRecord:
    return ValidatorRunRecord(
        request=ValidatorRequest(
            kind="smt_check",
            logic="QF_UF",
            payload=ValidatorPayload(
                formula_smt2="(assert true)",
                atom_map=[
                    ValidatorAtomRef(
                        assertion_name=atom_name,
                        object_id=f"obj_{idx}",
                        json_path=f"/path/{idx}",
                    )
                    for idx, atom_name in enumerate(atom_names)
                ],
            ),
            origin=[],
        ),
        result=ValidatorResult(
            status=status,
            assurance="solver_backed",
            backend="z3",
            timeout_ms=1000,
            options={},
            request_hash=request_hash,
            formula_hash=formula_hash,
            evidence=SolverEvidence(
                unsat_core=unsat_core,
                model=model,
            ),
            trace=[],
        ),
    )


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

    def fake_check_with_runs(*args: object, **kwargs: object) -> tuple[CheckReport, list]:
        return checks.pop(0), []

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(openai_provider, "build_openai_backend", lambda **kwargs: fake_backend)
    monkeypatch.setattr(openai_provider, "check_with_validator_runs", fake_check_with_runs)

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

    def fake_check_with_runs(*args: object, **kwargs: object) -> tuple[CheckReport, list]:
        return checks.pop(0), []

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(openai_provider, "build_openai_backend", lambda **kwargs: fake_backend)
    monkeypatch.setattr(openai_provider, "check_with_validator_runs", fake_check_with_runs)

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


def test_solver_evidence_summary_uses_latest_run_and_applies_caps(monkeypatch) -> None:
    monkeypatch.setattr(openai_provider, "MAX_SOLVER_SUMMARY_LINES", 500)

    old_run = _run_record(
        request_hash="req-old",
        formula_hash="f-old",
        status="UNSAT",
        unsat_core=["old_atom"],
        model={},
        atom_names=["old_atom"],
    )
    atom_names = [f"atom_{idx:02d}" for idx in range(55)]
    latest_run = _run_record(
        request_hash="req-latest",
        formula_hash="f-latest",
        status="SAT",
        unsat_core=atom_names,
        model={name: "True" for name in atom_names},
        atom_names=atom_names,
    )

    summary = openai_provider._solver_evidence_summary([old_run, latest_run])
    lines = summary.splitlines()

    assert "request_hash=req-latest" in summary
    assert "request_hash=req-old" not in summary
    assert "    ...+5 more" in summary
    assert len(lines) <= openai_provider.MAX_SOLVER_SUMMARY_LINES


def test_solver_evidence_summary_caps_total_lines(monkeypatch) -> None:
    monkeypatch.setattr(openai_provider, "MAX_SOLVER_SUMMARY_LINES", 10)
    atom_names = [f"atom_{idx:02d}" for idx in range(55)]
    run = _run_record(
        request_hash="req-overflow",
        formula_hash="f-overflow",
        status="SAT",
        unsat_core=atom_names,
        model={},
        atom_names=atom_names,
    )

    summary = openai_provider._solver_evidence_summary([run])
    lines = summary.splitlines()
    assert len(lines) == 11
    assert lines[-1].startswith("...+")


def test_failure_summary_includes_solver_section() -> None:
    run = _run_record(
        request_hash="req-1",
        formula_hash="f-1",
        status="UNSAT",
        unsat_core=["atom_a"],
        model={},
        atom_names=["atom_a"],
    )

    summary = openai_provider._failure_summary(_report_refuse(ReasonCode.NORM_ACTION_MISSING), [run])
    assert "Reasons:" in summary
    assert "Trace:" in summary
    assert "Solver Evidence:" in summary
    assert "request_hash=req-1" in summary
