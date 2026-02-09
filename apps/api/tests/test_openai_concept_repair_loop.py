from __future__ import annotations

from typing import Any

import adeu_api.openai_concept_provider as openai_concept_provider
from adeu_api.main import ConceptProposeRequest, propose_concept
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


def _minimal_concept_payload(*, concept_id: str) -> dict[str, Any]:
    return {
        "schema_version": "adeu.concepts.v0",
        "concept_id": concept_id,
        "context": {"doc_id": "concept://test", "domain_tags": ["test"]},
        "terms": [{"id": "t1", "label": "bank"}],
        "senses": [{"id": "s1", "term_id": "t1", "gloss": "financial institution"}],
        "claims": [
            {
                "id": "c1",
                "sense_id": "s1",
                "text": "bank means financial institution",
                "provenance": {"doc_ref": "concept://test#s1", "span": {"start": 0, "end": 10}},
            }
        ],
        "links": [],
        "ambiguity": [],
        "bridges": [],
    }


class _FakeBackend:
    def __init__(self, results: list[BackendResult]):
        self._results = list(results)
        self.calls = 0
        self.temperatures: list[float | None] = []

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
        self.temperatures.append(temperature)
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


def test_propose_concept_openai_stops_after_non_improving_repeat(monkeypatch) -> None:
    reports = [
        _report_refuse(ReasonCode.CONCEPT_INCOHERENT_UNSAT),
        _report_warn(ReasonCode.CONCEPT_PROVENANCE_MISSING),
        _report_warn(ReasonCode.CONCEPT_PROVENANCE_MISSING),
    ]
    fake_backend = _FakeBackend(
        [
            _ok_result(_minimal_concept_payload(concept_id="cn_attempt_1")),
            _ok_result(_minimal_concept_payload(concept_id="cn_attempt_2")),
            _ok_result(_minimal_concept_payload(concept_id="cn_attempt_3")),
        ]
    )

    def fake_check(*args: object, **kwargs: object) -> tuple[CheckReport, list[Any]]:
        return reports.pop(0), []

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(
        openai_concept_provider, "build_openai_backend", lambda **kwargs: fake_backend
    )
    monkeypatch.setattr(openai_concept_provider, "concept_check_with_validator_runs", fake_check)

    proposals, log, _ = openai_concept_provider.propose_concept_openai(
        source_text="The term bank is ambiguous.",
        mode=KernelMode.LAX,
        max_candidates=1,
        max_repairs=4,
        source_features={},
    )

    assert fake_backend.calls == 3
    assert fake_backend.temperatures == [0.3, 0.3, 0.3]
    assert len(log.attempts) == 3
    assert len(proposals) == 1

    expected_scores = [
        _report_refuse(ReasonCode.CONCEPT_INCOHERENT_UNSAT),
        _report_warn(ReasonCode.CONCEPT_PROVENANCE_MISSING),
        _report_warn(ReasonCode.CONCEPT_PROVENANCE_MISSING),
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


def test_propose_concept_openai_assigns_candidate_ranks(monkeypatch) -> None:
    fake_backend = _FakeBackend(
        [
            _ok_result(_minimal_concept_payload(concept_id="cn_warn")),
            _ok_result(_minimal_concept_payload(concept_id="cn_pass")),
        ]
    )
    checks = [_report_warn(ReasonCode.CONCEPT_PROVENANCE_MISSING), _report_pass()]

    def fake_check(*args: object, **kwargs: object) -> tuple[CheckReport, list[Any]]:
        return checks.pop(0), []

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setattr(
        openai_concept_provider, "build_openai_backend", lambda **kwargs: fake_backend
    )
    monkeypatch.setattr(openai_concept_provider, "concept_check_with_validator_runs", fake_check)

    resp = propose_concept(
        ConceptProposeRequest(
            source_text="The term bank is ambiguous.",
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


def test_propose_concept_openai_uses_configured_temperature(monkeypatch) -> None:
    fake_backend = _FakeBackend([_ok_result(_minimal_concept_payload(concept_id="cn_temp"))])

    def fake_check(*args: object, **kwargs: object) -> tuple[CheckReport, list[Any]]:
        return _report_pass(), []

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setenv("ADEU_OPENAI_TEMPERATURE", "0.6")
    monkeypatch.setattr(
        openai_concept_provider, "build_openai_backend", lambda **kwargs: fake_backend
    )
    monkeypatch.setattr(openai_concept_provider, "concept_check_with_validator_runs", fake_check)

    proposals, _, _ = openai_concept_provider.propose_concept_openai(
        source_text="bank",
        mode=KernelMode.LAX,
        max_candidates=1,
        max_repairs=0,
        source_features={},
    )

    assert len(proposals) == 1
    assert fake_backend.temperatures == [0.6]


def test_propose_concept_openai_uses_configured_default_loop_limits(monkeypatch) -> None:
    fake_backend = _FakeBackend([_ok_result(_minimal_concept_payload(concept_id="cn_limits"))])

    def fake_check(*args: object, **kwargs: object) -> tuple[CheckReport, list[Any]]:
        return _report_pass(), []

    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.setenv("ADEU_OPENAI_API", "responses")
    monkeypatch.setenv("ADEU_OPENAI_DEFAULT_MAX_CANDIDATES", "1")
    monkeypatch.setenv("ADEU_OPENAI_DEFAULT_MAX_REPAIRS", "1")
    monkeypatch.setattr(
        openai_concept_provider, "build_openai_backend", lambda **kwargs: fake_backend
    )
    monkeypatch.setattr(openai_concept_provider, "concept_check_with_validator_runs", fake_check)

    _, log, _ = openai_concept_provider.propose_concept_openai(
        source_text="bank",
        mode=KernelMode.LAX,
        max_candidates=None,
        max_repairs=None,
        source_features={},
    )

    assert log.k == 1
    assert log.n == 1
