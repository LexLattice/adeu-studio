from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any

from adeu_api.openai_backends import BackendMeta, BackendResult
from adeu_api.openai_proposer_core import (
    CoreAttemptLog,
    ProposerAdapter,
    run_openai_repair_loop,
)
from adeu_ir import CheckMetrics, CheckReason, CheckReport, ReasonSeverity
from adeu_ir.reason_codes import ReasonCode
from adeu_kernel import KernelMode


@dataclass(frozen=True)
class _FakeIR:
    candidate_id: str
    level: str


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


def _report(status: str) -> CheckReport:
    if status == "PASS":
        reasons: list[CheckReason] = []
    elif status == "WARN":
        reasons = [
            CheckReason(
                code=ReasonCode.CONDITION_UNDISCHARGED,
                severity=ReasonSeverity.WARN,
                message="warn",
            )
        ]
    else:
        reasons = [
            CheckReason(
                code=ReasonCode.SCHEMA_INVALID,
                severity=ReasonSeverity.ERROR,
                message="error",
            )
        ]
    return CheckReport(
        status=status,
        reason_codes=reasons,
        trace=[],
        metrics=CheckMetrics(
            num_statements=0,
            num_exceptions=0,
            num_bridges=0,
            num_ambiguities=0,
        ),
    )


def _ok(payload: dict[str, Any]) -> BackendResult:
    return BackendResult(
        provider_meta=BackendMeta(api="responses", model="gpt-5.2", response_mode="json_schema"),
        parsed_json=payload,
        raw_prompt="{}",
        raw_text="{}",
        error=None,
        prompt_hash="p",
        response_hash="r",
    )


class _Adapter(ProposerAdapter[_FakeIR, None]):
    domain = "fake"

    def build_initial_prompt(self, *, candidate_idx: int) -> tuple[str, str]:
        return "system", f"initial:{candidate_idx}"

    def build_repair_prompt(
        self,
        *,
        best_candidate: _FakeIR | None,
        last_attempt: CoreAttemptLog | None,
        failure_summary: str,
    ) -> tuple[str, str]:
        return "system", "repair"

    def parse_ir(self, raw_json: str) -> tuple[_FakeIR | None, str | None]:
        try:
            payload = json.loads(raw_json)
        except json.JSONDecodeError as exc:
            return None, str(exc)
        if not isinstance(payload, dict):
            return None, "not an object"
        candidate_id = payload.get("candidate_id")
        level = payload.get("level")
        if not isinstance(candidate_id, str) or not isinstance(level, str):
            return None, "schema invalid"
        return _FakeIR(candidate_id=candidate_id, level=level), None

    def canonicalize(self, ir: _FakeIR) -> _FakeIR:
        return ir

    def check_with_runs(self, ir: _FakeIR, mode: KernelMode) -> tuple[CheckReport, None]:
        if ir.level == "pass":
            return _report("PASS"), None
        if ir.level == "warn":
            return _report("WARN"), None
        return _report("REFUSE"), None

    def candidate_id(self, ir: _FakeIR) -> str:
        return ir.candidate_id

    def classify_backend_error(self, error_text: str) -> list[str]:
        return ["BACKEND_ERROR"]

    def classify_parse_error(self, parse_error_text: str) -> list[str]:
        return ["SCHEMA_INVALID"]

    def build_failure_summary(self, report: CheckReport, aux: None) -> str:
        return report.status


def test_run_openai_repair_loop_uses_strict_improvement_gate() -> None:
    adapter = _Adapter()
    backend = _FakeBackend(
        [
            _ok({"candidate_id": "c0", "level": "refuse"}),
            _ok({"candidate_id": "c1", "level": "warn"}),
            _ok({"candidate_id": "c2", "level": "warn"}),
        ]
    )

    candidates, log = run_openai_repair_loop(
        adapter=adapter,
        backend=backend,
        schema={},
        api="responses",
        model="gpt-5.2",
        mode=KernelMode.LAX,
        max_candidates=1,
        max_repairs=5,
        want_raw=False,
    )

    assert backend.calls == 3
    assert len(log.attempts) == 3
    assert [attempt.accepted_by_gate for attempt in log.attempts] == [True, True, False]
    assert candidates
    assert candidates[0].ir.candidate_id == "c1"
    assert candidates[0].report.status == "WARN"


def test_run_openai_repair_loop_aborts_on_responses_backend_error() -> None:
    adapter = _Adapter()
    backend = _FakeBackend(
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

    candidates, log = run_openai_repair_loop(
        adapter=adapter,
        backend=backend,
        schema={},
        api="responses",
        model="gpt-5.2",
        mode=KernelMode.LAX,
        max_candidates=3,
        max_repairs=3,
        want_raw=False,
    )

    assert backend.calls == 1
    assert candidates == []
    assert len(log.attempts) == 1
    assert log.attempts[0].status == "PARSE_ERROR"
    assert log.attempts[0].accepted_by_gate is False
