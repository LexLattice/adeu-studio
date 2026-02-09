from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Any, Generic, Protocol, TypeVar

from adeu_ir import CheckReport
from adeu_kernel import KernelMode

from .hashing import sha256_text
from .openai_backends import BackendApi, OpenAIBackend
from .scoring import ScoreKey, is_strict_improvement, score_key

IRT = TypeVar("IRT")
AuxT = TypeVar("AuxT")


@dataclass(frozen=True)
class CoreAttemptLog:
    attempt_idx: int
    status: str
    reason_codes_summary: list[str]
    score_key: ScoreKey | None
    accepted_by_gate: bool
    candidate_id: str | None = None
    domain_extras: dict[str, object] | None = None


@dataclass(frozen=True)
class CoreProposerLog:
    provider: str
    api: BackendApi
    model: str
    created_at: str
    k: int
    n: int
    attempts: list[CoreAttemptLog]
    prompt_hash: str | None = None
    response_hash: str | None = None
    raw_prompt: str | None = None
    raw_response: str | None = None


@dataclass(frozen=True)
class CoreCandidate(Generic[IRT, AuxT]):
    ir: IRT
    report: CheckReport
    aux: AuxT


class ProposerAdapter(Protocol[IRT, AuxT]):
    domain: str

    def build_initial_prompt(self, *, candidate_idx: int) -> tuple[str, str]: ...

    def build_repair_prompt(
        self,
        *,
        best_candidate: IRT | None,
        last_attempt: CoreAttemptLog | None,
        failure_summary: str,
    ) -> tuple[str, str]: ...

    def parse_ir(self, payload: dict[str, Any]) -> tuple[IRT | None, str | None]: ...

    def canonicalize(self, ir: IRT) -> IRT: ...

    def check_with_runs(self, ir: IRT, mode: KernelMode) -> tuple[CheckReport, AuxT]: ...

    def candidate_id(self, ir: IRT) -> str: ...

    def classify_backend_error(self, error_text: str) -> list[str]: ...

    def classify_parse_error(self, parse_error_text: str) -> list[str]: ...

    def build_failure_summary(self, report: CheckReport, aux: AuxT) -> str: ...


def _combine_hashes(hashes: list[str]) -> str | None:
    if not hashes:
        return None
    return sha256_text("|".join(hashes))


def run_openai_repair_loop(
    *,
    adapter: ProposerAdapter[IRT, AuxT],
    backend: OpenAIBackend,
    schema: dict[str, object],
    api: BackendApi,
    model: str,
    mode: KernelMode,
    max_candidates: int,
    max_repairs: int,
    temperature: float | None = 0.3,
    want_raw: bool = False,
) -> tuple[list[CoreCandidate[IRT, AuxT]], CoreProposerLog]:
    created_at = datetime.now(tz=timezone.utc).isoformat()
    attempt_logs: list[CoreAttemptLog] = []
    raw_prompt_log: list[str] = []
    raw_response_log: list[str] = []
    prompt_hashes: list[str] = []
    response_hashes: list[str] = []

    accepted_candidates: list[CoreCandidate[IRT, AuxT]] = []
    attempt_idx = 0
    abort_remaining_candidates = False

    for candidate_idx in range(max_candidates):
        accepted_ir: IRT | None = None
        accepted_report: CheckReport | None = None
        accepted_aux: AuxT | None = None
        accepted_score: ScoreKey | None = None
        previous_ir: IRT | None = None
        last_attempt: CoreAttemptLog | None = None
        failure_summary = ""

        for repair_idx in range(max_repairs + 1):
            if repair_idx == 0:
                system_prompt, user_prompt = adapter.build_initial_prompt(
                    candidate_idx=candidate_idx,
                )
            else:
                system_prompt, user_prompt = adapter.build_repair_prompt(
                    best_candidate=previous_ir,
                    last_attempt=last_attempt,
                    failure_summary=failure_summary,
                )

            backend_result = backend.generate_ir_json(
                system_prompt=system_prompt,
                user_prompt=user_prompt,
                json_schema=schema,
                model=model,
                temperature=temperature,
                extra=None,
            )

            if backend_result.prompt_hash:
                prompt_hashes.append(backend_result.prompt_hash)
            if backend_result.response_hash:
                response_hashes.append(backend_result.response_hash)
            if want_raw:
                if backend_result.raw_prompt:
                    raw_prompt_log.append(backend_result.raw_prompt)
                if backend_result.raw_text:
                    raw_response_log.append(backend_result.raw_text)

            if backend_result.error is not None or backend_result.parsed_json is None:
                error_text = backend_result.error or "backend returned no parsed JSON"
                attempt = CoreAttemptLog(
                    attempt_idx=attempt_idx,
                    status="PARSE_ERROR",
                    reason_codes_summary=adapter.classify_backend_error(error_text),
                    score_key=None,
                    accepted_by_gate=False,
                    candidate_id=None,
                )
                attempt_logs.append(attempt)
                last_attempt = attempt
                attempt_idx += 1
                failure_summary = error_text
                previous_ir = None

                if accepted_score is not None:
                    break
                if api == "responses" and "error" in error_text.lower():
                    abort_remaining_candidates = True
                    break
                continue

            parsed_ir, parse_error = adapter.parse_ir(backend_result.parsed_json)
            if parsed_ir is None or parse_error is not None:
                error_text = parse_error or "domain parse returned no IR"
                attempt = CoreAttemptLog(
                    attempt_idx=attempt_idx,
                    status="PARSE_ERROR",
                    reason_codes_summary=adapter.classify_parse_error(error_text),
                    score_key=None,
                    accepted_by_gate=False,
                    candidate_id=None,
                )
                attempt_logs.append(attempt)
                last_attempt = attempt
                attempt_idx += 1
                failure_summary = error_text
                previous_ir = None
                if accepted_score is not None:
                    break
                continue

            canonical_ir = adapter.canonicalize(parsed_ir)
            report, aux = adapter.check_with_runs(canonical_ir, mode)
            report_score = score_key(report)
            accepted_by_gate = is_strict_improvement(report_score, accepted_score)
            attempt = CoreAttemptLog(
                attempt_idx=attempt_idx,
                status=report.status,
                reason_codes_summary=sorted({r.code for r in report.reason_codes}),
                score_key=report_score,
                accepted_by_gate=accepted_by_gate,
                candidate_id=adapter.candidate_id(canonical_ir),
            )
            attempt_logs.append(attempt)
            last_attempt = attempt
            attempt_idx += 1

            previous_ir = canonical_ir
            failure_summary = adapter.build_failure_summary(report, aux)

            if accepted_by_gate:
                accepted_ir = canonical_ir
                accepted_report = report
                accepted_aux = aux
                accepted_score = report_score
            else:
                break

            if report.status == "PASS":
                break

        if (
            accepted_ir is not None
            and accepted_report is not None
            and accepted_score is not None
        ):
            accepted_candidates.append(
                CoreCandidate(
                    ir=accepted_ir,
                    report=accepted_report,
                    aux=accepted_aux,
                )
            )
        if abort_remaining_candidates:
            break

    return accepted_candidates, CoreProposerLog(
        provider="openai",
        api=api,
        model=model,
        created_at=created_at,
        k=max_candidates,
        n=max_repairs,
        attempts=attempt_logs,
        prompt_hash=_combine_hashes(prompt_hashes),
        response_hash=_combine_hashes(response_hashes),
        raw_prompt="\n\n---\n\n".join(raw_prompt_log) if want_raw else None,
        raw_response="\n\n---\n\n".join(raw_response_log) if want_raw else None,
    )
