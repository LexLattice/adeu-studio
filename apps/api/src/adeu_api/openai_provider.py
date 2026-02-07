from __future__ import annotations

import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any

from adeu_ir import AdeuIR, CheckReport, Context
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, check
from pydantic import ValidationError

from .id_canonicalization import canonicalize_ir_ids
from .openai_backends import BackendApi, build_openai_backend
from .openai_config import (
    env_flag,
    openai_api,
    openai_api_key,
    openai_base_url,
    openai_model,
)
from .openai_proposer_core import (
    CoreAttemptLog,
    ProposerAdapter,
    run_openai_repair_loop,
)

DEFAULT_MAX_CANDIDATES = 5
DEFAULT_MAX_REPAIRS = 3


@dataclass(frozen=True)
class ProposerAttemptLog:
    attempt_idx: int
    status: str
    reason_codes_summary: list[str]
    score_key: tuple[int, int, int, int] | None
    accepted_by_gate: bool
    candidate_ir_id: str | None = None


@dataclass(frozen=True)
class ProposerLog:
    provider: str
    api: BackendApi
    model: str
    created_at: str
    k: int
    n: int
    attempts: list[ProposerAttemptLog]
    prompt_hash: str | None = None
    response_hash: str | None = None
    raw_prompt: str | None = None
    raw_response: str | None = None


class _AdeuAdapter(ProposerAdapter[AdeuIR, None]):
    domain = "adeu"

    def __init__(self, *, clause_text: str, context: Context):
        self._clause_text = clause_text
        self._context = context

    def build_initial_prompt(self, *, candidate_idx: int) -> tuple[str, str]:
        ctx_json = self._context.model_dump(mode="json", exclude_none=True)
        system_prompt = (
            "You are ADEU Studio's proposer.\n"
            "Output ONLY a single JSON object that validates the ADEU IR schema.\n"
            "Do not include markdown fences. Do not include extra keys.\n"
            "If the clause has modal verbs (e.g., may/shall/must/should/will), include an "
            "ambiguity marker with ambiguity.issue='modality_ambiguity'."
        )
        user_prompt = (
            f"Candidate #{candidate_idx + 1}.\n\n"
            "Clause:\n"
            f"{self._clause_text}\n\n"
            "Context (must match exactly):\n"
            f"{json.dumps(ctx_json, ensure_ascii=False, sort_keys=True)}\n"
        )
        return system_prompt, user_prompt

    def build_repair_prompt(
        self,
        *,
        best_candidate: AdeuIR | None,
        last_attempt: CoreAttemptLog | None,
        failure_summary: str,
    ) -> tuple[str, str]:
        del last_attempt
        ctx_json = self._context.model_dump(mode="json", exclude_none=True)
        prev_json = (
            json.dumps(
                best_candidate.model_dump(mode="json", exclude_none=True),
                ensure_ascii=False,
                sort_keys=True,
            )
            if best_candidate is not None
            else "null"
        )
        system_prompt = (
            "You are ADEU Studio's repair loop.\n"
            "Return ONLY corrected ADEU IR JSON that validates the schema.\n"
            "Do not include extra keys. Do not include markdown fences."
        )
        user_prompt = (
            "Fix the ADEU IR so the kernel checker improves.\n\n"
            "Clause:\n"
            f"{self._clause_text}\n\n"
            "Context (must match exactly):\n"
            f"{json.dumps(ctx_json, ensure_ascii=False, sort_keys=True)}\n\n"
            "Previous IR JSON:\n"
            f"{prev_json}\n\n"
            "Checker failures (reason codes + paths):\n"
            f"{failure_summary}\n\n"
            "Return ONLY the corrected ADEU IR JSON object."
        )
        return system_prompt, user_prompt

    def parse_ir(self, payload: dict[str, Any]) -> tuple[AdeuIR | None, str | None]:
        try:
            return AdeuIR.model_validate(payload), None
        except ValidationError as exc:
            return None, f"ADEU IR schema validation failed: {exc}"

    def canonicalize(self, ir: AdeuIR) -> AdeuIR:
        return canonicalize_ir_ids(ir.model_copy(update={"context": self._context}))

    def check_with_runs(self, ir: AdeuIR, mode: KernelMode) -> tuple[CheckReport, None]:
        return check(ir, mode=mode), None

    def candidate_id(self, ir: AdeuIR) -> str:
        return ir.ir_id

    def classify_backend_error(self, error_text: str) -> list[str]:
        lowered = error_text.lower()
        if "http" in lowered or "request failed" in lowered or "openai " in lowered:
            return ["BACKEND_ERROR"]
        return ["SCHEMA_INVALID"]

    def classify_parse_error(self, parse_error_text: str) -> list[str]:
        del parse_error_text
        return ["SCHEMA_INVALID"]

    def build_failure_summary(self, report: CheckReport, aux: None) -> str:
        del aux
        return "\n".join(
            f"- {getattr(reason, 'code', '')} {getattr(reason, 'json_path', '')}"
            for reason in getattr(report, "reason_codes", []) or []
        )


@lru_cache(maxsize=1)
def _adeu_ir_json_schema() -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    schema_path = root / "packages" / "adeu_ir" / "schema" / "adeu.ir.v0.json"
    try:
        payload = json.loads(schema_path.read_text(encoding="utf-8"))
    except FileNotFoundError as e:
        raise RuntimeError(f"ADEU IR schema file not found: {schema_path}") from e
    except json.JSONDecodeError as e:
        raise RuntimeError(f"ADEU IR schema JSON invalid: {e}") from e
    if not isinstance(payload, dict):
        raise RuntimeError("ADEU IR schema root must be a JSON object")
    return payload


def propose_openai(
    *,
    clause_text: str,
    context: Context,
    mode: KernelMode,
    max_candidates: int | None,
    max_repairs: int | None,
) -> tuple[list[tuple[AdeuIR, CheckReport]], ProposerLog, str]:
    api_key = openai_api_key()
    if not api_key:
        raise RuntimeError("OpenAI provider not configured (set OPENAI_API_KEY)")

    api = openai_api()
    model = openai_model()
    base_url = openai_base_url()
    schema = _adeu_ir_json_schema()
    backend = build_openai_backend(api=api, api_key=api_key, base_url=base_url)
    want_raw = env_flag("ADEU_LOG_RAW_LLM")

    k = DEFAULT_MAX_CANDIDATES if max_candidates is None else max_candidates
    n = DEFAULT_MAX_REPAIRS if max_repairs is None else max_repairs

    adapter = _AdeuAdapter(clause_text=clause_text, context=context)
    core_candidates, core_log = run_openai_repair_loop(
        adapter=adapter,
        backend=backend,
        schema=schema,
        api=api,
        model=model,
        mode=mode,
        max_candidates=k,
        max_repairs=n,
        temperature=0.3,
        want_raw=want_raw,
    )

    proposals = [(item.ir, item.report) for item in core_candidates]
    log = ProposerLog(
        provider=core_log.provider,
        api=core_log.api,
        model=core_log.model,
        created_at=core_log.created_at,
        k=core_log.k,
        n=core_log.n,
        attempts=[
            ProposerAttemptLog(
                attempt_idx=attempt.attempt_idx,
                status=attempt.status,
                reason_codes_summary=attempt.reason_codes_summary,
                score_key=attempt.score_key,
                accepted_by_gate=attempt.accepted_by_gate,
                candidate_ir_id=attempt.candidate_id,
            )
            for attempt in core_log.attempts
        ],
        prompt_hash=core_log.prompt_hash,
        response_hash=core_log.response_hash,
        raw_prompt=core_log.raw_prompt,
        raw_response=core_log.raw_response,
    )
    return proposals, log, model
