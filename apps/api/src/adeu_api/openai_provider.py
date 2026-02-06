from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any, cast

from adeu_ir import AdeuIR, CheckReport, Context
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, check
from pydantic import ValidationError

from .id_canonicalization import canonicalize_ir_ids
from .openai_backends import BackendApi, build_openai_backend
from .scoring import is_strict_improvement, score_key

DEFAULT_OPENAI_MODEL = "gpt-5.2"
DEFAULT_OPENAI_API: BackendApi = "responses"
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


def _env_flag(name: str) -> bool:
    return os.environ.get(name, "").strip() == "1"


def _openai_api_key() -> str | None:
    return os.environ.get("OPENAI_API_KEY") or os.environ.get("ADEU_OPENAI_API_KEY")


def _openai_model() -> str:
    return os.environ.get("ADEU_OPENAI_MODEL", DEFAULT_OPENAI_MODEL).strip() or DEFAULT_OPENAI_MODEL


def _openai_api() -> BackendApi:
    value = os.environ.get("ADEU_OPENAI_API", DEFAULT_OPENAI_API).strip().lower()
    if value in {"responses", "chat"}:
        return cast(BackendApi, value)
    raise RuntimeError("ADEU_OPENAI_API must be one of: responses, chat")


def _openai_base_url() -> str:
    return os.environ.get("ADEU_OPENAI_BASE_URL", "https://api.openai.com/v1").rstrip("/")


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


def _combine_hashes(hashes: list[str]) -> str | None:
    if not hashes:
        return None
    return hashlib.sha256("|".join(hashes).encode("utf-8")).hexdigest()


def _error_reason_summary(error: str) -> list[str]:
    lowered = error.lower()
    if "http" in lowered or "request failed" in lowered or "openai " in lowered:
        return ["BACKEND_ERROR"]
    return ["SCHEMA_INVALID"]


def _initial_prompt(*, clause_text: str, context: Context, candidate_idx: int) -> tuple[str, str]:
    ctx_json = context.model_dump(mode="json", exclude_none=True)
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
        f"{clause_text}\n\n"
        "Context (must match exactly):\n"
        f"{json.dumps(ctx_json, ensure_ascii=False, sort_keys=True)}\n"
    )
    return system_prompt, user_prompt


def _repair_prompt(
    *,
    clause_text: str,
    context: Context,
    previous_ir: AdeuIR | None,
    failure_summary: str,
) -> tuple[str, str]:
    ctx_json = context.model_dump(mode="json", exclude_none=True)
    prev_json = (
        json.dumps(
            previous_ir.model_dump(mode="json", exclude_none=True),
            ensure_ascii=False,
            sort_keys=True,
        )
        if previous_ir is not None
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
        f"{clause_text}\n\n"
        "Context (must match exactly):\n"
        f"{json.dumps(ctx_json, ensure_ascii=False, sort_keys=True)}\n\n"
        "Previous IR JSON:\n"
        f"{prev_json}\n\n"
        "Checker failures (reason codes + paths):\n"
        f"{failure_summary}\n\n"
        "Return ONLY the corrected ADEU IR JSON object."
    )
    return system_prompt, user_prompt


def propose_openai(
    *,
    clause_text: str,
    context: Context,
    mode: KernelMode,
    max_candidates: int | None,
    max_repairs: int | None,
) -> tuple[list[tuple[AdeuIR, CheckReport]], ProposerLog, str]:
    api_key = _openai_api_key()
    if not api_key:
        raise RuntimeError("OpenAI provider not configured (set OPENAI_API_KEY)")

    api = _openai_api()
    model = _openai_model()
    base_url = _openai_base_url()
    schema = _adeu_ir_json_schema()
    backend = build_openai_backend(api=api, api_key=api_key, base_url=base_url)
    want_raw = _env_flag("ADEU_LOG_RAW_LLM")

    k = DEFAULT_MAX_CANDIDATES if max_candidates is None else max_candidates
    n = DEFAULT_MAX_REPAIRS if max_repairs is None else max_repairs

    created_at = datetime.now(tz=timezone.utc).isoformat()
    attempt_logs: list[ProposerAttemptLog] = []
    raw_prompt_log: list[str] = []
    raw_response_log: list[str] = []
    prompt_hashes: list[str] = []
    response_hashes: list[str] = []

    final: list[tuple[AdeuIR, CheckReport]] = []
    attempt_idx = 0
    abort_remaining_candidates = False

    for cand_idx in range(k):
        accepted_ir: AdeuIR | None = None
        accepted_report: CheckReport | None = None
        accepted_score: tuple[int, int, int, int] | None = None

        previous_ir: AdeuIR | None = None
        failure_summary = ""

        for repair_idx in range(n + 1):
            if repair_idx == 0:
                system_prompt, user_prompt = _initial_prompt(
                    clause_text=clause_text,
                    context=context,
                    candidate_idx=cand_idx,
                )
            else:
                system_prompt, user_prompt = _repair_prompt(
                    clause_text=clause_text,
                    context=context,
                    previous_ir=previous_ir,
                    failure_summary=failure_summary,
                )

            backend_result = backend.generate_ir_json(
                system_prompt=system_prompt,
                user_prompt=user_prompt,
                json_schema=schema,
                model=model,
                temperature=0.3,
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
                attempt_logs.append(
                    ProposerAttemptLog(
                        attempt_idx=attempt_idx,
                        status="PARSE_ERROR",
                        reason_codes_summary=_error_reason_summary(error_text),
                        score_key=None,
                        accepted_by_gate=False,
                        candidate_ir_id=None,
                    )
                )
                attempt_idx += 1
                failure_summary = error_text
                previous_ir = None

                if accepted_score is not None:
                    break
                if api == "responses" and "error" in error_text.lower():
                    abort_remaining_candidates = True
                    break
                continue

            try:
                ir = AdeuIR.model_validate(backend_result.parsed_json)
            except ValidationError as e:
                attempt_logs.append(
                    ProposerAttemptLog(
                        attempt_idx=attempt_idx,
                        status="PARSE_ERROR",
                        reason_codes_summary=["SCHEMA_INVALID"],
                        score_key=None,
                        accepted_by_gate=False,
                        candidate_ir_id=None,
                    )
                )
                attempt_idx += 1
                failure_summary = f"ADEU IR schema validation failed: {e}"
                previous_ir = None
                if accepted_score is not None:
                    break
                continue

            ir = ir.model_copy(update={"context": context})
            ir = canonicalize_ir_ids(ir)
            report = check(ir, mode=mode)
            report_score = score_key(report)
            accepted_by_gate = is_strict_improvement(report_score, accepted_score)

            attempt_logs.append(
                ProposerAttemptLog(
                    attempt_idx=attempt_idx,
                    status=str(getattr(report, "status", "REFUSE")),
                    reason_codes_summary=sorted({r.code for r in report.reason_codes}),
                    score_key=report_score,
                    accepted_by_gate=accepted_by_gate,
                    candidate_ir_id=ir.ir_id,
                )
            )
            attempt_idx += 1

            previous_ir = ir
            failure_summary = "\n".join(
                f"- {getattr(r, 'code', '')} {getattr(r, 'json_path', '')}"
                for r in getattr(report, "reason_codes", []) or []
            )

            if accepted_by_gate:
                accepted_ir = ir
                accepted_report = report
                accepted_score = report_score
            else:
                break

            if getattr(report, "status", "REFUSE") == "PASS":
                break

        if accepted_ir is not None and accepted_report is not None:
            final.append((accepted_ir, accepted_report))
        if abort_remaining_candidates:
            break

    log = ProposerLog(
        provider="openai",
        api=api,
        model=model,
        created_at=created_at,
        k=k,
        n=n,
        attempts=attempt_logs,
        prompt_hash=_combine_hashes(prompt_hashes),
        response_hash=_combine_hashes(response_hashes),
        raw_prompt="\n\n---\n\n".join(raw_prompt_log) if want_raw else None,
        raw_response="\n\n---\n\n".join(raw_response_log) if want_raw else None,
    )
    return final, log, model
