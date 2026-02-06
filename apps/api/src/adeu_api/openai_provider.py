from __future__ import annotations

import json
import os
import urllib.error
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timezone

from adeu_ir import AdeuIR, CheckReport, Context, ReasonSeverity
from adeu_kernel import KernelMode, check
from pydantic import ValidationError

from .id_canonicalization import canonicalize_ir_ids

DEFAULT_OPENAI_MODEL = "gpt-5.2"
DEFAULT_MAX_CANDIDATES = 5
DEFAULT_MAX_REPAIRS = 3

_STATUS_SCORE = {"PASS": 0, "WARN": 1, "REFUSE": 2}


@dataclass(frozen=True)
class ProposerAttemptLog:
    attempt_idx: int
    status: str
    reason_codes_summary: list[str]
    candidate_ir_id: str | None = None


@dataclass(frozen=True)
class ProposerLog:
    provider: str
    model: str
    created_at: str
    attempts: list[ProposerAttemptLog]
    raw_prompt: str | None = None
    raw_response: str | None = None


def _env_flag(name: str) -> bool:
    return os.environ.get(name, "").strip() == "1"


def _openai_api_key() -> str | None:
    return os.environ.get("OPENAI_API_KEY") or os.environ.get("ADEU_OPENAI_API_KEY")


def _openai_model() -> str:
    return os.environ.get("ADEU_OPENAI_MODEL", DEFAULT_OPENAI_MODEL).strip() or DEFAULT_OPENAI_MODEL


def _openai_base_url() -> str:
    return os.environ.get("ADEU_OPENAI_BASE_URL", "https://api.openai.com/v1").rstrip("/")


def _score_reason_tuple(report: CheckReport) -> tuple[int, int, int, int, tuple[str, ...]]:
    # CheckReport-like object with `.status` and `.reason_codes[*].severity`/`.code`.
    status = getattr(report, "status", "REFUSE")
    status_score = _STATUS_SCORE.get(status, 99)
    reason_codes = getattr(report, "reason_codes", []) or []
    num_errors = sum(
        1 for r in reason_codes if getattr(r, "severity", None) == ReasonSeverity.ERROR
    )
    num_warns = sum(1 for r in reason_codes if getattr(r, "severity", None) == ReasonSeverity.WARN)
    codes = tuple(
        sorted(
            str(getattr(r, "code", ""))
            for r in reason_codes
            if getattr(r, "code", None)
        )
    )
    return (status_score, num_errors, num_warns, len(reason_codes), codes)


def _extract_json(text: str) -> object:
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        start = text.find("{")
        end = text.rfind("}")
        if start == -1 or end == -1 or end <= start:
            raise
        return json.loads(text[start : end + 1])


def _chat_completion_json(*, model: str, messages: list[dict[str, str]]) -> tuple[str, str]:
    api_key = _openai_api_key()
    if not api_key:
        raise RuntimeError("OpenAI provider not configured (set OPENAI_API_KEY)")

    base_url = _openai_base_url()
    url = f"{base_url}/chat/completions"
    payload = {
        "model": model,
        "messages": messages,
        "temperature": 0.3,
        "response_format": {"type": "json_object"},
    }
    raw_prompt = json.dumps(payload, ensure_ascii=False, sort_keys=True)

    req = urllib.request.Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "authorization": f"Bearer {api_key}",
            "content-type": "application/json",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:  # noqa: S310 (trusted host)
            raw = resp.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        detail = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"OpenAI HTTPError {e.code}: {detail}") from e

    data = json.loads(raw)
    choices = data.get("choices") or []
    if not choices:
        raise RuntimeError("OpenAI response missing choices")
    message = choices[0].get("message") or {}
    content = message.get("content")
    if not isinstance(content, str) or not content.strip():
        raise RuntimeError("OpenAI response missing message.content")
    return raw_prompt, content


def _initial_prompt(
    *, clause_text: str, context: Context, candidate_idx: int
) -> list[dict[str, str]]:
    ctx_json = context.model_dump(mode="json", exclude_none=True)
    return [
        {
            "role": "system",
            "content": (
                "You are ADEU Studio's proposer.\n"
                "Output ONLY a single JSON object that validates the ADEU IR schema.\n"
                "Do not include markdown fences. Do not include extra keys.\n"
                "If the clause has modal verbs (e.g., may/shall/must/should/will), include an "
                "ambiguity marker with ambiguity.issue='modality_ambiguity'."
            ),
        },
        {
            "role": "user",
            "content": (
                f"Candidate #{candidate_idx + 1}.\n\n"
                "Clause:\n"
                f"{clause_text}\n\n"
                "Context (must match exactly):\n"
                f"{json.dumps(ctx_json, ensure_ascii=False, sort_keys=True)}\n"
            ),
        },
    ]


def _repair_prompt(
    *,
    clause_text: str,
    context: Context,
    previous_ir: AdeuIR | None,
    failure_summary: str,
) -> list[dict[str, str]]:
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
    return [
        {
            "role": "system",
            "content": (
                "You are ADEU Studio's repair loop.\n"
                "Return ONLY corrected ADEU IR JSON that validates the schema.\n"
                "Do not include extra keys. Do not include markdown fences."
            ),
        },
        {
            "role": "user",
            "content": (
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
            ),
        },
    ]


def propose_openai(
    *,
    clause_text: str,
    context: Context,
    mode: KernelMode,
    max_candidates: int | None,
    max_repairs: int | None,
) -> tuple[list[tuple[AdeuIR, CheckReport]], ProposerLog, str]:
    model = _openai_model()
    want_raw = _env_flag("ADEU_LOG_RAW_LLM")

    k = DEFAULT_MAX_CANDIDATES if max_candidates is None else max_candidates
    n = DEFAULT_MAX_REPAIRS if max_repairs is None else max_repairs

    created_at = datetime.now(tz=timezone.utc).isoformat()
    attempt_logs: list[ProposerAttemptLog] = []
    raw_prompt_log: list[str] = []
    raw_response_log: list[str] = []

    final: list[tuple[AdeuIR, CheckReport]] = []
    attempt_idx = 0

    for cand_idx in range(k):
        best_ir: AdeuIR | None = None
        best_report: CheckReport | None = None
        best_key: tuple[int, int, int, int, tuple[str, ...]] | None = None
        previous_progress: tuple[int, int, int] | None = None
        seen_reason_sets: set[tuple[str, ...]] = set()

        previous_ir: AdeuIR | None = None
        failure_summary = ""

        for repair_idx in range(n + 1):
            if repair_idx == 0:
                messages = _initial_prompt(
                    clause_text=clause_text, context=context, candidate_idx=cand_idx
                )
            else:
                messages = _repair_prompt(
                    clause_text=clause_text,
                    context=context,
                    previous_ir=previous_ir,
                    failure_summary=failure_summary,
                )

            raw_prompt, content = _chat_completion_json(model=model, messages=messages)
            if want_raw:
                raw_prompt_log.append(raw_prompt)
                raw_response_log.append(content)

            try:
                payload = _extract_json(content)
            except json.JSONDecodeError as e:
                attempt_logs.append(
                    ProposerAttemptLog(
                        attempt_idx=attempt_idx,
                        status="PARSE_ERROR",
                        reason_codes_summary=["SCHEMA_INVALID"],
                        candidate_ir_id=None,
                    )
                )
                attempt_idx += 1
                failure_summary = f"Could not parse JSON: {e}"
                previous_ir = None
                continue

            try:
                ir = AdeuIR.model_validate(payload)
            except ValidationError as e:
                attempt_logs.append(
                    ProposerAttemptLog(
                        attempt_idx=attempt_idx,
                        status="PARSE_ERROR",
                        reason_codes_summary=["SCHEMA_INVALID"],
                        candidate_ir_id=None,
                    )
                )
                attempt_idx += 1
                failure_summary = f"ADEU IR schema validation failed: {e}"
                previous_ir = None
                continue

            # Fail-closed but enforce deterministic context/source_features.
            ir = ir.model_copy(update={"context": context})
            ir = canonicalize_ir_ids(ir)
            report = check(ir, mode=mode)
            key = _score_reason_tuple(report)
            progress = (key[0], key[1], key[3])
            attempt_logs.append(
                ProposerAttemptLog(
                    attempt_idx=attempt_idx,
                    status=str(getattr(report, "status", "REFUSE")),
                    reason_codes_summary=sorted(set(key[4])),
                    candidate_ir_id=ir.ir_id,
                )
            )
            attempt_idx += 1

            previous_ir = ir
            failure_summary = "\n".join(
                f"- {getattr(r, 'code', '')} {getattr(r, 'json_path', '')}"
                for r in getattr(report, "reason_codes", []) or []
            )

            if best_key is None or key < best_key:
                best_ir, best_report, best_key = ir, report, key

            if getattr(report, "status", "REFUSE") != "REFUSE":
                break

            # Stop early if the same refusal repeats.
            reason_set = key[4]
            if reason_set in seen_reason_sets:
                break
            if previous_progress is not None and progress == previous_progress:
                break
            seen_reason_sets.add(reason_set)
            previous_progress = progress

        if best_ir is not None and best_report is not None:
            final.append((best_ir, best_report))

    log = ProposerLog(
        provider="openai",
        model=model,
        created_at=created_at,
        attempts=attempt_logs,
        raw_prompt="\n\n---\n\n".join(raw_prompt_log) if want_raw else None,
        raw_response="\n\n---\n\n".join(raw_response_log) if want_raw else None,
    )
    return final, log, model
