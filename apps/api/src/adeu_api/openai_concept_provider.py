from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any, cast

from adeu_concepts import ConceptIR
from adeu_concepts import check_with_validator_runs as concept_check_with_validator_runs
from adeu_ir import CheckReport
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, ValidatorRunRecord
from pydantic import ValidationError

from .concept_id_canonicalization import canonicalize_concept_ids
from .openai_backends import BackendApi, build_openai_backend
from .scoring import is_strict_improvement, score_key

DEFAULT_OPENAI_MODEL = "gpt-5.2"
DEFAULT_OPENAI_API: BackendApi = "responses"
DEFAULT_MAX_CANDIDATES = 5
DEFAULT_MAX_REPAIRS = 3

ConceptProposal = tuple[ConceptIR, CheckReport, list[ValidatorRunRecord]]


@dataclass(frozen=True)
class ConceptProposerAttemptLog:
    attempt_idx: int
    status: str
    reason_codes_summary: list[str]
    score_key: tuple[int, int, int, int] | None
    accepted_by_gate: bool
    candidate_concept_id: str | None = None


@dataclass(frozen=True)
class ConceptProposerLog:
    provider: str
    api: BackendApi
    model: str
    created_at: str
    k: int
    n: int
    source_features: dict[str, Any]
    attempts: list[ConceptProposerAttemptLog]
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
def _concept_json_schema() -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    schema_path = root / "packages" / "adeu_concepts" / "schema" / "adeu.concepts.v0.json"
    try:
        payload = json.loads(schema_path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RuntimeError(f"Concept schema file not found: {schema_path}") from exc
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"Concept schema JSON invalid: {exc}") from exc
    if not isinstance(payload, dict):
        raise RuntimeError("Concept schema root must be a JSON object")
    return payload


def _combine_hashes(hashes: list[str]) -> str | None:
    if not hashes:
        return None
    return hashlib.sha256("|".join(hashes).encode("utf-8")).hexdigest()


def _error_reason_summary(error: str) -> list[str]:
    lowered = error.lower()
    if "http" in lowered or "request failed" in lowered or "openai " in lowered:
        return ["BACKEND_ERROR"]
    return ["CONCEPT_SCHEMA_INVALID"]


def _initial_prompt(
    *,
    source_text: str,
    source_features: dict[str, Any],
    candidate_idx: int,
) -> tuple[str, str]:
    system_prompt = (
        "You are ADEU Studio's concept proposer.\n"
        "Output ONLY one JSON object matching the ConceptIR schema.\n"
        "No markdown fences. No prose.\n"
        "Use stable IDs and valid references."
    )
    user_prompt = (
        f"Candidate #{candidate_idx + 1}.\n\n"
        "Source text:\n"
        f"{source_text}\n\n"
        "Deterministic source features:\n"
        f"{json.dumps(source_features, ensure_ascii=False, sort_keys=True)}"
    )
    return system_prompt, user_prompt


def _solver_evidence_summary(runs: list[ValidatorRunRecord]) -> str:
    if not runs:
        return "no_solver_runs"
    lines: list[str] = []
    for run_idx, run in enumerate(runs):
        lines.append(f"run[{run_idx}] status={run.result.status}")
        atom_lookup = {atom.assertion_name: atom for atom in run.request.payload.atom_map}
        unsat_core = sorted(run.result.evidence.unsat_core)
        if unsat_core:
            lines.append("  unsat_core:")
            for atom_name in unsat_core:
                atom = atom_lookup.get(atom_name)
                if atom is None:
                    lines.append(f"    - {atom_name}")
                    continue
                lines.append(
                    f"    - {atom_name} -> object_id={atom.object_id} json_path={atom.json_path}"
                )
        model_items = sorted(run.result.evidence.model.items())
        if model_items:
            lines.append("  sat_model:")
            for atom_name, value in model_items:
                atom = atom_lookup.get(atom_name)
                if atom is None:
                    continue
                lines.append(
                    "    - "
                    f"{atom_name}={value} -> object_id={atom.object_id} "
                    f"json_path={atom.json_path}"
                )
    return "\n".join(lines)


def _repair_prompt(
    *,
    source_text: str,
    source_features: dict[str, Any],
    previous_ir: ConceptIR | None,
    failure_summary: str,
) -> tuple[str, str]:
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
        "You are ADEU Studio's concept repair loop.\n"
        "Return ONLY corrected ConceptIR JSON that validates the schema.\n"
        "Do not include markdown or explanatory prose."
    )
    user_prompt = (
        "Fix the ConceptIR so checker/solver outcomes improve.\n\n"
        "Source text:\n"
        f"{source_text}\n\n"
        "Deterministic source features:\n"
        f"{json.dumps(source_features, ensure_ascii=False, sort_keys=True)}\n\n"
        "Previous ConceptIR JSON:\n"
        f"{prev_json}\n\n"
        "Checker failures + solver evidence:\n"
        f"{failure_summary}\n\n"
        "Return ONLY corrected ConceptIR JSON."
    )
    return system_prompt, user_prompt


def _failure_summary(report: CheckReport, runs: list[ValidatorRunRecord]) -> str:
    reason_lines = [
        f"- {reason.code} {reason.json_path or ''} {reason.message}"
        for reason in report.reason_codes
    ]
    trace_lines = [f"- {item.rule_id}: {','.join(item.because)}" for item in report.trace]
    solver_summary = _solver_evidence_summary(runs)
    return (
        "Reasons:\n"
        + ("\n".join(reason_lines) if reason_lines else "- none")
        + "\n\nTrace:\n"
        + ("\n".join(trace_lines) if trace_lines else "- none")
        + "\n\nSolver Evidence:\n"
        + solver_summary
    )


def propose_concept_openai(
    *,
    source_text: str,
    mode: KernelMode,
    max_candidates: int | None,
    max_repairs: int | None,
    source_features: dict[str, Any],
) -> tuple[list[ConceptProposal], ConceptProposerLog, str]:
    api_key = _openai_api_key()
    if not api_key:
        raise RuntimeError("OpenAI provider not configured (set OPENAI_API_KEY)")

    api = _openai_api()
    model = _openai_model()
    base_url = _openai_base_url()
    schema = _concept_json_schema()
    backend = build_openai_backend(api=api, api_key=api_key, base_url=base_url)
    want_raw = _env_flag("ADEU_LOG_RAW_LLM")

    k = DEFAULT_MAX_CANDIDATES if max_candidates is None else max_candidates
    n = DEFAULT_MAX_REPAIRS if max_repairs is None else max_repairs

    created_at = datetime.now(tz=timezone.utc).isoformat()
    attempt_logs: list[ConceptProposerAttemptLog] = []
    raw_prompt_log: list[str] = []
    raw_response_log: list[str] = []
    prompt_hashes: list[str] = []
    response_hashes: list[str] = []

    final: list[ConceptProposal] = []
    attempt_idx = 0
    abort_remaining_candidates = False

    for cand_idx in range(k):
        accepted_ir: ConceptIR | None = None
        accepted_report: CheckReport | None = None
        accepted_runs: list[ValidatorRunRecord] | None = None
        accepted_score: tuple[int, int, int, int] | None = None

        previous_ir: ConceptIR | None = None
        failure_summary = ""

        for repair_idx in range(n + 1):
            if repair_idx == 0:
                system_prompt, user_prompt = _initial_prompt(
                    source_text=source_text,
                    source_features=source_features,
                    candidate_idx=cand_idx,
                )
            else:
                system_prompt, user_prompt = _repair_prompt(
                    source_text=source_text,
                    source_features=source_features,
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
                    ConceptProposerAttemptLog(
                        attempt_idx=attempt_idx,
                        status="PARSE_ERROR",
                        reason_codes_summary=_error_reason_summary(error_text),
                        score_key=None,
                        accepted_by_gate=False,
                        candidate_concept_id=None,
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
                parsed = ConceptIR.model_validate(backend_result.parsed_json)
            except ValidationError as exc:
                attempt_logs.append(
                    ConceptProposerAttemptLog(
                        attempt_idx=attempt_idx,
                        status="PARSE_ERROR",
                        reason_codes_summary=["CONCEPT_SCHEMA_INVALID"],
                        score_key=None,
                        accepted_by_gate=False,
                        candidate_concept_id=None,
                    )
                )
                attempt_idx += 1
                failure_summary = f"Concept schema validation failed: {exc}"
                previous_ir = None
                if accepted_score is not None:
                    break
                continue

            concept = canonicalize_concept_ids(parsed)
            report, runs = concept_check_with_validator_runs(concept, mode=mode)
            report_score = score_key(report)
            accepted_by_gate = is_strict_improvement(report_score, accepted_score)
            attempt_logs.append(
                ConceptProposerAttemptLog(
                    attempt_idx=attempt_idx,
                    status=report.status,
                    reason_codes_summary=sorted({r.code for r in report.reason_codes}),
                    score_key=report_score,
                    accepted_by_gate=accepted_by_gate,
                    candidate_concept_id=concept.concept_id,
                )
            )
            attempt_idx += 1

            previous_ir = concept
            failure_summary = _failure_summary(report, runs)

            if accepted_by_gate:
                accepted_ir = concept
                accepted_report = report
                accepted_runs = runs
                accepted_score = report_score
            else:
                break

            if report.status == "PASS":
                break

        if accepted_ir is not None and accepted_report is not None and accepted_runs is not None:
            final.append((accepted_ir, accepted_report, accepted_runs))
        if abort_remaining_candidates:
            break

    log = ConceptProposerLog(
        provider="openai",
        api=api,
        model=model,
        created_at=created_at,
        k=k,
        n=n,
        source_features=source_features,
        attempts=attempt_logs,
        prompt_hash=_combine_hashes(prompt_hashes),
        response_hash=_combine_hashes(response_hashes),
        raw_prompt="\n\n---\n\n".join(raw_prompt_log) if want_raw else None,
        raw_response="\n\n---\n\n".join(raw_response_log) if want_raw else None,
    )
    return final, log, model
