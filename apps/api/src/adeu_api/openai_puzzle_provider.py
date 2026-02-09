from __future__ import annotations

import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any

from adeu_ir import CheckReport
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, ValidatorRunRecord
from adeu_puzzles import KnightsKnavesPuzzle
from adeu_puzzles import check_with_validator_runs as puzzle_check_with_validator_runs
from pydantic import ValidationError

from .openai_backends import BackendApi, build_openai_backend
from .openai_config import (
    env_flag,
    openai_api,
    openai_api_key,
    openai_base_url,
    openai_default_max_candidates,
    openai_default_max_repairs,
    openai_model,
    openai_temperature,
)
from .openai_proposer_core import (
    CoreAttemptLog,
    ProposerAdapter,
    run_openai_repair_loop,
)
from .puzzle_id_canonicalization import canonicalize_puzzle_ids

PuzzleProposal = tuple[KnightsKnavesPuzzle, CheckReport, list[ValidatorRunRecord]]


@dataclass(frozen=True)
class PuzzleProposerAttemptLog:
    attempt_idx: int
    status: str
    reason_codes_summary: list[str]
    score_key: tuple[int, int, int, int] | None
    accepted_by_gate: bool
    candidate_puzzle_id: str | None = None


@dataclass(frozen=True)
class PuzzleProposerLog:
    provider: str
    api: BackendApi
    model: str
    created_at: str
    k: int
    n: int
    source_features: dict[str, Any]
    attempts: list[PuzzleProposerAttemptLog]
    prompt_hash: str | None = None
    response_hash: str | None = None
    raw_prompt: str | None = None
    raw_response: str | None = None


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


class _PuzzleAdapter(ProposerAdapter[KnightsKnavesPuzzle, list[ValidatorRunRecord]]):
    domain = "puzzles"

    def __init__(
        self,
        *,
        puzzle_text: str,
        source_features: dict[str, Any],
        context_override: dict[str, Any] | None,
    ):
        self._puzzle_text = puzzle_text
        self._source_features = source_features
        self._context_override = context_override

    def build_initial_prompt(self, *, candidate_idx: int) -> tuple[str, str]:
        system_prompt = (
            "You are ADEU Studio's puzzle proposer.\n"
            "Output ONLY one JSON object matching the Knights/Knaves PuzzleIR schema.\n"
            "No markdown fences. No prose.\n"
            "Use stable IDs and valid references."
        )
        user_prompt = (
            f"Candidate #{candidate_idx + 1}.\n\n"
            "Puzzle text:\n"
            f"{self._puzzle_text}\n\n"
            "Deterministic source features:\n"
            f"{json.dumps(self._source_features, ensure_ascii=False, sort_keys=True)}\n\n"
            "Optional context override:\n"
            f"{json.dumps(self._context_override or {}, ensure_ascii=False, sort_keys=True)}"
        )
        return system_prompt, user_prompt

    def build_repair_prompt(
        self,
        *,
        best_candidate: KnightsKnavesPuzzle | None,
        last_attempt: CoreAttemptLog | None,
        failure_summary: str,
    ) -> tuple[str, str]:
        del last_attempt
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
            "You are ADEU Studio's puzzle repair loop.\n"
            "Return ONLY corrected PuzzleIR JSON that validates the schema.\n"
            "Do not include markdown or explanatory prose."
        )
        user_prompt = (
            "Fix the PuzzleIR so checker/solver outcomes improve.\n\n"
            "Puzzle text:\n"
            f"{self._puzzle_text}\n\n"
            "Deterministic source features:\n"
            f"{json.dumps(self._source_features, ensure_ascii=False, sort_keys=True)}\n\n"
            "Optional context override:\n"
            f"{json.dumps(self._context_override or {}, ensure_ascii=False, sort_keys=True)}\n\n"
            "Previous PuzzleIR JSON:\n"
            f"{prev_json}\n\n"
            "Checker failures + solver evidence:\n"
            f"{failure_summary}\n\n"
            "Return ONLY corrected PuzzleIR JSON."
        )
        return system_prompt, user_prompt

    def parse_ir(self, payload: dict[str, Any]) -> tuple[KnightsKnavesPuzzle | None, str | None]:
        try:
            return KnightsKnavesPuzzle.model_validate(payload), None
        except ValidationError as exc:
            return None, f"Puzzle schema validation failed: {exc}"

    def canonicalize(self, ir: KnightsKnavesPuzzle) -> KnightsKnavesPuzzle:
        return canonicalize_puzzle_ids(ir)

    def check_with_runs(
        self,
        ir: KnightsKnavesPuzzle,
        mode: KernelMode,
    ) -> tuple[CheckReport, list[ValidatorRunRecord]]:
        return puzzle_check_with_validator_runs(ir, mode=mode)

    def candidate_id(self, ir: KnightsKnavesPuzzle) -> str:
        return ir.puzzle_id

    def classify_backend_error(self, error_text: str) -> list[str]:
        lowered = error_text.lower()
        if "http" in lowered or "request failed" in lowered or "openai " in lowered:
            return ["BACKEND_ERROR"]
        return ["PUZZLE_SCHEMA_INVALID"]

    def classify_parse_error(self, parse_error_text: str) -> list[str]:
        del parse_error_text
        return ["PUZZLE_SCHEMA_INVALID"]

    def build_failure_summary(
        self,
        report: CheckReport,
        aux: list[ValidatorRunRecord],
    ) -> str:
        return _failure_summary(report, aux)


@lru_cache(maxsize=1)
def _puzzle_json_schema() -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    schema_path = (
        root / "packages" / "adeu_puzzles" / "schema" / "adeu.puzzle.knights_knaves.v0.json"
    )
    try:
        payload = json.loads(schema_path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RuntimeError(f"Puzzle schema file not found: {schema_path}") from exc
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"Puzzle schema JSON invalid: {exc}") from exc
    if not isinstance(payload, dict):
        raise RuntimeError("Puzzle schema root must be a JSON object")
    return payload


def propose_puzzle_openai(
    *,
    puzzle_text: str,
    mode: KernelMode,
    max_candidates: int | None,
    max_repairs: int | None,
    source_features: dict[str, Any],
    context_override: dict[str, Any] | None,
) -> tuple[list[PuzzleProposal], PuzzleProposerLog, str]:
    api_key = openai_api_key()
    if not api_key:
        raise RuntimeError("OpenAI provider not configured (set OPENAI_API_KEY)")

    api = openai_api()
    model = openai_model()
    base_url = openai_base_url()
    schema = _puzzle_json_schema()
    backend = build_openai_backend(api=api, api_key=api_key, base_url=base_url)
    want_raw = env_flag("ADEU_LOG_RAW_LLM")

    k = openai_default_max_candidates() if max_candidates is None else max_candidates
    n = openai_default_max_repairs() if max_repairs is None else max_repairs

    adapter = _PuzzleAdapter(
        puzzle_text=puzzle_text,
        source_features=source_features,
        context_override=context_override,
    )
    core_candidates, core_log = run_openai_repair_loop(
        adapter=adapter,
        backend=backend,
        schema=schema,
        api=api,
        model=model,
        mode=mode,
        max_candidates=k,
        max_repairs=n,
        temperature=openai_temperature(),
        want_raw=want_raw,
    )

    proposals = [(item.ir, item.report, item.aux) for item in core_candidates]
    log = PuzzleProposerLog(
        provider=core_log.provider,
        api=core_log.api,
        model=core_log.model,
        created_at=core_log.created_at,
        k=core_log.k,
        n=core_log.n,
        source_features=source_features,
        attempts=[
            PuzzleProposerAttemptLog(
                attempt_idx=attempt.attempt_idx,
                status=attempt.status,
                reason_codes_summary=attempt.reason_codes_summary,
                score_key=attempt.score_key,
                accepted_by_gate=attempt.accepted_by_gate,
                candidate_puzzle_id=attempt.candidate_id,
            )
            for attempt in core_log.attempts
        ],
        prompt_hash=core_log.prompt_hash,
        response_hash=core_log.response_hash,
        raw_prompt=core_log.raw_prompt,
        raw_response=core_log.raw_response,
    )
    return proposals, log, model
