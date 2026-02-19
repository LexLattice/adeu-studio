from __future__ import annotations

import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any

from adeu_concepts import ConceptIR
from adeu_concepts import check_with_validator_runs as concept_check_with_validator_runs
from adeu_ir import CheckReport
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, ValidatorRunRecord
from pydantic import ValidationError

from .codex_payload_normalization import normalize_codex_transport_payload
from .concept_id_canonicalization import canonicalize_concept_ids
from .openai_backends import (
    BackendApi,
    OpenAIBackend,
    build_codex_exec_backend,
    build_openai_backend,
)
from .openai_config import (
    codex_bin,
    codex_model,
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
    CoreProposerLog,
    ProposerAdapter,
    run_openai_repair_loop,
)

ConceptProposal = tuple[ConceptIR, CheckReport, list[ValidatorRunRecord]]
_OPTIONAL_LIST_FIELDS = ("terms", "senses", "claims", "links", "ambiguity", "bridges")


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


def _normalize_provenance_span(provenance: dict[str, Any]) -> None:
    span = provenance.get("span")
    if not isinstance(span, dict):
        return
    start = span.get("start")
    end = span.get("end")
    if isinstance(start, int) and isinstance(end, int) and end <= start:
        provenance["span"] = None


def _normalize_concept_payload_for_parse(payload: dict[str, Any]) -> dict[str, Any]:
    normalized = normalize_codex_transport_payload(payload)

    for field in _OPTIONAL_LIST_FIELDS:
        if normalized.get(field) is None:
            normalized[field] = []

    for field in ("terms", "senses", "claims", "links", "bridges"):
        rows = normalized.get(field)
        if not isinstance(rows, list):
            continue
        for row in rows:
            if not isinstance(row, dict):
                continue
            provenance = row.get("provenance")
            if isinstance(provenance, dict):
                _normalize_provenance_span(provenance)

    ambiguities = normalized.get("ambiguity")
    if isinstance(ambiguities, list):
        schema_version = normalized.get("schema_version", "adeu.concepts.v0")
        for ambiguity in ambiguities:
            if not isinstance(ambiguity, dict):
                continue
            option_details_by_id = ambiguity.get("option_details_by_id")
            if not isinstance(option_details_by_id, dict):
                continue
            for option_payload in option_details_by_id.values():
                if not isinstance(option_payload, dict):
                    continue
                if option_payload.get("patch") is None:
                    option_payload["patch"] = []
                variant_ir_id = option_payload.get("variant_ir_id")
                patch_value = option_payload.get("patch")
                if variant_ir_id is None and isinstance(patch_value, list) and not patch_value:
                    option_payload["patch"] = [
                        {
                            "op": "test",
                            "path": "/schema_version",
                            "value": schema_version,
                        }
                    ]

    return normalized


class _ConceptAdapter(ProposerAdapter[ConceptIR, list[ValidatorRunRecord]]):
    domain = "concepts"

    def __init__(
        self,
        *,
        source_text: str,
        source_features: dict[str, Any],
        normalize_parse_payload: bool = False,
    ):
        self._source_text = source_text
        self._source_features = source_features
        self._normalize_parse_payload = normalize_parse_payload

    def build_initial_prompt(self, *, candidate_idx: int) -> tuple[str, str]:
        system_prompt = (
            "You are ADEU Studio's concept proposer.\n"
            "Output ONLY one JSON object matching the ConceptIR schema.\n"
            "No markdown fences. No prose.\n"
            "Use stable IDs and valid references."
        )
        user_prompt = (
            f"Candidate #{candidate_idx + 1}.\n\n"
            "Source text:\n"
            f"{self._source_text}\n\n"
            "Deterministic source features:\n"
            f"{json.dumps(self._source_features, ensure_ascii=False, sort_keys=True)}"
        )
        return system_prompt, user_prompt

    def build_repair_prompt(
        self,
        *,
        best_candidate: ConceptIR | None,
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
            "You are ADEU Studio's concept repair loop.\n"
            "Return ONLY corrected ConceptIR JSON that validates the schema.\n"
            "Do not include markdown or explanatory prose."
        )
        user_prompt = (
            "Fix the ConceptIR so checker/solver outcomes improve.\n\n"
            "Source text:\n"
            f"{self._source_text}\n\n"
            "Deterministic source features:\n"
            f"{json.dumps(self._source_features, ensure_ascii=False, sort_keys=True)}\n\n"
            "Previous ConceptIR JSON:\n"
            f"{prev_json}\n\n"
            "Checker failures + solver evidence:\n"
            f"{failure_summary}\n\n"
            "Return ONLY corrected ConceptIR JSON."
        )
        return system_prompt, user_prompt

    def parse_ir(self, payload: dict[str, Any]) -> tuple[ConceptIR | None, str | None]:
        parse_payload = (
            _normalize_concept_payload_for_parse(payload)
            if self._normalize_parse_payload
            else payload
        )
        try:
            return ConceptIR.model_validate(parse_payload), None
        except ValidationError as exc:
            return None, f"Concept schema validation failed: {exc}"

    def canonicalize(self, ir: ConceptIR) -> ConceptIR:
        return canonicalize_concept_ids(ir)

    def check_with_runs(
        self,
        ir: ConceptIR,
        mode: KernelMode,
    ) -> tuple[CheckReport, list[ValidatorRunRecord]]:
        return concept_check_with_validator_runs(
            ir,
            mode=mode,
            source_text=self._source_text,
        )

    def candidate_id(self, ir: ConceptIR) -> str:
        return ir.concept_id

    def classify_backend_error(self, error_text: str) -> list[str]:
        lowered = error_text.lower()
        if (
            "http" in lowered
            or "request failed" in lowered
            or "openai " in lowered
            or "codex" in lowered
        ):
            return ["BACKEND_ERROR"]
        return ["CONCEPT_SCHEMA_INVALID"]

    def classify_parse_error(self, parse_error_text: str) -> list[str]:
        del parse_error_text
        return ["CONCEPT_SCHEMA_INVALID"]

    def build_failure_summary(
        self,
        report: CheckReport,
        aux: list[ValidatorRunRecord],
    ) -> str:
        return _failure_summary(report, aux)


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


def _resolve_loop_limits(
    *,
    max_candidates: int | None,
    max_repairs: int | None,
) -> tuple[int, int]:
    k = openai_default_max_candidates() if max_candidates is None else max_candidates
    n = openai_default_max_repairs() if max_repairs is None else max_repairs
    return k, n


def _build_concept_proposer_log(
    *,
    core_log: CoreProposerLog,
    source_features: dict[str, Any],
) -> ConceptProposerLog:
    return ConceptProposerLog(
        provider=core_log.provider,
        api=core_log.api,
        model=core_log.model,
        created_at=core_log.created_at,
        k=core_log.k,
        n=core_log.n,
        source_features=source_features,
        attempts=[
            ConceptProposerAttemptLog(
                attempt_idx=attempt.attempt_idx,
                status=attempt.status,
                reason_codes_summary=attempt.reason_codes_summary,
                score_key=attempt.score_key,
                accepted_by_gate=attempt.accepted_by_gate,
                candidate_concept_id=attempt.candidate_id,
            )
            for attempt in core_log.attempts
        ],
        prompt_hash=core_log.prompt_hash,
        response_hash=core_log.response_hash,
        raw_prompt=core_log.raw_prompt,
        raw_response=core_log.raw_response,
    )


def _propose_concept_with_backend(
    *,
    source_text: str,
    mode: KernelMode,
    max_candidates: int | None,
    max_repairs: int | None,
    source_features: dict[str, Any],
    api: BackendApi,
    model: str,
    backend: OpenAIBackend,
    temperature: float | None,
    provider_label: str,
) -> tuple[list[ConceptProposal], ConceptProposerLog, str]:
    schema = _concept_json_schema()
    want_raw = env_flag("ADEU_LOG_RAW_LLM")
    k, n = _resolve_loop_limits(max_candidates=max_candidates, max_repairs=max_repairs)

    adapter = _ConceptAdapter(
        source_text=source_text,
        source_features=source_features,
        normalize_parse_payload=provider_label == "codex",
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
        temperature=temperature,
        want_raw=want_raw,
        provider=provider_label,
    )

    proposals = [(item.ir, item.report, item.aux) for item in core_candidates]
    return (
        proposals,
        _build_concept_proposer_log(core_log=core_log, source_features=source_features),
        model,
    )


def propose_concept_openai(
    *,
    source_text: str,
    mode: KernelMode,
    max_candidates: int | None,
    max_repairs: int | None,
    source_features: dict[str, Any],
) -> tuple[list[ConceptProposal], ConceptProposerLog, str]:
    api_key = openai_api_key()
    if not api_key:
        raise RuntimeError("OpenAI provider not configured (set OPENAI_API_KEY)")

    api = openai_api()
    model = openai_model()
    base_url = openai_base_url()
    backend = build_openai_backend(api=api, api_key=api_key, base_url=base_url)
    return _propose_concept_with_backend(
        source_text=source_text,
        mode=mode,
        max_candidates=max_candidates,
        max_repairs=max_repairs,
        source_features=source_features,
        api=api,
        model=model,
        backend=backend,
        temperature=openai_temperature(),
        provider_label="openai",
    )


def propose_concept_codex(
    *,
    source_text: str,
    mode: KernelMode,
    max_candidates: int | None,
    max_repairs: int | None,
    source_features: dict[str, Any],
) -> tuple[list[ConceptProposal], ConceptProposerLog, str]:
    api: BackendApi = "codex_exec"
    model = codex_model()
    backend = build_codex_exec_backend(codex_bin=codex_bin())
    return _propose_concept_with_backend(
        source_text=source_text,
        mode=mode,
        max_candidates=max_candidates,
        max_repairs=max_repairs,
        source_features=source_features,
        api=api,
        model=model,
        backend=backend,
        temperature=None,
        provider_label="codex",
    )
