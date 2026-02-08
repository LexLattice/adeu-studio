from __future__ import annotations

import hashlib
import os
import sqlite3
from datetime import datetime, timezone
from typing import Any, Callable, Literal

from adeu_concepts import (
    ConceptAnalysis,
    ConceptIR,
    ConceptRunRef,
    analyze_concept,
    pick_latest_run,
    strip_analysis_details,
    strip_forced_details,
)
from adeu_concepts import (
    check_with_solver_status as check_concept_with_solver_status,
)
from adeu_concepts import (
    check_with_validator_runs as check_concept_with_validator_runs,
)
from adeu_explain import (
    ConceptAnalysisDelta,
    DiffReport,
    FlipExplanation,
    ForcedEdgeKey,
    ValidatorRunInput,
    build_diff_report,
    build_flip_explanation,
)
from adeu_ir import (
    AdeuIR,
    CheckReport,
    Context,
    ProofArtifact,
    ProofInput,
    ReasonSeverity,
    TraceItem,
)
from adeu_kernel import (
    KernelMode,
    PatchValidationError,
    ValidatorRunRecord,
    apply_ambiguity_option,
    build_adeu_core_proof_requests,
    build_proof_backend,
    build_validator_backend,
    check,
    check_with_validator_runs,
)
from adeu_puzzles import (
    KnightsKnavesPuzzle,
    PuzzleSolveResult,
    solve_knights_knaves,
)
from adeu_puzzles import (
    check_with_validator_runs as check_puzzle_with_validator_runs,
)
from fastapi import FastAPI, HTTPException, Query
from pydantic import BaseModel, ConfigDict, Field

from .concept_id_canonicalization import canonicalize_concept_ids
from .concept_mock_provider import get_concept_fixture_bundle
from .concept_source_features import extract_concept_source_features
from .id_canonicalization import canonicalize_ir_ids
from .mock_provider import load_fixture_bundles
from .openai_concept_provider import propose_concept_openai
from .puzzle_id_canonicalization import canonicalize_puzzle_ids
from .puzzle_mock_provider import get_puzzle_fixture_bundle
from .puzzle_source_features import extract_puzzle_source_features
from .scoring import ranking_sort_key, score_key
from .source_features import extract_source_features
from .storage import (
    create_artifact,
    create_concept_artifact,
    create_proof_artifact,
    create_validator_run,
    get_artifact,
    get_concept_artifact,
    list_artifacts,
    list_concept_artifacts,
    list_concept_validator_runs,
    list_proof_artifacts,
    list_validator_runs,
    transaction as storage_transaction,
)

MAX_SOURCE_TEXT_BYTES = 200_000


class ProposeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    clause_text: str = Field(min_length=1)
    provider: Literal["mock", "openai"] = "mock"
    mode: KernelMode = KernelMode.LAX
    context: Context | None = None
    max_candidates: int | None = Field(default=None, ge=1, le=20)
    max_repairs: int | None = Field(default=None, ge=0, le=10)


class ProviderInfo(BaseModel):
    model_config = ConfigDict(extra="forbid")
    kind: Literal["mock", "openai"]
    api: str | None = None
    model: str | None = None


class ProposerAttempt(BaseModel):
    model_config = ConfigDict(extra="forbid")
    attempt_idx: int
    status: Literal["PASS", "WARN", "REFUSE", "PARSE_ERROR"]
    reason_codes_summary: list[str] = Field(default_factory=list)
    score_key: tuple[int, int, int, int] | None = None
    accepted_by_gate: bool | None = None
    candidate_rank: int | None = None


class ProposerLog(BaseModel):
    model_config = ConfigDict(extra="forbid")
    provider: str
    api: str | None = None
    model: str | None = None
    created_at: str
    k: int | None = None
    n: int | None = None
    source_features: dict[str, Any] | None = None
    attempts: list[ProposerAttempt] = Field(default_factory=list)
    prompt_hash: str | None = None
    response_hash: str | None = None
    raw_prompt: str | None = None
    raw_response: str | None = None


class ProposeCandidate(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: AdeuIR
    check_report: CheckReport
    rank: int


class ProposeResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    provider: ProviderInfo
    candidates: list[ProposeCandidate]
    proposer_log: ProposerLog


class CheckRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: AdeuIR
    mode: KernelMode = KernelMode.LAX


class PuzzleCheckRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    puzzle: KnightsKnavesPuzzle
    mode: KernelMode = KernelMode.LAX


class ConceptCheckRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    source_text: str | None = None
    mode: KernelMode = KernelMode.LAX


class ConceptAnalyzeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    source_text: str | None = None
    mode: KernelMode = KernelMode.LAX
    include_validator_runs: bool = False
    include_analysis_details: bool = True
    include_forced_details: bool = True
    validator_runs: list[ValidatorRunInput] | None = None


class ConceptArtifactCreateRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    source_text: str = Field(min_length=1)
    ir: ConceptIR
    mode: KernelMode = KernelMode.STRICT


class PuzzleProposeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    puzzle_text: str = Field(min_length=1)
    provider: Literal["mock", "openai"] = "mock"
    mode: KernelMode = KernelMode.LAX
    context_override: dict[str, Any] | None = None
    max_candidates: int | None = Field(default=None, ge=1, le=20)
    max_repairs: int | None = Field(default=None, ge=0, le=10)


class ConceptProposeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    source_text: str = Field(min_length=1)
    provider: Literal["mock", "openai"] = "mock"
    mode: KernelMode = KernelMode.LAX
    max_candidates: int | None = Field(default=None, ge=1, le=20)
    max_repairs: int | None = Field(default=None, ge=0, le=10)


class PuzzleSolveRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    puzzle: KnightsKnavesPuzzle
    backend: Literal["z3", "mock"] = "z3"


class DiffRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    left_ir: AdeuIR
    right_ir: AdeuIR
    mode: KernelMode = KernelMode.LAX
    left_validator_runs: list[ValidatorRunInput] | None = None
    right_validator_runs: list[ValidatorRunInput] | None = None
    left_artifact_id: str | None = None
    right_artifact_id: str | None = None


class ConceptDiffRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    left_ir: ConceptIR
    right_ir: ConceptIR
    mode: KernelMode = KernelMode.LAX
    left_source_text: str | None = None
    right_source_text: str | None = None
    left_validator_runs: list[ValidatorRunInput] | None = None
    right_validator_runs: list[ValidatorRunInput] | None = None


class PuzzleDiffRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    left_ir: KnightsKnavesPuzzle
    right_ir: KnightsKnavesPuzzle
    mode: KernelMode = KernelMode.LAX
    left_validator_runs: list[ValidatorRunInput] | None = None
    right_validator_runs: list[ValidatorRunInput] | None = None


class ExplainFlipBaseRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    mode: KernelMode = KernelMode.LAX
    include_analysis_delta: bool = False
    include_forced_details: bool = False
    left_validator_runs: list[ValidatorRunInput] | None = None
    right_validator_runs: list[ValidatorRunInput] | None = None
    left_source_text: str | None = None
    right_source_text: str | None = None
    additional_solver_call_budget: int | None = Field(default=None, ge=0, le=200)


class ExplainFlipAdeuRequest(ExplainFlipBaseRequest):
    domain: Literal["adeu"]
    left_ir: AdeuIR
    right_ir: AdeuIR


class ExplainFlipConceptsRequest(ExplainFlipBaseRequest):
    domain: Literal["concepts"]
    left_ir: ConceptIR
    right_ir: ConceptIR


class ExplainFlipPuzzlesRequest(ExplainFlipBaseRequest):
    domain: Literal["puzzles"]
    left_ir: KnightsKnavesPuzzle
    right_ir: KnightsKnavesPuzzle


ExplainFlipRequest = ExplainFlipAdeuRequest | ExplainFlipConceptsRequest | ExplainFlipPuzzlesRequest


class ApplyAmbiguityOptionRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: AdeuIR
    ambiguity_id: str = Field(min_length=1)
    option_id: str = Field(min_length=1)
    variants_by_id: dict[str, AdeuIR] | None = None
    mode: KernelMode = KernelMode.LAX


class ApplyAmbiguityOptionResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    patched_ir: AdeuIR
    check_report: CheckReport


class ArtifactCreateRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    clause_text: str = Field(min_length=1)
    ir: AdeuIR
    mode: KernelMode = KernelMode.STRICT


class ArtifactCreateResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    created_at: str
    check_report: CheckReport


class ArtifactGetResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    created_at: str
    clause_text: str
    ir: AdeuIR
    check_report: CheckReport


class ArtifactSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    created_at: str
    doc_id: str | None
    jurisdiction: str | None
    status: str | None
    num_errors: int | None
    num_warns: int | None


class ArtifactListResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    items: list[ArtifactSummary]


class StoredProofArtifact(BaseModel):
    model_config = ConfigDict(extra="forbid")
    proof: ProofArtifact
    artifact_id: str
    created_at: str


class ArtifactProofListResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    items: list[StoredProofArtifact]


class StoredValidatorRun(BaseModel):
    model_config = ConfigDict(extra="forbid")
    run_id: str
    artifact_id: str | None
    concept_artifact_id: str | None = None
    created_at: str
    backend: str
    backend_version: str | None
    timeout_ms: int
    options_json: dict[str, object]
    request_hash: str
    formula_hash: str
    status: str
    evidence_json: dict[str, object]
    atom_map_json: dict[str, object]


class ArtifactValidatorRunsResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    items: list[StoredValidatorRun]


app = FastAPI(title="ADEU Studio API")


class PuzzleProposeCandidate(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: KnightsKnavesPuzzle
    check_report: CheckReport
    rank: int


class PuzzleProposeResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    provider: ProviderInfo
    candidates: list[PuzzleProposeCandidate]
    proposer_log: ProposerLog


class ConceptProposeCandidate(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    check_report: CheckReport
    rank: int


class ConceptProposeResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    provider: ProviderInfo
    candidates: list[ConceptProposeCandidate]
    proposer_log: ProposerLog


class ConceptAnalyzeResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    check_report: CheckReport
    analysis: ConceptAnalysis
    validator_runs: list[ValidatorRunInput] | None = None


class ExplainFlipResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    diff_report: DiffReport
    flip_explanation: FlipExplanation
    analysis_delta: ConceptAnalysisDelta | None = None
    run_ir_mismatch: bool = False
    left_mismatch: bool = False
    right_mismatch: bool = False


class ConceptArtifactCreateResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    created_at: str
    check_report: CheckReport
    analysis: ConceptAnalysis | None = None


class ConceptArtifactSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    created_at: str
    doc_id: str | None
    status: str | None
    num_errors: int | None
    num_warns: int | None


class ConceptArtifactListResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    items: list[ConceptArtifactSummary]


class ConceptArtifactGetResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    created_at: str
    schema_version: str
    artifact_version: int
    source_text: str
    ir: ConceptIR
    check_report: CheckReport
    analysis: ConceptAnalysis | None = None


def _env_flag(name: str) -> bool:
    return os.environ.get(name, "").strip() == "1"


def _enforce_source_text_size(source_text: str, *, field: str = "source_text") -> None:
    size_bytes = len(source_text.encode("utf-8"))
    if size_bytes <= MAX_SOURCE_TEXT_BYTES:
        return
    raise HTTPException(
        status_code=400,
        detail={
            "code": "PAYLOAD_TOO_LARGE",
            "message": (
                f"{field} exceeds {MAX_SOURCE_TEXT_BYTES} bytes "
                f"(got {size_bytes} bytes)"
            ),
            "field": field,
            "max_bytes": MAX_SOURCE_TEXT_BYTES,
            "actual_bytes": size_bytes,
        },
    )


def _persist_validator_runs(
    *,
    runs: list[ValidatorRunRecord],
    artifact_id: str | None,
    concept_artifact_id: str | None = None,
    connection: sqlite3.Connection | None = None,
) -> None:
    for run in runs:
        atom_map = {
            atom.assertion_name: {
                "object_id": atom.object_id,
                "json_path": atom.json_path,
            }
            for atom in run.request.payload.atom_map
        }
        create_validator_run(
            artifact_id=artifact_id,
            concept_artifact_id=concept_artifact_id,
            backend=run.result.backend,
            backend_version=run.result.backend_version,
            timeout_ms=run.result.timeout_ms,
            options_json=run.result.options,
            request_hash=run.result.request_hash,
            formula_hash=run.result.formula_hash,
            status=run.result.status,
            evidence_json=run.result.evidence.model_dump(mode="json", exclude_none=True),
            atom_map_json=atom_map,
            connection=connection,
        )


def _validator_run_input_from_record(run: ValidatorRunRecord) -> ValidatorRunInput:
    return ValidatorRunInput(
        run_id=None,
        created_at=None,
        backend=run.result.backend,
        backend_version=run.result.backend_version,
        timeout_ms=run.result.timeout_ms,
        options_json=run.result.options,
        request_hash=run.result.request_hash,
        formula_hash=run.result.formula_hash,
        status=run.result.status,
        evidence_json=run.result.evidence.model_dump(mode="json", exclude_none=True),
        atom_map_json={
            atom.assertion_name: {
                "object_id": atom.object_id,
                "json_path": atom.json_path,
            }
            for atom in run.request.payload.atom_map
        },
    )


def _normalize_validator_run_input(run: ValidatorRunInput) -> ValidatorRunInput:
    if isinstance(run.atom_map_json, dict):
        atom_map = {
            name: {
                "object_id": ref.object_id if hasattr(ref, "object_id") else ref.get("object_id"),
                "json_path": ref.json_path if hasattr(ref, "json_path") else ref.get("json_path"),
            }
            for name, ref in run.atom_map_json.items()
        }
    else:
        atom_map = {
            ref.assertion_name: {
                "object_id": ref.object_id,
                "json_path": ref.json_path,
            }
            for ref in run.atom_map_json
        }
    payload = run.model_dump(mode="python")
    payload["atom_map_json"] = atom_map
    return ValidatorRunInput.model_validate(payload)


def _concept_run_ref_from_input(run: ValidatorRunInput) -> ConceptRunRef:
    run = _normalize_validator_run_input(run)
    atom_map: dict[str, dict[str, str | None]] = {
        name: {
            "object_id": ref.object_id,
            "json_path": ref.json_path,
        }
        for name, ref in run.atom_map_json.items()
    }
    evidence_json = run.evidence_json or {}
    unsat_core_raw = evidence_json.get("unsat_core")
    if isinstance(unsat_core_raw, list):
        unsat_core = [str(item) for item in unsat_core_raw]
    else:
        unsat_core = []

    model_raw = evidence_json.get("model")
    model: dict[str, object] = {}
    if isinstance(model_raw, dict):
        model = {str(key): value for key, value in model_raw.items()}
    error_raw = evidence_json.get("error")
    error_text = str(error_raw) if isinstance(error_raw, str) else None

    return ConceptRunRef(
        run_id=run.run_id,
        created_at=run.created_at,
        status=run.status,
        request_hash=run.request_hash,
        formula_hash=run.formula_hash,
        evidence_model=model,
        evidence_unsat_core=unsat_core,
        evidence_error=error_text,
        atom_map_json=atom_map,
    )


def _sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _configured_proof_backend_kind() -> Literal["mock", "lean"]:
    value = os.environ.get("ADEU_PROOF_BACKEND", "mock").strip().lower()
    if value == "mock":
        return "mock"
    if value == "lean":
        return "lean"
    return "mock"


def _proof_inputs_from_validator_runs(runs: list[ValidatorRunRecord]) -> list[ProofInput]:
    inputs: list[ProofInput] = []
    seen: set[tuple[str | None, str | None, str | None]] = set()
    for run in runs:
        formula_hash = run.result.formula_hash
        origins = run.request.origin or []
        if origins:
            for origin in origins:
                key = (origin.object_id, origin.json_path, formula_hash)
                if key in seen:
                    continue
                seen.add(key)
                inputs.append(
                    ProofInput(
                        object_id=origin.object_id,
                        json_path=origin.json_path,
                        formula_hash=formula_hash,
                    )
                )
        else:
            key = (None, None, formula_hash)
            if key in seen:
                continue
            seen.add(key)
            inputs.append(ProofInput(formula_hash=formula_hash))
    return inputs


def _persist_proof_artifact(
    *,
    artifact_id: str,
    ir: AdeuIR,
    runs: list[ValidatorRunRecord],
    connection: sqlite3.Connection | None = None,
) -> None:
    inputs = _proof_inputs_from_validator_runs(runs)
    obligations = build_adeu_core_proof_requests(
        theorem_prefix=ir.ir_id,
        inputs=inputs,
    )
    backend_kind = _configured_proof_backend_kind()
    backend_error: str | None = None
    try:
        backend = build_proof_backend()
    except RuntimeError as exc:
        backend = None
        backend_error = str(exc)

    for obligation in obligations:
        theorem_id = obligation.theorem_id
        theorem_src = obligation.theorem_src
        try:
            if backend is None:
                raise RuntimeError(backend_error or "proof backend unavailable")
            proof = backend.check(
                theorem_id=theorem_id,
                theorem_src=theorem_src,
                inputs=obligation.inputs,
            )
        except RuntimeError as exc:
            proof = ProofArtifact(
                proof_id=f"proof_{_sha256(theorem_id + str(exc))[:16]}",
                backend=backend_kind,
                theorem_id=theorem_id,
                status="failed",
                proof_hash=_sha256(theorem_src + str(exc)),
                inputs=obligation.inputs,
                details={"error": str(exc)},
            )

        details = dict(proof.details)
        details.setdefault("backend_proof_id", proof.proof_id)
        details.setdefault("semantics_version", obligation.semantics_version)
        details.setdefault("inputs_hash", obligation.metadata.get("inputs_hash"))
        details.setdefault("theorem_src_hash", obligation.metadata.get("theorem_src_hash"))
        details.setdefault("obligation_kind", obligation.obligation_kind)
        create_proof_artifact(
            artifact_id=artifact_id,
            backend=proof.backend,
            theorem_id=proof.theorem_id,
            status=proof.status,
            proof_hash=proof.proof_hash,
            inputs_json=[item.model_dump(mode="json", exclude_none=True) for item in proof.inputs],
            details_json=details,
            connection=connection,
        )


def _score_and_rank_proposals(
    proposals: list[tuple[AdeuIR, CheckReport]],
) -> list[ProposeCandidate]:
    scored: list[tuple[tuple[int, int, int, int], str, AdeuIR, CheckReport]] = [
        (score_key(report), ir.ir_id, ir, report) for ir, report in proposals
    ]
    scored.sort(key=lambda item: ranking_sort_key(item[0], item[1]))
    return [
        ProposeCandidate(ir=ir, check_report=report, rank=rank)
        for rank, (_, _, ir, report) in enumerate(scored)
    ]


def _score_and_rank_puzzle_proposals(
    proposals: list[tuple[KnightsKnavesPuzzle, CheckReport]],
) -> list[PuzzleProposeCandidate]:
    scored: list[tuple[tuple[int, int, int, int], str, KnightsKnavesPuzzle, CheckReport]] = [
        (score_key(report), puzzle.puzzle_id, puzzle, report) for puzzle, report in proposals
    ]
    scored.sort(key=lambda item: ranking_sort_key(item[0], item[1]))
    return [
        PuzzleProposeCandidate(ir=puzzle, check_report=report, rank=rank)
        for rank, (_, _, puzzle, report) in enumerate(scored)
    ]


def _score_and_rank_concept_proposals(
    proposals: list[tuple[ConceptIR, CheckReport]],
) -> list[ConceptProposeCandidate]:
    scored: list[tuple[tuple[int, int, int, int], str, ConceptIR, CheckReport]] = [
        (score_key(report), concept.concept_id, concept, report) for concept, report in proposals
    ]
    scored.sort(key=lambda item: ranking_sort_key(item[0], item[1]))
    return [
        ConceptProposeCandidate(ir=concept, check_report=report, rank=rank)
        for rank, (_, _, concept, report) in enumerate(scored)
    ]


def _resolve_diff_runs(
    *,
    inline_runs: list[ValidatorRunInput] | None,
    recompute_fn: Callable[[], tuple[CheckReport, list[ValidatorRunRecord]]],
) -> tuple[list[ValidatorRunInput] | list[ValidatorRunRecord], str]:
    if inline_runs is not None:
        return inline_runs, "provided"
    try:
        _, runs = recompute_fn()
        return runs, "recomputed"
    except Exception:
        return [], "recomputed_error"


def _diff_run_source(left_source: str, right_source: str) -> str:
    if left_source == "provided" and right_source == "provided":
        return "provided"
    if left_source.startswith("recomputed") and right_source.startswith("recomputed"):
        return "recomputed"
    return "mixed"


def _extract_backend_timeout(
    runs: list[ValidatorRunInput] | list[ValidatorRunRecord],
) -> tuple[str | None, int | None]:
    if not runs:
        return None, None

    run = runs[0]
    if isinstance(run, ValidatorRunRecord):
        return run.result.backend, run.result.timeout_ms
    if isinstance(run, ValidatorRunInput):
        return run.backend, run.timeout_ms

    return None, None


def _runs_to_inputs(
    runs: list[ValidatorRunInput] | list[ValidatorRunRecord],
) -> list[ValidatorRunInput]:
    if not runs:
        return []
    first = runs[0]
    if isinstance(first, ValidatorRunInput):
        return [_normalize_validator_run_input(run) for run in runs]
    return [_validator_run_input_from_record(run) for run in runs]


def _resolve_concepts_analyze_runs(
    req: ConceptAnalyzeRequest,
) -> tuple[CheckReport, list[ConceptRunRef], list[ValidatorRunInput], list[ValidatorRunRecord]]:
    if req.validator_runs is not None:
        normalized_runs = [_normalize_validator_run_input(run) for run in req.validator_runs]
        concept_runs = [_concept_run_ref_from_input(run) for run in normalized_runs]
        selected = pick_latest_run(concept_runs)
        report = check_concept_with_solver_status(
            req.ir,
            mode=req.mode,
            source_text=req.source_text,
            solver_status=selected.status if selected is not None else None,
            solver_error=selected.evidence_error if selected is not None else None,
            solver_unsat_core=selected.evidence_unsat_core if selected is not None else None,
        )
        return report, concept_runs, normalized_runs, []

    report, records = check_concept_with_validator_runs(
        req.ir,
        mode=req.mode,
        source_text=req.source_text,
    )
    run_inputs = [_validator_run_input_from_record(record) for record in records]
    concept_runs = [_concept_run_ref_from_input(run) for run in run_inputs]
    return report, concept_runs, run_inputs, records


def _build_diff_report_with_runs(
    *,
    left_ir: Any,
    right_ir: Any,
    left_id: str,
    right_id: str,
    mode: KernelMode,
    left_inline_runs: list[ValidatorRunInput] | None,
    right_inline_runs: list[ValidatorRunInput] | None,
    left_recompute_fn: Callable[[], tuple[CheckReport, list[ValidatorRunRecord]]],
    right_recompute_fn: Callable[[], tuple[CheckReport, list[ValidatorRunRecord]]],
) -> DiffReport:
    left_runs, left_source = _resolve_diff_runs(
        inline_runs=left_inline_runs,
        recompute_fn=left_recompute_fn,
    )
    right_runs, right_source = _resolve_diff_runs(
        inline_runs=right_inline_runs,
        recompute_fn=right_recompute_fn,
    )
    left_backend, left_timeout_ms = _extract_backend_timeout(left_runs)
    right_backend, right_timeout_ms = _extract_backend_timeout(right_runs)
    return build_diff_report(
        left_ir,
        right_ir,
        left_id=left_id,
        right_id=right_id,
        left_runs=left_runs,
        right_runs=right_runs,
        summary_run_source=_diff_run_source(left_source, right_source),
        summary_recompute_mode=mode.value,
        summary_left_backend=left_backend,
        summary_right_backend=right_backend,
        summary_left_timeout_ms=left_timeout_ms,
        summary_right_timeout_ms=right_timeout_ms,
    )


def _latest_run_input(runs: list[ValidatorRunInput]) -> ValidatorRunInput | None:
    if not runs:
        return None
    latest = runs[-1]
    latest_key = _run_sort_key_for_input(latest, fallback_index=len(runs) - 1)
    for idx, run in enumerate(runs):
        key = _run_sort_key_for_input(run, fallback_index=idx)
        if key > latest_key:
            latest = run
            latest_key = key
    return latest


def _run_sort_key_for_input(
    run: ValidatorRunInput,
    *,
    fallback_index: int,
) -> tuple[int, datetime, int]:
    created_at = run.created_at
    parsed = None
    if isinstance(created_at, str):
        text = created_at.replace("Z", "+00:00")
        try:
            parsed = datetime.fromisoformat(text)
        except ValueError:
            parsed = None
    if parsed is None:
        return (0, datetime.min.replace(tzinfo=timezone.utc), fallback_index)
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return (1, parsed, fallback_index)


def _run_hash_pair(run: ValidatorRunInput | None) -> tuple[str | None, str | None]:
    if run is None:
        return None, None
    return run.request_hash, run.formula_hash


def _run_hash_mismatch(
    *,
    inline_runs: list[ValidatorRunInput] | None,
    recomputed_records: list[ValidatorRunRecord],
) -> bool:
    if inline_runs is None:
        return False
    normalized_inline = [_normalize_validator_run_input(run) for run in inline_runs]
    recomputed_inputs = [_validator_run_input_from_record(record) for record in recomputed_records]
    inline_latest = _latest_run_input(normalized_inline)
    recomputed_latest = _latest_run_input(recomputed_inputs)
    inline_pair = _run_hash_pair(inline_latest)
    recomputed_pair = _run_hash_pair(recomputed_latest)
    if not inline_pair[0] or not inline_pair[1]:
        return False
    if not recomputed_pair[0] or not recomputed_pair[1]:
        return False
    return inline_pair != recomputed_pair


def _resolve_explain_runs(
    *,
    inline_runs: list[ValidatorRunInput] | None,
    recompute_fn: Callable[[], tuple[CheckReport, list[ValidatorRunRecord]]],
) -> tuple[
    list[ValidatorRunInput] | list[ValidatorRunRecord],
    str,
    CheckReport | None,
    bool,
    list[ValidatorRunInput],
]:
    if inline_runs is None:
        try:
            report, records = recompute_fn()
            recomputed_inputs = [_validator_run_input_from_record(record) for record in records]
            return records, "recomputed", report, False, recomputed_inputs
        except Exception:
            return [], "recomputed_error", None, False, []

    normalized_inline = [_normalize_validator_run_input(run) for run in inline_runs]
    mismatch = False
    report: CheckReport | None = None
    recomputed_inputs: list[ValidatorRunInput] = []
    try:
        recomputed_report, recomputed_records = recompute_fn()
        report = recomputed_report
        recomputed_inputs = [
            _validator_run_input_from_record(record) for record in recomputed_records
        ]
        mismatch = _run_hash_mismatch(
            inline_runs=normalized_inline,
            recomputed_records=recomputed_records,
        )
    except Exception:
        pass
    return normalized_inline, "provided", report, mismatch, recomputed_inputs


def _edge_key(
    src_sense_id: str,
    dst_sense_id: str,
    kind: str,
) -> tuple[str, str, str]:
    return (src_sense_id, dst_sense_id, kind)


def _check_status_value(report: CheckReport | None) -> str:
    if report is None:
        return "REFUSE"
    return report.status


def _build_concept_analysis_delta(
    left_analysis: ConceptAnalysis,
    right_analysis: ConceptAnalysis,
) -> ConceptAnalysisDelta:
    left_mic_atoms = {constraint.atom_name for constraint in left_analysis.mic.constraints}
    right_mic_atoms = {constraint.atom_name for constraint in right_analysis.mic.constraints}
    mic_available = (
        left_analysis.mic.status != "UNAVAILABLE" and right_analysis.mic.status != "UNAVAILABLE"
    )

    left_forced_edges = {
        _edge_key(edge.src_sense_id, edge.dst_sense_id, edge.kind)
        for edge in left_analysis.forced.forced_edges
    }
    right_forced_edges = {
        _edge_key(edge.src_sense_id, edge.dst_sense_id, edge.kind)
        for edge in right_analysis.forced.forced_edges
    }
    forced_available = (
        left_analysis.forced.status != "UNAVAILABLE"
        and right_analysis.forced.status != "UNAVAILABLE"
    )

    left_countermodels = {
        _edge_key(model.src_sense_id, model.dst_sense_id, model.kind): model.solver_status
        for model in left_analysis.forced.countermodels
    }
    right_countermodels = {
        _edge_key(model.src_sense_id, model.dst_sense_id, model.kind): model.solver_status
        for model in right_analysis.forced.countermodels
    }
    changed_countermodel_keys = sorted(
        key
        for key in set(left_countermodels) | set(right_countermodels)
        if left_countermodels.get(key) != right_countermodels.get(key)
    )

    return ConceptAnalysisDelta(
        mic_delta_status=None if mic_available else "UNAVAILABLE_SIDE",
        forced_delta_status=None if forced_available else "UNAVAILABLE_SIDE",
        mic_atoms_added=sorted(right_mic_atoms - left_mic_atoms) if mic_available else [],
        mic_atoms_removed=sorted(left_mic_atoms - right_mic_atoms) if mic_available else [],
        forced_edges_added=[
            ForcedEdgeKey(src_sense_id=src, dst_sense_id=dst, kind=kind)
            for src, dst, kind in sorted(right_forced_edges - left_forced_edges)
        ]
        if forced_available
        else [],
        forced_edges_removed=[
            ForcedEdgeKey(src_sense_id=src, dst_sense_id=dst, kind=kind)
            for src, dst, kind in sorted(left_forced_edges - right_forced_edges)
        ]
        if forced_available
        else [],
        countermodel_edges_changed=[
            ForcedEdgeKey(src_sense_id=src, dst_sense_id=dst, kind=kind)
            for src, dst, kind in changed_countermodel_keys
        ]
        if forced_available
        else [],
    )


@app.post("/propose", response_model=ProposeResponse)
def propose(req: ProposeRequest) -> ProposeResponse:
    bundles = load_fixture_bundles()
    clause = req.clause_text.strip()
    bundle = bundles.get(clause)
    features = extract_source_features(clause)

    base_context: Context
    if req.context is not None:
        base_context = req.context
    elif bundle is not None and bundle.proposals:
        base_context = bundle.proposals[0].context
    else:
        base_context = Context(
            doc_id="api:adhoc",
            jurisdiction="US-CA",
            time_eval=datetime.now(tz=timezone.utc),
        )

    context = base_context.model_copy(update={"source_features": features})
    if req.provider == "openai":
        from .openai_provider import propose_openai

        try:
            proposed, openai_log, model = propose_openai(
                clause_text=clause,
                context=context,
                mode=req.mode,
                max_candidates=req.max_candidates,
                max_repairs=req.max_repairs,
            )
        except RuntimeError as exc:
            raise HTTPException(status_code=400, detail=str(exc)) from exc

        candidates = _score_and_rank_proposals(proposed)
        rank_by_ir_id = {candidate.ir.ir_id: candidate.rank for candidate in candidates}
        return ProposeResponse(
            provider=ProviderInfo(kind="openai", api=openai_log.api, model=model),
            candidates=candidates,
            proposer_log=ProposerLog(
                provider=openai_log.provider,
                api=openai_log.api,
                model=openai_log.model,
                created_at=openai_log.created_at,
                k=openai_log.k,
                n=openai_log.n,
                source_features=features.model_dump(mode="json"),
                attempts=[
                    ProposerAttempt(
                        attempt_idx=a.attempt_idx,
                        status=a.status,
                        reason_codes_summary=a.reason_codes_summary,
                        score_key=a.score_key,
                        accepted_by_gate=a.accepted_by_gate,
                        candidate_rank=rank_by_ir_id.get(a.candidate_ir_id),
                    )
                    for a in openai_log.attempts
                ],
                prompt_hash=openai_log.prompt_hash,
                response_hash=openai_log.response_hash,
                raw_prompt=openai_log.raw_prompt,
                raw_response=openai_log.raw_response,
            ),
        )

    if bundle is None:
        return ProposeResponse(
            provider=ProviderInfo(kind="mock", api="mock"),
            candidates=[],
            proposer_log=ProposerLog(
                provider="mock",
                api="mock",
                created_at=datetime.now(tz=timezone.utc).isoformat(),
                k=0,
                n=0,
                source_features=features.model_dump(mode="json"),
            ),
        )

    scored: list[tuple[AdeuIR, CheckReport]] = []
    for ir in bundle.proposals:
        ir_with_features = ir.model_copy(update={"context": context})
        report = check(ir_with_features, mode=req.mode)
        scored.append((ir_with_features, report))

    candidates = _score_and_rank_proposals(scored)
    return ProposeResponse(
        provider=ProviderInfo(kind="mock", api="mock"),
        candidates=candidates,
        proposer_log=ProposerLog(
            provider="mock",
            api="mock",
            created_at=datetime.now(tz=timezone.utc).isoformat(),
            k=len(candidates),
            n=0,
            source_features=features.model_dump(mode="json"),
            attempts=[
                ProposerAttempt(
                    attempt_idx=idx,
                    status=c.check_report.status,
                    reason_codes_summary=sorted({r.code for r in c.check_report.reason_codes}),
                    score_key=score_key(c.check_report),
                    accepted_by_gate=True,
                    candidate_rank=c.rank,
                )
                for idx, c in enumerate(candidates)
            ],
        ),
    )


@app.post("/check", response_model=CheckReport)
def check_variant(req: CheckRequest) -> CheckReport:
    report, runs = check_with_validator_runs(req.ir, mode=req.mode)
    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS") and runs:
        _persist_validator_runs(runs=runs, artifact_id=None)
    return report


@app.post("/puzzles/check", response_model=CheckReport)
def check_puzzle_variant(req: PuzzleCheckRequest) -> CheckReport:
    report, runs = check_puzzle_with_validator_runs(req.puzzle, mode=req.mode)
    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS") and runs:
        _persist_validator_runs(runs=runs, artifact_id=None)
    return report


@app.post("/concepts/check", response_model=CheckReport)
def check_concept_variant(req: ConceptCheckRequest) -> CheckReport:
    if req.source_text is not None:
        _enforce_source_text_size(req.source_text)
    report, runs = check_concept_with_validator_runs(
        req.ir,
        mode=req.mode,
        source_text=req.source_text,
    )
    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS") and runs:
        _persist_validator_runs(runs=runs, artifact_id=None)
    return report


@app.post("/concepts/analyze", response_model=ConceptAnalyzeResponse)
def analyze_concept_variant(req: ConceptAnalyzeRequest) -> ConceptAnalyzeResponse:
    if req.source_text is not None:
        _enforce_source_text_size(req.source_text)
    report, concept_runs, run_inputs, recomputed_records = _resolve_concepts_analyze_runs(req)
    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS") and recomputed_records:
        _persist_validator_runs(runs=recomputed_records, artifact_id=None)

    selected = pick_latest_run(concept_runs)
    analysis = analyze_concept(req.ir, run=selected)
    if not req.include_analysis_details:
        analysis = strip_analysis_details(analysis)
    elif not req.include_forced_details:
        analysis = strip_forced_details(analysis)

    return ConceptAnalyzeResponse(
        ir=req.ir,
        check_report=report,
        analysis=analysis,
        validator_runs=run_inputs if req.include_validator_runs else None,
    )


@app.post("/puzzles/propose", response_model=PuzzleProposeResponse)
def propose_puzzle(req: PuzzleProposeRequest) -> PuzzleProposeResponse:
    puzzle_text = req.puzzle_text.strip()
    source_features = extract_puzzle_source_features(puzzle_text)

    if req.provider == "openai":
        from .openai_puzzle_provider import propose_puzzle_openai

        try:
            proposed, puzzle_log, model = propose_puzzle_openai(
                puzzle_text=puzzle_text,
                mode=req.mode,
                max_candidates=req.max_candidates,
                max_repairs=req.max_repairs,
                source_features=source_features,
                context_override=req.context_override,
            )
        except RuntimeError as exc:
            raise HTTPException(status_code=400, detail=str(exc)) from exc

        if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS"):
            for _, _, runs in proposed:
                if runs:
                    _persist_validator_runs(runs=runs, artifact_id=None)

        candidates = _score_and_rank_puzzle_proposals(
            [(puzzle, report) for puzzle, report, _ in proposed]
        )
        rank_by_puzzle_id = {candidate.ir.puzzle_id: candidate.rank for candidate in candidates}
        return PuzzleProposeResponse(
            provider=ProviderInfo(kind="openai", api=puzzle_log.api, model=model),
            candidates=candidates,
            proposer_log=ProposerLog(
                provider=puzzle_log.provider,
                api=puzzle_log.api,
                model=puzzle_log.model,
                created_at=puzzle_log.created_at,
                k=puzzle_log.k,
                n=puzzle_log.n,
                source_features=puzzle_log.source_features,
                attempts=[
                    ProposerAttempt(
                        attempt_idx=attempt.attempt_idx,
                        status=attempt.status,
                        reason_codes_summary=attempt.reason_codes_summary,
                        score_key=attempt.score_key,
                        accepted_by_gate=attempt.accepted_by_gate,
                        candidate_rank=(
                            rank_by_puzzle_id.get(attempt.candidate_puzzle_id)
                            if attempt.candidate_puzzle_id
                            else None
                        ),
                    )
                    for attempt in puzzle_log.attempts
                ],
                prompt_hash=puzzle_log.prompt_hash,
                response_hash=puzzle_log.response_hash,
                raw_prompt=puzzle_log.raw_prompt,
                raw_response=puzzle_log.raw_response,
            ),
        )

    bundle = get_puzzle_fixture_bundle(puzzle_text)
    if bundle is None:
        return PuzzleProposeResponse(
            provider=ProviderInfo(kind="mock", api="mock"),
            candidates=[],
            proposer_log=ProposerLog(
                provider="mock",
                api="mock",
                created_at=datetime.now(tz=timezone.utc).isoformat(),
                k=0,
                n=0,
                source_features=source_features,
            ),
        )

    checked: list[tuple[KnightsKnavesPuzzle, CheckReport]] = []
    checked_runs: list[list[ValidatorRunRecord]] = []
    for proposal in bundle.proposals:
        puzzle = canonicalize_puzzle_ids(proposal)
        report, runs = check_puzzle_with_validator_runs(puzzle, mode=req.mode)
        checked.append((puzzle, report))
        checked_runs.append(runs)

    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS"):
        for runs in checked_runs:
            if runs:
                _persist_validator_runs(runs=runs, artifact_id=None)

    candidates = _score_and_rank_puzzle_proposals(checked)
    return PuzzleProposeResponse(
        provider=ProviderInfo(kind="mock", api="mock"),
        candidates=candidates,
        proposer_log=ProposerLog(
            provider="mock",
            api="mock",
            created_at=datetime.now(tz=timezone.utc).isoformat(),
            k=len(candidates),
            n=0,
            source_features=source_features,
            attempts=[
                ProposerAttempt(
                    attempt_idx=idx,
                    status=candidate.check_report.status,
                    reason_codes_summary=sorted(
                        {reason.code for reason in candidate.check_report.reason_codes}
                    ),
                    score_key=score_key(candidate.check_report),
                    accepted_by_gate=True,
                    candidate_rank=candidate.rank,
                )
                for idx, candidate in enumerate(candidates)
            ],
        ),
    )


@app.post("/concepts/propose", response_model=ConceptProposeResponse)
def propose_concept(req: ConceptProposeRequest) -> ConceptProposeResponse:
    source_text = req.source_text.strip()
    _enforce_source_text_size(source_text)
    source_features = extract_concept_source_features(source_text)

    if req.provider == "openai":
        try:
            proposed, concept_log, model = propose_concept_openai(
                source_text=source_text,
                mode=req.mode,
                max_candidates=req.max_candidates,
                max_repairs=req.max_repairs,
                source_features=source_features,
            )
        except RuntimeError as exc:
            raise HTTPException(status_code=400, detail=str(exc)) from exc

        if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS"):
            for _, _, runs in proposed:
                if runs:
                    _persist_validator_runs(runs=runs, artifact_id=None)

        candidates = _score_and_rank_concept_proposals(
            [(concept, report) for concept, report, _ in proposed]
        )
        rank_by_concept_id = {candidate.ir.concept_id: candidate.rank for candidate in candidates}
        return ConceptProposeResponse(
            provider=ProviderInfo(kind="openai", api=concept_log.api, model=model),
            candidates=candidates,
            proposer_log=ProposerLog(
                provider=concept_log.provider,
                api=concept_log.api,
                model=concept_log.model,
                created_at=concept_log.created_at,
                k=concept_log.k,
                n=concept_log.n,
                source_features=concept_log.source_features,
                attempts=[
                    ProposerAttempt(
                        attempt_idx=attempt.attempt_idx,
                        status=attempt.status,
                        reason_codes_summary=attempt.reason_codes_summary,
                        score_key=attempt.score_key,
                        accepted_by_gate=attempt.accepted_by_gate,
                        candidate_rank=(
                            rank_by_concept_id.get(attempt.candidate_concept_id)
                            if attempt.candidate_concept_id
                            else None
                        ),
                    )
                    for attempt in concept_log.attempts
                ],
                prompt_hash=concept_log.prompt_hash,
                response_hash=concept_log.response_hash,
                raw_prompt=concept_log.raw_prompt,
                raw_response=concept_log.raw_response,
            ),
        )

    bundle = get_concept_fixture_bundle(source_text)
    if bundle is None:
        return ConceptProposeResponse(
            provider=ProviderInfo(kind="mock", api="mock"),
            candidates=[],
            proposer_log=ProposerLog(
                provider="mock",
                api="mock",
                created_at=datetime.now(tz=timezone.utc).isoformat(),
                k=0,
                n=0,
                source_features=source_features,
            ),
        )

    checked: list[tuple[ConceptIR, CheckReport]] = []
    checked_runs: list[list[ValidatorRunRecord]] = []
    for proposal in bundle.proposals:
        concept = canonicalize_concept_ids(proposal)
        report, runs = check_concept_with_validator_runs(
            concept,
            mode=req.mode,
            source_text=source_text,
        )
        checked.append((concept, report))
        checked_runs.append(runs)

    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS"):
        for runs in checked_runs:
            if runs:
                _persist_validator_runs(runs=runs, artifact_id=None)

    candidates = _score_and_rank_concept_proposals(checked)
    return ConceptProposeResponse(
        provider=ProviderInfo(kind="mock", api="mock"),
        candidates=candidates,
        proposer_log=ProposerLog(
            provider="mock",
            api="mock",
            created_at=datetime.now(tz=timezone.utc).isoformat(),
            k=len(candidates),
            n=0,
            source_features=source_features,
            attempts=[
                ProposerAttempt(
                    attempt_idx=idx,
                    status=candidate.check_report.status,
                    reason_codes_summary=sorted(
                        {reason.code for reason in candidate.check_report.reason_codes}
                    ),
                    score_key=score_key(candidate.check_report),
                    accepted_by_gate=True,
                    candidate_rank=candidate.rank,
                )
                for idx, candidate in enumerate(candidates)
            ],
        ),
    )


@app.post("/concepts/artifacts", response_model=ConceptArtifactCreateResponse)
def create_concept_artifact_endpoint(
    req: ConceptArtifactCreateRequest,
) -> ConceptArtifactCreateResponse:
    _enforce_source_text_size(req.source_text)
    report, runs = check_concept_with_validator_runs(
        req.ir,
        mode=req.mode,
        source_text=req.source_text,
    )
    if report.status == "REFUSE":
        raise HTTPException(status_code=400, detail="refused by kernel")

    num_errors = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.ERROR)
    num_warns = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.WARN)
    run_inputs = [_validator_run_input_from_record(record) for record in runs]
    concept_runs = [_concept_run_ref_from_input(run) for run in run_inputs]
    selected = pick_latest_run(concept_runs)
    analysis = analyze_concept(req.ir, run=selected) if selected is not None else None

    row = create_concept_artifact(
        schema_version=req.ir.schema_version,
        artifact_version=1,
        source_text=req.source_text,
        doc_id=req.ir.context.doc_id,
        status=report.status,
        num_errors=num_errors,
        num_warns=num_warns,
        ir_json=req.ir.model_dump(mode="json", exclude_none=True),
        check_report_json=report.model_dump(mode="json", exclude_none=True),
        analysis_json=analysis.model_dump(mode="json", exclude_none=True) if analysis else None,
    )
    if runs:
        _persist_validator_runs(
            runs=runs,
            artifact_id=None,
            concept_artifact_id=row.artifact_id,
        )
    return ConceptArtifactCreateResponse(
        artifact_id=row.artifact_id,
        created_at=row.created_at,
        check_report=report,
        analysis=analysis,
    )


@app.get("/concepts/artifacts", response_model=ConceptArtifactListResponse)
def list_concept_artifacts_endpoint(
    doc_id: str | None = None,
    status: Literal["PASS", "WARN", "REFUSE"] | None = None,
    created_after: str | None = None,
    created_before: str | None = None,
    limit: int = Query(50, ge=1, le=200),
    offset: int = Query(0, ge=0, le=50_000),
) -> ConceptArtifactListResponse:
    try:
        rows = list_concept_artifacts(
            doc_id=doc_id,
            status=status,
            created_after=created_after,
            created_before=created_before,
            limit=limit,
            offset=offset,
        )
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return ConceptArtifactListResponse(
        items=[
            ConceptArtifactSummary(
                artifact_id=row.artifact_id,
                created_at=row.created_at,
                doc_id=row.doc_id,
                status=row.status,
                num_errors=row.num_errors,
                num_warns=row.num_warns,
            )
            for row in rows
        ]
    )


@app.get("/concepts/artifacts/{artifact_id}", response_model=ConceptArtifactGetResponse)
def get_concept_artifact_endpoint(artifact_id: str) -> ConceptArtifactGetResponse:
    row = get_concept_artifact(artifact_id=artifact_id)
    if row is None:
        raise HTTPException(status_code=404, detail="not found")
    analysis = ConceptAnalysis.model_validate(row.analysis_json) if row.analysis_json else None
    return ConceptArtifactGetResponse(
        artifact_id=row.artifact_id,
        created_at=row.created_at,
        schema_version=row.schema_version,
        artifact_version=row.artifact_version,
        source_text=row.source_text,
        ir=ConceptIR.model_validate(row.ir_json),
        check_report=CheckReport.model_validate(row.check_report_json),
        analysis=analysis,
    )


@app.get(
    "/concepts/artifacts/{artifact_id}/validator-runs",
    response_model=ArtifactValidatorRunsResponse,
)
def list_concept_artifact_validator_runs_endpoint(
    artifact_id: str,
) -> ArtifactValidatorRunsResponse:
    row = get_concept_artifact(artifact_id=artifact_id)
    if row is None:
        raise HTTPException(status_code=404, detail="not found")

    rows = list_concept_validator_runs(concept_artifact_id=artifact_id)
    return ArtifactValidatorRunsResponse(
        items=[
            StoredValidatorRun(
                run_id=run.run_id,
                artifact_id=run.artifact_id,
                concept_artifact_id=run.concept_artifact_id,
                created_at=run.created_at,
                backend=run.backend,
                backend_version=run.backend_version,
                timeout_ms=run.timeout_ms,
                options_json=run.options_json,
                request_hash=run.request_hash,
                formula_hash=run.formula_hash,
                status=run.status,
                evidence_json=run.evidence_json,
                atom_map_json=run.atom_map_json,
            )
            for run in rows
        ]
    )


@app.post("/diff", response_model=DiffReport)
def diff_endpoint(req: DiffRequest) -> DiffReport:
    return _build_diff_report_with_runs(
        left_ir=req.left_ir,
        right_ir=req.right_ir,
        left_id=req.left_ir.ir_id,
        right_id=req.right_ir.ir_id,
        mode=req.mode,
        left_inline_runs=req.left_validator_runs,
        right_inline_runs=req.right_validator_runs,
        left_recompute_fn=lambda: check_with_validator_runs(req.left_ir, mode=req.mode),
        right_recompute_fn=lambda: check_with_validator_runs(req.right_ir, mode=req.mode),
    )


@app.post("/concepts/diff", response_model=DiffReport)
def diff_concepts_endpoint(req: ConceptDiffRequest) -> DiffReport:
    return _build_diff_report_with_runs(
        left_ir=req.left_ir,
        right_ir=req.right_ir,
        left_id=req.left_ir.concept_id,
        right_id=req.right_ir.concept_id,
        mode=req.mode,
        left_inline_runs=req.left_validator_runs,
        right_inline_runs=req.right_validator_runs,
        left_recompute_fn=lambda: check_concept_with_validator_runs(
            req.left_ir,
            mode=req.mode,
            source_text=req.left_source_text,
        ),
        right_recompute_fn=lambda: check_concept_with_validator_runs(
            req.right_ir,
            mode=req.mode,
            source_text=req.right_source_text,
        ),
    )


@app.post("/puzzles/diff", response_model=DiffReport)
def diff_puzzles_endpoint(req: PuzzleDiffRequest) -> DiffReport:
    return _build_diff_report_with_runs(
        left_ir=req.left_ir,
        right_ir=req.right_ir,
        left_id=req.left_ir.puzzle_id,
        right_id=req.right_ir.puzzle_id,
        mode=req.mode,
        left_inline_runs=req.left_validator_runs,
        right_inline_runs=req.right_validator_runs,
        left_recompute_fn=lambda: check_puzzle_with_validator_runs(req.left_ir, mode=req.mode),
        right_recompute_fn=lambda: check_puzzle_with_validator_runs(req.right_ir, mode=req.mode),
    )


@app.post("/explain_flip", response_model=ExplainFlipResponse)
def explain_flip_endpoint(req: ExplainFlipRequest) -> ExplainFlipResponse:
    if isinstance(req, ExplainFlipAdeuRequest):
        left_runs, left_source, left_report, left_mismatch, _ = _resolve_explain_runs(
            inline_runs=req.left_validator_runs,
            recompute_fn=lambda: check_with_validator_runs(req.left_ir, mode=req.mode),
        )
        right_runs, right_source, right_report, right_mismatch, _ = _resolve_explain_runs(
            inline_runs=req.right_validator_runs,
            recompute_fn=lambda: check_with_validator_runs(req.right_ir, mode=req.mode),
        )
        if left_report is None:
            try:
                left_report = check(req.left_ir, mode=req.mode)
            except Exception:
                left_report = None
        if right_report is None:
            try:
                right_report = check(req.right_ir, mode=req.mode)
            except Exception:
                right_report = None

        left_backend, left_timeout_ms = _extract_backend_timeout(left_runs)
        right_backend, right_timeout_ms = _extract_backend_timeout(right_runs)
        diff_report = build_diff_report(
            req.left_ir,
            req.right_ir,
            left_id=req.left_ir.ir_id,
            right_id=req.right_ir.ir_id,
            left_runs=left_runs,
            right_runs=right_runs,
            summary_run_source=_diff_run_source(left_source, right_source),
            summary_recompute_mode=req.mode.value,
            summary_left_backend=left_backend,
            summary_right_backend=right_backend,
            summary_left_timeout_ms=left_timeout_ms,
            summary_right_timeout_ms=right_timeout_ms,
        )
        flip_explanation = build_flip_explanation(
            req.left_ir,
            req.right_ir,
            diff_report=diff_report,
            left_check_status=_check_status_value(left_report),
            right_check_status=_check_status_value(right_report),
        )
        return ExplainFlipResponse(
            diff_report=diff_report,
            flip_explanation=flip_explanation,
            analysis_delta=None,
            left_mismatch=left_mismatch,
            right_mismatch=right_mismatch,
            run_ir_mismatch=(left_mismatch or right_mismatch),
        )

    if isinstance(req, ExplainFlipPuzzlesRequest):
        left_runs, left_source, left_report, left_mismatch, _ = _resolve_explain_runs(
            inline_runs=req.left_validator_runs,
            recompute_fn=lambda: check_puzzle_with_validator_runs(req.left_ir, mode=req.mode),
        )
        right_runs, right_source, right_report, right_mismatch, _ = _resolve_explain_runs(
            inline_runs=req.right_validator_runs,
            recompute_fn=lambda: check_puzzle_with_validator_runs(req.right_ir, mode=req.mode),
        )
        if left_report is None:
            try:
                left_report = check_puzzle_with_validator_runs(req.left_ir, mode=req.mode)[0]
            except Exception:
                left_report = None
        if right_report is None:
            try:
                right_report = check_puzzle_with_validator_runs(req.right_ir, mode=req.mode)[0]
            except Exception:
                right_report = None

        left_backend, left_timeout_ms = _extract_backend_timeout(left_runs)
        right_backend, right_timeout_ms = _extract_backend_timeout(right_runs)
        diff_report = build_diff_report(
            req.left_ir,
            req.right_ir,
            left_id=req.left_ir.puzzle_id,
            right_id=req.right_ir.puzzle_id,
            left_runs=left_runs,
            right_runs=right_runs,
            summary_run_source=_diff_run_source(left_source, right_source),
            summary_recompute_mode=req.mode.value,
            summary_left_backend=left_backend,
            summary_right_backend=right_backend,
            summary_left_timeout_ms=left_timeout_ms,
            summary_right_timeout_ms=right_timeout_ms,
        )
        flip_explanation = build_flip_explanation(
            req.left_ir,
            req.right_ir,
            diff_report=diff_report,
            left_check_status=_check_status_value(left_report),
            right_check_status=_check_status_value(right_report),
        )
        return ExplainFlipResponse(
            diff_report=diff_report,
            flip_explanation=flip_explanation,
            analysis_delta=None,
            left_mismatch=left_mismatch,
            right_mismatch=right_mismatch,
            run_ir_mismatch=(left_mismatch or right_mismatch),
        )

    left_runs, left_source, left_report, left_mismatch, _ = _resolve_explain_runs(
        inline_runs=req.left_validator_runs,
        recompute_fn=lambda: check_concept_with_validator_runs(
            req.left_ir,
            mode=req.mode,
            source_text=req.left_source_text,
        ),
    )
    right_runs, right_source, right_report, right_mismatch, _ = _resolve_explain_runs(
        inline_runs=req.right_validator_runs,
        recompute_fn=lambda: check_concept_with_validator_runs(
            req.right_ir,
            mode=req.mode,
            source_text=req.right_source_text,
        ),
    )

    left_inputs = _runs_to_inputs(left_runs)
    right_inputs = _runs_to_inputs(right_runs)
    left_selected = pick_latest_run([_concept_run_ref_from_input(run) for run in left_inputs])
    right_selected = pick_latest_run([_concept_run_ref_from_input(run) for run in right_inputs])

    if req.left_validator_runs is not None:
        left_report = check_concept_with_solver_status(
            req.left_ir,
            mode=req.mode,
            source_text=req.left_source_text,
            solver_status=left_selected.status if left_selected is not None else None,
            solver_error=left_selected.evidence_error if left_selected is not None else None,
            solver_unsat_core=(
                left_selected.evidence_unsat_core if left_selected is not None else None
            ),
        )
    elif left_report is None:
        left_report = check_concept_with_solver_status(
            req.left_ir,
            mode=req.mode,
            source_text=req.left_source_text,
            solver_status=None,
            solver_error=None,
            solver_unsat_core=None,
        )

    if req.right_validator_runs is not None:
        right_report = check_concept_with_solver_status(
            req.right_ir,
            mode=req.mode,
            source_text=req.right_source_text,
            solver_status=right_selected.status if right_selected is not None else None,
            solver_error=right_selected.evidence_error if right_selected is not None else None,
            solver_unsat_core=(
                right_selected.evidence_unsat_core if right_selected is not None else None
            ),
        )
    elif right_report is None:
        right_report = check_concept_with_solver_status(
            req.right_ir,
            mode=req.mode,
            source_text=req.right_source_text,
            solver_status=None,
            solver_error=None,
            solver_unsat_core=None,
        )

    left_backend, left_timeout_ms = _extract_backend_timeout(left_runs)
    right_backend, right_timeout_ms = _extract_backend_timeout(right_runs)
    diff_report = build_diff_report(
        req.left_ir,
        req.right_ir,
        left_id=req.left_ir.concept_id,
        right_id=req.right_ir.concept_id,
        left_runs=left_runs,
        right_runs=right_runs,
        summary_run_source=_diff_run_source(left_source, right_source),
        summary_recompute_mode=req.mode.value,
        summary_left_backend=left_backend,
        summary_right_backend=right_backend,
        summary_left_timeout_ms=left_timeout_ms,
        summary_right_timeout_ms=right_timeout_ms,
    )
    flip_explanation = build_flip_explanation(
        req.left_ir,
        req.right_ir,
        diff_report=diff_report,
        left_check_status=_check_status_value(left_report),
        right_check_status=_check_status_value(right_report),
    )

    analysis_delta: ConceptAnalysisDelta | None = None
    if req.include_analysis_delta:
        budget = (
            req.additional_solver_call_budget
            if req.additional_solver_call_budget is not None
            else 40
        )
        left_budget = budget // 2
        right_budget = budget - left_budget
        left_analysis = analyze_concept(
            req.left_ir,
            run=left_selected,
            max_solver_calls_total=1 + max(0, left_budget),
        )
        right_analysis = analyze_concept(
            req.right_ir,
            run=right_selected,
            max_solver_calls_total=1 + max(0, right_budget),
        )
        if not req.include_forced_details:
            left_analysis = strip_forced_details(left_analysis)
            right_analysis = strip_forced_details(right_analysis)
        analysis_delta = _build_concept_analysis_delta(left_analysis, right_analysis)

    return ExplainFlipResponse(
        diff_report=diff_report,
        flip_explanation=flip_explanation,
        analysis_delta=analysis_delta,
        left_mismatch=left_mismatch,
        right_mismatch=right_mismatch,
        run_ir_mismatch=(left_mismatch or right_mismatch),
    )


@app.post("/puzzles/solve", response_model=PuzzleSolveResult)
def solve_puzzle_endpoint(req: PuzzleSolveRequest) -> PuzzleSolveResult:
    try:
        backend = build_validator_backend(req.backend)
    except RuntimeError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return solve_knights_knaves(req.puzzle, validator_backend=backend)


@app.post("/apply_ambiguity_option", response_model=ApplyAmbiguityOptionResponse)
def apply_ambiguity_option_endpoint(
    req: ApplyAmbiguityOptionRequest,
) -> ApplyAmbiguityOptionResponse:
    try:
        patched = apply_ambiguity_option(
            req.ir,
            ambiguity_id=req.ambiguity_id,
            option_id=req.option_id,
            variants_by_id=req.variants_by_id,
        )
    except PatchValidationError as e:
        ir = req.ir
        metrics = ir.calculate_metrics()
        report = CheckReport(
            status="REFUSE",
            reason_codes=[e.reason],
            trace=[
                TraceItem(
                    rule_id="ambiguity/apply_option",
                    because=[e.reason.code],
                    affected_ids=[ir.ir_id],
                )
            ],
            metrics=metrics,
        )
        return ApplyAmbiguityOptionResponse(patched_ir=ir, check_report=report)

    patched = canonicalize_ir_ids(patched)
    report = check(patched, mode=req.mode)
    return ApplyAmbiguityOptionResponse(patched_ir=patched, check_report=report)


@app.post("/artifacts", response_model=ArtifactCreateResponse)
def create_artifact_endpoint(req: ArtifactCreateRequest) -> ArtifactCreateResponse:
    report, runs = check_with_validator_runs(req.ir, mode=req.mode)
    if report.status == "REFUSE":
        raise HTTPException(status_code=400, detail="refused by kernel")

    num_errors = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.ERROR)
    num_warns = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.WARN)

    with storage_transaction() as connection:
        row = create_artifact(
            clause_text=req.clause_text,
            doc_id=req.ir.context.doc_id,
            jurisdiction=req.ir.context.jurisdiction,
            status=report.status,
            num_errors=num_errors,
            num_warns=num_warns,
            ir_json=req.ir.model_dump(mode="json", exclude_none=True),
            check_report_json=report.model_dump(mode="json", exclude_none=True),
            connection=connection,
        )
        if runs:
            _persist_validator_runs(
                runs=runs,
                artifact_id=row.artifact_id,
                connection=connection,
            )
        _persist_proof_artifact(
            artifact_id=row.artifact_id,
            ir=req.ir,
            runs=runs,
            connection=connection,
        )
    return ArtifactCreateResponse(
        artifact_id=row.artifact_id,
        created_at=row.created_at,
        check_report=report,
    )


@app.get("/artifacts", response_model=ArtifactListResponse)
def list_artifacts_endpoint(
    doc_id: str | None = None,
    status: Literal["PASS", "WARN", "REFUSE"] | None = None,
    created_after: str | None = None,
    created_before: str | None = None,
    limit: int = Query(50, ge=1, le=200),
    offset: int = Query(0, ge=0, le=50_000),
) -> ArtifactListResponse:
    try:
        items = list_artifacts(
            doc_id=doc_id,
            status=status,
            created_after=created_after,
            created_before=created_before,
            limit=limit,
            offset=offset,
        )
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return ArtifactListResponse(
        items=[
            ArtifactSummary(
                artifact_id=row.artifact_id,
                created_at=row.created_at,
                doc_id=row.doc_id,
                jurisdiction=row.jurisdiction,
                status=row.status,
                num_errors=row.num_errors,
                num_warns=row.num_warns,
            )
            for row in items
        ]
    )


@app.get("/artifacts/{artifact_id}", response_model=ArtifactGetResponse)
def get_artifact_endpoint(artifact_id: str) -> ArtifactGetResponse:
    row = get_artifact(artifact_id=artifact_id)
    if row is None:
        raise HTTPException(status_code=404, detail="not found")
    return ArtifactGetResponse(
        artifact_id=row.artifact_id,
        created_at=row.created_at,
        clause_text=row.clause_text,
        ir=AdeuIR.model_validate(row.ir_json),
        check_report=CheckReport.model_validate(row.check_report_json),
    )


@app.get("/artifacts/{artifact_id}/proofs", response_model=ArtifactProofListResponse)
def list_artifact_proofs_endpoint(artifact_id: str) -> ArtifactProofListResponse:
    artifact = get_artifact(artifact_id=artifact_id)
    if artifact is None:
        raise HTTPException(status_code=404, detail="not found")

    rows = list_proof_artifacts(artifact_id=artifact_id)
    items = [
        StoredProofArtifact(
            proof=ProofArtifact(
                proof_id=row.proof_id,
                backend=row.backend,  # type: ignore[arg-type]
                theorem_id=row.theorem_id,
                status=row.status,  # type: ignore[arg-type]
                proof_hash=row.proof_hash,
                inputs=[ProofInput.model_validate(item) for item in row.inputs_json],
                details=row.details_json,
            ),
            artifact_id=row.artifact_id,
            created_at=row.created_at,
        )
        for row in rows
    ]
    return ArtifactProofListResponse(items=items)


@app.get("/artifacts/{artifact_id}/validator-runs", response_model=ArtifactValidatorRunsResponse)
def list_artifact_validator_runs_endpoint(artifact_id: str) -> ArtifactValidatorRunsResponse:
    artifact = get_artifact(artifact_id=artifact_id)
    if artifact is None:
        raise HTTPException(status_code=404, detail="not found")

    rows = list_validator_runs(artifact_id=artifact_id)
    return ArtifactValidatorRunsResponse(
        items=[
            StoredValidatorRun(
                run_id=row.run_id,
                artifact_id=row.artifact_id,
                concept_artifact_id=row.concept_artifact_id,
                created_at=row.created_at,
                backend=row.backend,
                backend_version=row.backend_version,
                timeout_ms=row.timeout_ms,
                options_json=row.options_json,
                request_hash=row.request_hash,
                formula_hash=row.formula_hash,
                status=row.status,
                evidence_json=row.evidence_json,
                atom_map_json=row.atom_map_json,
            )
            for row in rows
        ]
    )


@app.get("/healthz")
def healthz() -> dict[str, str]:
    return {"status": "ok"}
