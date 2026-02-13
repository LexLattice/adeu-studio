from __future__ import annotations

import os
import re
import sqlite3
from collections import deque
from datetime import datetime, timezone
from typing import Any, Callable, Literal, NamedTuple

from adeu_concepts import (
    DEFAULT_MAX_ANSWERS_PER_QUESTION,
    DEFAULT_MAX_QUESTIONS,
    AmbiguityOption,
    ConceptAnalysis,
    ConceptIR,
    ConceptPatchValidationError,
    ConceptQuestion,
    ConceptQuestionAnchor,
    ConceptRunRef,
    analyze_concept,
    apply_concept_ambiguity_option,
    apply_concept_json_patch,
    build_concept_questions,
    pick_latest_run,
    strip_analysis_details,
    strip_forced_details,
    unavailable_analysis,
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
    MappingTrust,
    ProofArtifact,
    ProofInput,
    ReasonSeverity,
    TraceItem,
)
from adeu_ir.models import JsonPatchOp
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
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, ConfigDict, Field, model_validator

from .adeu_concept_bridge import (
    BridgeLossReport,
    BridgeManifest,
    build_bridge_loss_report,
    lift_adeu_to_concepts,
)
from .concept_id_canonicalization import canonicalize_concept_ids
from .concept_mock_provider import get_concept_fixture_bundle
from .concept_source_features import extract_concept_source_features
from .hashing import canonical_json, sha256_canonical_json, sha256_text
from .id_canonicalization import canonicalize_ir_ids
from .mock_provider import load_fixture_bundles
from .openai_concept_provider import propose_concept_openai
from .puzzle_id_canonicalization import canonicalize_puzzle_ids
from .puzzle_mock_provider import get_puzzle_fixture_bundle
from .puzzle_source_features import extract_puzzle_source_features
from .scoring import ranking_sort_key, score_key
from .source_features import extract_source_features
from .storage import (
    ProofArtifactRow,
    ValidatorRunRow,
    create_artifact,
    create_concept_artifact,
    create_document,
    create_proof_artifact,
    create_validator_run,
    get_artifact,
    get_concept_artifact,
    get_document,
    list_artifacts,
    list_concept_artifacts,
    list_concept_validator_runs,
    list_documents,
    list_proof_artifacts,
    list_proof_artifacts_for_artifacts,
    list_validator_runs,
    list_validator_runs_for_artifacts,
)
from .storage import (
    transaction as storage_transaction,
)
from .urm_routes import router as urm_router

DEFAULT_LIST_LIMIT = 50
MAX_LIST_LIMIT = 200
MAX_LIST_OFFSET = 50_000
MAX_PROPOSE_CANDIDATES = 20
MAX_PROPOSE_REPAIRS = 10
MAX_ADDITIONAL_SOLVER_CALL_BUDGET = 200
ALIGNMENT_MAX_SUGGESTIONS_MIN = 1
ALIGNMENT_MAX_SUGGESTIONS_MAX = 500
QUESTIONS_BUDGET_VERSION = "budget.v1"
CONCEPTS_QUESTION_RANK_VERSION = "concepts.qrank.v3"
ADEU_QUESTION_RANK_VERSION = "adeu.qrank.v1"
CONCEPTS_RATIONALE_VERSION = "concepts.rationale.v1"
ADEU_RATIONALE_VERSION = "adeu.rationale.v1"
TOURNAMENT_SCORE_VERSION = "concepts.tscore.v2"
QUESTION_TRUNCATION_REASON_DRY_RUN_CAP = "dry_run_cap_reached"
QUESTION_TRUNCATION_REASON_SOLVER_CALL_CAP = "solver_call_cap_reached"
QUESTION_TRUNCATION_REASON_MAX_QUESTIONS = "max_questions_reached"
QUESTION_TRUNCATION_REASON_CANDIDATE_CAP = "candidate_cap_reached"
TOURNAMENT_TIE_BREAK_ORDER = "objective_vector_desc_then_stable_id_asc"
TOURNAMENT_OBJECTIVE_DIMENSIONS: tuple[str, ...] = (
    "status_score",
    "neg_error_count",
    "neg_warn_count",
    "neg_mic_count",
    "neg_countermodel_count",
)
QUESTION_POLARITY_BY_SIGNAL: dict[str, str] = {
    "mic": "resolve_conflict",
    "forced_countermodel": "resolve_nonentailment",
    "disconnected_clusters": "connect_clusters",
}


def _env_int(
    name: str,
    default: int,
    *,
    minimum: int | None = None,
    maximum: int | None = None,
) -> int:
    raw_value = os.environ.get(name, "").strip()
    if not raw_value:
        value = default
    else:
        try:
            value = int(raw_value)
        except ValueError as exc:
            raise RuntimeError(f"{name} must be an integer") from exc

    if minimum is not None and value < minimum:
        raise RuntimeError(f"{name} must be >= {minimum}")
    if maximum is not None and value > maximum:
        raise RuntimeError(f"{name} must be <= {maximum}")
    return value


def _env_csv(name: str) -> list[str]:
    raw_value = os.environ.get(name, "").strip()
    if not raw_value:
        return []
    return [item.strip() for item in raw_value.split(",") if item.strip()]


ALIGNMENT_MAX_SUGGESTIONS_DEFAULT = _env_int(
    "ADEU_ALIGNMENT_MAX_SUGGESTIONS_DEFAULT",
    100,
    minimum=ALIGNMENT_MAX_SUGGESTIONS_MIN,
    maximum=ALIGNMENT_MAX_SUGGESTIONS_MAX,
)
MAX_SOURCE_TEXT_BYTES = _env_int("ADEU_MAX_SOURCE_TEXT_BYTES", 200_000, minimum=1)
MAX_QUESTION_DRY_RUN_EVALS_TOTAL = _env_int(
    "ADEU_MAX_QUESTION_DRY_RUN_EVALS_TOTAL",
    20,
    minimum=1,
)
MAX_QUESTION_SOLVER_CALLS_TOTAL = _env_int(
    "ADEU_MAX_QUESTION_SOLVER_CALLS_TOTAL",
    40,
    minimum=1,
)
MAX_ALIGNMENT_SCOPE_ARTIFACTS = _env_int(
    "ADEU_MAX_ALIGNMENT_SCOPE_ARTIFACTS",
    200,
    minimum=1,
)
DEFAULT_EXPLAIN_ANALYSIS_BUDGET = _env_int(
    "ADEU_EXPLAIN_ANALYSIS_BUDGET_DEFAULT",
    40,
    minimum=0,
    maximum=MAX_ADDITIONAL_SOLVER_CALL_BUDGET,
)
QUESTION_FORCED_BUDGET_MAX = _env_int(
    "ADEU_QUESTION_FORCED_BUDGET_MAX",
    10,
    minimum=1,
)
QUESTION_FORCED_BUDGET_DIVISOR = _env_int(
    "ADEU_QUESTION_FORCED_BUDGET_DIVISOR",
    3,
    minimum=1,
)
QUESTION_MIC_SHRINK_ITERS_MAX = _env_int(
    "ADEU_QUESTION_MIC_SHRINK_ITERS_MAX",
    20,
    minimum=1,
)
MAX_TOURNAMENT_DRY_RUN_EVALS_TOTAL = _env_int(
    "ADEU_MAX_TOURNAMENT_DRY_RUN_EVALS_TOTAL",
    MAX_QUESTION_DRY_RUN_EVALS_TOTAL,
    minimum=1,
)
MAX_TOURNAMENT_SOLVER_CALLS_TOTAL = _env_int(
    "ADEU_MAX_TOURNAMENT_SOLVER_CALLS_TOTAL",
    MAX_QUESTION_SOLVER_CALLS_TOTAL,
    minimum=1,
)
MAX_TOURNAMENT_REPLAY_CANDIDATES = _env_int(
    "ADEU_MAX_TOURNAMENT_REPLAY_CANDIDATES",
    20,
    minimum=1,
    maximum=200,
)
MAX_TOURNAMENT_PATCH_OPS_PER_CANDIDATE = _env_int(
    "ADEU_MAX_TOURNAMENT_PATCH_OPS_PER_CANDIDATE",
    50,
    minimum=1,
    maximum=500,
)
MAX_TOURNAMENT_TOTAL_PATCH_OPS = _env_int(
    "ADEU_MAX_TOURNAMENT_TOTAL_PATCH_OPS",
    200,
    minimum=1,
    maximum=5_000,
)
MAX_TOURNAMENT_REPLAY_PAYLOAD_BYTES = _env_int(
    "ADEU_MAX_TOURNAMENT_REPLAY_PAYLOAD_BYTES",
    500_000,
    minimum=1_024,
)
MAX_TOURNAMENT_TOP_K = _env_int(
    "ADEU_MAX_TOURNAMENT_TOP_K",
    10,
    minimum=1,
    maximum=100,
)
_ALIGNMENT_KIND_RANKS: dict[str, int] = {
    "merge_candidate": 0,
    "conflict_candidate": 1,
}
_PROOF_SEMANTICS_VERSION_REQUIRED = "adeu.lean.core.v1"
_PROOF_REQUIRED_OBLIGATION_KINDS: tuple[str, ...] = (
    "conflict_soundness",
    "pred_closed_world",
)
DEFAULT_CORS_ALLOW_ORIGINS: tuple[str, ...] = (
    "http://localhost:3000",
    "http://127.0.0.1:3000",
)
CORS_ALLOW_ORIGINS = _env_csv("ADEU_CORS_ALLOW_ORIGINS") or list(DEFAULT_CORS_ALLOW_ORIGINS)
LOCALHOST_CORS_ORIGIN_REGEX = r"^https?://(localhost|127\.0\.0\.1)(:\d+)?$"


class ProposeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    clause_text: str = Field(min_length=1)
    provider: Literal["mock", "openai"] = "mock"
    mode: KernelMode = KernelMode.LAX
    context: Context | None = None
    max_candidates: int | None = Field(default=None, ge=1, le=MAX_PROPOSE_CANDIDATES)
    max_repairs: int | None = Field(default=None, ge=0, le=MAX_PROPOSE_REPAIRS)


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
    doc_id: str | None = None
    mode: KernelMode = KernelMode.LAX


class ConceptAnalyzeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    source_text: str | None = None
    doc_id: str | None = None
    mode: KernelMode = KernelMode.LAX
    include_validator_runs: bool = False
    include_analysis_details: bool = True
    include_forced_details: bool = True
    validator_runs: list[ValidatorRunInput] | None = None


class ConceptQuestionsRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    source_text: str | None = None
    doc_id: str | None = None
    mode: KernelMode = KernelMode.LAX
    include_forced_details: bool = False
    expected_ir_hash: str | None = None


class ConceptTournamentCandidateInput(BaseModel):
    model_config = ConfigDict(extra="forbid")
    question_id: str = Field(min_length=1)
    patch_ops: list[JsonPatchOp] = Field(
        min_length=1,
        max_length=MAX_TOURNAMENT_PATCH_OPS_PER_CANDIDATE,
    )


class ConceptTournamentRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    source_text: str | None = None
    doc_id: str | None = None
    mode: KernelMode = KernelMode.LAX
    tournament_mode: Literal["live_generation", "replay_candidates"] = "replay_candidates"
    provider: Literal["mock", "openai"] = "mock"
    candidates: list[ConceptTournamentCandidateInput] | None = Field(
        default=None,
        max_length=MAX_TOURNAMENT_REPLAY_CANDIDATES,
    )
    max_candidates: int = Field(default=MAX_TOURNAMENT_REPLAY_CANDIDATES, ge=1)
    top_k: int = Field(default=5, ge=1, le=MAX_TOURNAMENT_TOP_K)
    max_solver_calls: int | None = Field(
        default=None,
        ge=1,
        le=MAX_TOURNAMENT_SOLVER_CALLS_TOTAL,
    )
    max_dry_runs: int | None = Field(
        default=None,
        ge=1,
        le=MAX_TOURNAMENT_DRY_RUN_EVALS_TOTAL,
    )
    include_analysis_details: bool = False
    include_forced_details: bool = False
    expected_ir_hash: str | None = None

    @model_validator(mode="after")
    def _validate_replay_bounds(self) -> "ConceptTournamentRequest":
        if self.max_candidates > MAX_TOURNAMENT_REPLAY_CANDIDATES:
            raise ValueError(
                f"max_candidates must be <= {MAX_TOURNAMENT_REPLAY_CANDIDATES}"
            )
        if self.top_k > self.max_candidates:
            raise ValueError("top_k must be <= max_candidates")
        if self.tournament_mode == "live_generation" and self.candidates:
            raise ValueError("candidates must be omitted for live_generation")
        if self.candidates:
            total_patch_ops = sum(len(candidate.patch_ops) for candidate in self.candidates)
            if total_patch_ops > MAX_TOURNAMENT_TOTAL_PATCH_OPS:
                raise ValueError(
                    f"total candidate patch ops must be <= {MAX_TOURNAMENT_TOTAL_PATCH_OPS}"
                )
            payload = canonical_json(
                [
                    candidate.model_dump(mode="json", by_alias=True, exclude_none=True)
                    for candidate in self.candidates
                ]
            )
            payload_size = len(payload.encode("utf-8"))
            if payload_size > MAX_TOURNAMENT_REPLAY_PAYLOAD_BYTES:
                raise ValueError(
                    "candidate payload exceeds "
                    f"{MAX_TOURNAMENT_REPLAY_PAYLOAD_BYTES} bytes (got {payload_size})"
                )
        return self


class AdeuAnalyzeConceptsRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: AdeuIR
    source_text: str | None = None
    doc_id: str | None = None
    mode: KernelMode = KernelMode.LAX
    include_validator_runs: bool = False
    include_analysis_details: bool = True
    include_forced_details: bool = True


class AdeuQuestionsRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: AdeuIR
    source_text: str | None = None
    mode: KernelMode = KernelMode.LAX
    include_validator_runs: bool = False
    include_analysis_details: bool = False
    expected_ir_hash: str | None = None


class ConceptArtifactCreateRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    source_text: str | None = Field(default=None, min_length=1)
    doc_id: str | None = None
    ir: ConceptIR
    mode: KernelMode = KernelMode.STRICT


class PuzzleProposeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    puzzle_text: str = Field(min_length=1)
    provider: Literal["mock", "openai"] = "mock"
    mode: KernelMode = KernelMode.LAX
    context_override: dict[str, Any] | None = None
    max_candidates: int | None = Field(default=None, ge=1, le=MAX_PROPOSE_CANDIDATES)
    max_repairs: int | None = Field(default=None, ge=0, le=MAX_PROPOSE_REPAIRS)


class ConceptProposeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    source_text: str | None = Field(default=None, min_length=1)
    doc_id: str | None = None
    provider: Literal["mock", "openai"] = "mock"
    mode: KernelMode = KernelMode.LAX
    max_candidates: int | None = Field(default=None, ge=1, le=MAX_PROPOSE_CANDIDATES)
    max_repairs: int | None = Field(default=None, ge=0, le=MAX_PROPOSE_REPAIRS)


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
    left_doc_id: str | None = None
    right_doc_id: str | None = None
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
    left_doc_id: str | None = None
    right_doc_id: str | None = None
    additional_solver_call_budget: int | None = Field(
        default=None,
        ge=0,
        le=MAX_ADDITIONAL_SOLVER_CALL_BUDGET,
    )


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


class ConceptApplyAmbiguityOptionRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    ir_hash: str | None = None
    ambiguity_id: str = Field(min_length=1)
    option_id: str = Field(min_length=1)
    variants_by_id: dict[str, ConceptIR] | None = None
    source_text: str | None = None
    doc_id: str | None = None
    mode: KernelMode = KernelMode.LAX
    dry_run: bool = False
    include_validator_runs: bool = False


class ConceptApplyPatchRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ir: ConceptIR
    ir_hash: str | None = None
    patch_ops: list[JsonPatchOp]
    source_text: str | None = None
    doc_id: str | None = None
    mode: KernelMode = KernelMode.LAX
    dry_run: bool = False
    include_validator_runs: bool = False


ConceptPatchErrorCode = Literal[
    "PATCH_INVALID_OP",
    "PATCH_PATH_FORBIDDEN",
    "PATCH_TEST_FAILED",
    "PATCH_APPLY_FAILED",
    "PATCH_REF_INTEGRITY_VIOLATION",
    "PATCH_SIZE_LIMIT",
]


class ConceptApplyAmbiguityOptionError(BaseModel):
    model_config = ConfigDict(extra="forbid")
    op_index: int
    path: str
    code: ConceptPatchErrorCode
    message: str


SolverTrustLevel = Literal["kernel_only", "solver_backed", "proof_checked"]
ArtifactProofTrust = Literal[
    "lean_core_v1_proved",
    "lean_core_v1_partial_or_failed",
    "mock_backend_not_proof_checked",
    "no_required_proofs",
]
EvidenceRefKind = Literal["event", "run", "validator", "proof", "artifact"]


class EvidenceRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    kind: EvidenceRefKind
    ref: str = Field(min_length=1)
    note: str | None = None


class ConceptApplyAmbiguityOptionResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    patched_ir: ConceptIR
    check_report: CheckReport
    evidence_refs: list[EvidenceRef] = Field(default_factory=list)
    validator_runs: list[ValidatorRunInput] | None = None
    mapping_trust: MappingTrust | None = None
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: str | None = None


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
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: ArtifactProofTrust = "no_required_proofs"


class ArtifactGetResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    created_at: str
    clause_text: str
    ir: AdeuIR
    check_report: CheckReport
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: ArtifactProofTrust = "no_required_proofs"


class ArtifactSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    created_at: str
    doc_id: str | None
    jurisdiction: str | None
    status: str | None
    num_errors: int | None
    num_warns: int | None
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: ArtifactProofTrust = "no_required_proofs"


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
app.add_middleware(
    CORSMiddleware,
    allow_origins=CORS_ALLOW_ORIGINS,
    allow_origin_regex=LOCALHOST_CORS_ORIGIN_REGEX,
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)
app.include_router(urm_router)


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


class ConceptQuestionsResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    check_report: CheckReport
    questions: list[ConceptQuestion]
    evidence_refs: list[EvidenceRef] = Field(default_factory=list)
    question_count: int
    max_questions: int = DEFAULT_MAX_QUESTIONS
    max_answers_per_question: int = DEFAULT_MAX_ANSWERS_PER_QUESTION
    question_rank_version: Literal["concepts.qrank.v3"] = CONCEPTS_QUESTION_RANK_VERSION
    rationale_version: Literal["concepts.rationale.v1"] = CONCEPTS_RATIONALE_VERSION
    budget_report: "QuestionsBudgetReport"
    bridge_loss_signals: list["BridgeLossSignal"] = Field(default_factory=list)
    mapping_trust: MappingTrust | None = None
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: str | None = None


class QuestionsBudgetReport(BaseModel):
    model_config = ConfigDict(extra="forbid")
    budget_version: Literal["budget.v1"] = QUESTIONS_BUDGET_VERSION
    max_solver_calls: int
    used_solver_calls: int
    max_dry_runs: int
    used_dry_runs: int
    truncated: bool
    truncation_reason: str | None = None


class BridgeLossSignal(BaseModel):
    model_config = ConfigDict(extra="forbid")
    signal_kind: str
    affected_anchors: list[str] = Field(default_factory=list)
    severity: Literal["low", "medium", "high"]


class TournamentScoreMetadata(BaseModel):
    model_config = ConfigDict(extra="forbid")
    score_version: Literal["concepts.tscore.v2"] = TOURNAMENT_SCORE_VERSION
    objective_dimensions: list[str] = Field(
        default_factory=lambda: list(TOURNAMENT_OBJECTIVE_DIMENSIONS)
    )
    tie_break_order: Literal["objective_vector_desc_then_stable_id_asc"] = (
        TOURNAMENT_TIE_BREAK_ORDER
    )


class TournamentTieBreakProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid")
    stable_id: str
    objective_dimensions: list[str] = Field(
        default_factory=lambda: list(TOURNAMENT_OBJECTIVE_DIMENSIONS)
    )
    tie_break_order: Literal["objective_vector_desc_then_stable_id_asc"] = (
        TOURNAMENT_TIE_BREAK_ORDER
    )


class ConceptTournamentCandidateResult(BaseModel):
    model_config = ConfigDict(extra="forbid")
    candidate_id: str
    question_id: str
    rank: int
    improved: bool
    objective_vector: list[int] = Field(default_factory=list)
    patch_ops: list[JsonPatchOp] = Field(default_factory=list)
    check_report: CheckReport
    analysis: ConceptAnalysis | None = None
    diff_report: DiffReport
    score_version: Literal["concepts.tscore.v2"] = TOURNAMENT_SCORE_VERSION
    tie_break_provenance: TournamentTieBreakProvenance
    bridge_loss_signals: list[BridgeLossSignal] = Field(default_factory=list)
    mapping_trust: MappingTrust | None = None
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: str | None = None


class ConceptTournamentResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    tournament_mode: Literal["live_generation", "replay_candidates"]
    provider: Literal["mock", "openai"]
    tournament_score_version: Literal["concepts.tscore.v2"] = TOURNAMENT_SCORE_VERSION
    base_ir_hash: str
    base_objective_vector: list[int] = Field(default_factory=list)
    score_metadata: TournamentScoreMetadata = Field(default_factory=TournamentScoreMetadata)
    no_safe_improvement: bool
    selected_candidate_id: str | None = None
    candidate_count: int
    evaluated_count: int
    candidates: list[ConceptTournamentCandidateResult] = Field(default_factory=list)
    budget_report: QuestionsBudgetReport
    bridge_loss_signals: list[BridgeLossSignal] = Field(default_factory=list)
    mapping_trust: MappingTrust | None = None
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: str | None = None


class AdeuAnalyzeConceptsResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    concept_ir: ConceptIR
    check_report: CheckReport
    analysis: ConceptAnalysis
    bridge_manifest: BridgeManifest
    bridge_loss_report: BridgeLossReport
    bridge_mapping_version: str
    mapping_hash: str
    mapping_trust: MappingTrust
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: str | None = None
    validator_runs: list[ValidatorRunInput] | None = None


class AdeuQuestionsResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    check_report: CheckReport
    questions: list[ConceptQuestion]
    evidence_refs: list[EvidenceRef] = Field(default_factory=list)
    question_count: int
    max_questions: int = DEFAULT_MAX_QUESTIONS
    max_answers_per_question: int = DEFAULT_MAX_ANSWERS_PER_QUESTION
    question_rank_version: Literal["adeu.qrank.v1"] = ADEU_QUESTION_RANK_VERSION
    rationale_version: Literal["adeu.rationale.v1"] = ADEU_RATIONALE_VERSION
    bridge_manifest: BridgeManifest
    bridge_mapping_version: str
    mapping_hash: str
    bridge_loss_signals: list[BridgeLossSignal] = Field(default_factory=list)
    budget_report: QuestionsBudgetReport
    mapping_trust: MappingTrust = "derived_bridge"
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: str | None = None
    validator_runs: list[ValidatorRunInput] | None = None
    analysis: ConceptAnalysis | None = None


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


class DocumentCreateRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    doc_id: str = Field(min_length=1)
    domain: str = Field(min_length=1)
    source_text: str = Field(min_length=1)
    metadata: dict[str, Any] | None = None


class DocumentResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    doc_id: str
    domain: str
    source_text: str
    created_at: str
    metadata: dict[str, Any] = Field(default_factory=dict)


class DocumentSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")
    doc_id: str
    domain: str
    created_at: str


class DocumentListResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    items: list[DocumentSummary]


class ConceptAlignRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_ids: list[str] = Field(default_factory=list)
    doc_ids: list[str] = Field(default_factory=list)
    max_suggestions: int = Field(
        default=ALIGNMENT_MAX_SUGGESTIONS_DEFAULT,
        ge=ALIGNMENT_MAX_SUGGESTIONS_MIN,
        le=ALIGNMENT_MAX_SUGGESTIONS_MAX,
    )

    @model_validator(mode="after")
    def _require_scope(self) -> "ConceptAlignRequest":
        if self.artifact_ids or self.doc_ids:
            return self
        raise ValueError("provide artifact_ids and/or doc_ids")


class ConceptAlignmentArtifactRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    doc_id: str | None
    concept_id: str


class ConceptAlignmentTermRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    doc_id: str | None
    concept_id: str
    term_id: str
    label: str
    normalized_label: str


class ConceptAlignmentSenseRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifact_id: str
    doc_id: str | None
    concept_id: str
    sense_id: str
    term_id: str
    gloss: str
    gloss_signature: str


class ConceptAlignmentSuggestion(BaseModel):
    model_config = ConfigDict(extra="forbid")
    suggestion_id: str
    suggestion_fingerprint: str
    kind: Literal["merge_candidate", "conflict_candidate"]
    vocabulary_key: str
    reason: str
    artifact_ids: list[str] = Field(default_factory=list)
    doc_ids: list[str] = Field(default_factory=list)
    term_refs: list[ConceptAlignmentTermRef] = Field(default_factory=list)
    sense_refs: list[ConceptAlignmentSenseRef] = Field(default_factory=list)


class ConceptAlignmentStats(BaseModel):
    model_config = ConfigDict(extra="forbid")
    merge_candidate_count: int
    conflict_candidate_count: int


class ConceptAlignmentCoherenceDiagnostics(BaseModel):
    model_config = ConfigDict(extra="forbid")
    vocabulary_drift_count: int
    suggestion_stability_count: int
    term_use_consistency_count: int


class ConceptAlignResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")
    artifacts: list[ConceptAlignmentArtifactRef]
    suggestion_count: int
    suggestions: list[ConceptAlignmentSuggestion]
    alignment_stats: ConceptAlignmentStats
    coherence_diagnostics: ConceptAlignmentCoherenceDiagnostics
    mapping_trust: MappingTrust = "derived_alignment"
    solver_trust: SolverTrustLevel = "kernel_only"
    proof_trust: str | None = None


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
            "message": (f"{field} exceeds {MAX_SOURCE_TEXT_BYTES} bytes (got {size_bytes} bytes)"),
            "field": field,
            "max_bytes": MAX_SOURCE_TEXT_BYTES,
            "actual_bytes": size_bytes,
        },
    )


def _resolve_source_text_and_doc_id(
    *,
    source_text: str | None,
    doc_id: str | None,
    require_source: bool = False,
    source_field: str = "source_text",
) -> tuple[str | None, str | None]:
    if source_text is not None:
        _enforce_source_text_size(source_text, field=source_field)

    if doc_id is None:
        if require_source and source_text is None:
            raise HTTPException(
                status_code=400,
                detail={
                    "code": "DOC_SOURCE_REQUIRED",
                    "message": "provide source_text or doc_id",
                },
            )
        return source_text, None

    row = get_document(doc_id=doc_id)
    if row is None:
        raise HTTPException(
            status_code=404,
            detail={
                "code": "DOC_NOT_FOUND",
                "message": f"document not found for doc_id={doc_id!r}",
                "doc_id": doc_id,
            },
        )

    if source_text is not None and source_text != row.source_text:
        raise HTTPException(
            status_code=400,
            detail={
                "code": "DOC_TEXT_MISMATCH",
                "message": "provided source_text does not match stored document source_text",
                "doc_id": doc_id,
            },
        )

    return row.source_text, doc_id


def _normalize_alignment_text(value: str) -> str:
    tokens = re.findall(r"[a-z0-9]+", value.lower())
    return " ".join(tokens)


def _sanitize_alignment_token(value: str) -> str:
    cleaned = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in value)
    cleaned = cleaned.strip("_")
    return cleaned or "alignment"


def _next_alignment_suggestion_id(
    *,
    kind: Literal["merge_candidate", "conflict_candidate"],
    vocabulary_key: str,
    used_ids: set[str],
) -> str:
    stem = _sanitize_alignment_token(f"{kind}_{vocabulary_key}")
    candidate = stem
    suffix = 2
    while candidate in used_ids:
        candidate = f"{stem}_{suffix}"
        suffix += 1
    used_ids.add(candidate)
    return candidate


def _resolve_alignment_artifact_ids(req: ConceptAlignRequest) -> list[str]:
    artifact_ids = {artifact_id.strip() for artifact_id in req.artifact_ids if artifact_id.strip()}
    for doc_id in sorted({item.strip() for item in req.doc_ids if item.strip()}):
        rows = list_concept_artifacts(doc_id=doc_id, limit=1, offset=0)
        if not rows:
            raise HTTPException(
                status_code=404,
                detail={
                    "code": "ALIGNMENT_DOC_NO_ARTIFACT",
                    "message": f"no concept artifacts found for doc_id={doc_id!r}",
                    "doc_id": doc_id,
                },
            )
        artifact_ids.add(rows[0].artifact_id)
    if len(artifact_ids) > MAX_ALIGNMENT_SCOPE_ARTIFACTS:
        raise HTTPException(
            status_code=400,
            detail={
                "code": "ALIGNMENT_SCOPE_TOO_LARGE",
                "message": (
                    "alignment scope exceeds deterministic cap "
                    f"({len(artifact_ids)} > {MAX_ALIGNMENT_SCOPE_ARTIFACTS})"
                ),
                "max_artifacts": MAX_ALIGNMENT_SCOPE_ARTIFACTS,
                "actual_artifacts": len(artifact_ids),
            },
        )
    if artifact_ids:
        return sorted(artifact_ids)
    raise HTTPException(
        status_code=400,
        detail={
            "code": "ALIGNMENT_SCOPE_EMPTY",
            "message": "alignment scope is empty after normalization",
        },
    )


def _collect_alignment_artifacts(
    artifact_ids: list[str],
) -> list[tuple[str, str | None, ConceptIR]]:
    items: list[tuple[str, str | None, ConceptIR]] = []
    for artifact_id in artifact_ids:
        row = get_concept_artifact(artifact_id=artifact_id)
        if row is None:
            raise HTTPException(
                status_code=404,
                detail={
                    "code": "ALIGNMENT_ARTIFACT_NOT_FOUND",
                    "message": f"concept artifact not found for artifact_id={artifact_id!r}",
                    "artifact_id": artifact_id,
                },
            )
        items.append((row.artifact_id, row.doc_id, ConceptIR.model_validate(row.ir_json)))
    return items


class _AlignmentTermEntry(NamedTuple):
    artifact_id: str
    doc_id: str | None
    concept: ConceptIR
    term_id: str
    label: str


def _alignment_kind_rank(kind: str) -> int:
    return _ALIGNMENT_KIND_RANKS.get(kind, 2)


def _alignment_suggestion_fingerprint(
    *,
    kind: Literal["merge_candidate", "conflict_candidate"],
    vocabulary_key: str,
    term_refs: list[ConceptAlignmentTermRef],
    sense_refs: list[ConceptAlignmentSenseRef],
) -> str:
    concept_ids = sorted(
        {item.concept_id for item in term_refs} | {item.concept_id for item in sense_refs}
    )
    term_ids = sorted({item.term_id for item in term_refs} | {item.term_id for item in sense_refs})
    sense_ids = sorted({item.sense_id for item in sense_refs})
    payload = {
        "kind": kind,
        "vocabulary_key": vocabulary_key,
        "concept_ids": concept_ids,
        "term_ids": term_ids,
        "sense_ids": sense_ids,
    }
    return sha256_canonical_json(payload)[:12]


def _alignment_stats(suggestions: list[ConceptAlignmentSuggestion]) -> ConceptAlignmentStats:
    merge_count = sum(1 for item in suggestions if item.kind == "merge_candidate")
    conflict_count = sum(1 for item in suggestions if item.kind == "conflict_candidate")
    return ConceptAlignmentStats(
        merge_candidate_count=merge_count,
        conflict_candidate_count=conflict_count,
    )


def _alignment_coherence_diagnostics(
    suggestions: list[ConceptAlignmentSuggestion],
) -> ConceptAlignmentCoherenceDiagnostics:
    kinds_by_vocabulary: dict[str, set[str]] = {}
    fingerprints: set[str] = set()
    for suggestion in suggestions:
        kinds_by_vocabulary.setdefault(suggestion.vocabulary_key, set()).add(suggestion.kind)
        if suggestion.suggestion_fingerprint:
            fingerprints.add(suggestion.suggestion_fingerprint)

    vocabulary_drift_count = sum(
        1 for kinds in kinds_by_vocabulary.values() if "conflict_candidate" in kinds
    )
    term_use_consistency_count = sum(
        1
        for kinds in kinds_by_vocabulary.values()
        if "merge_candidate" in kinds and "conflict_candidate" not in kinds
    )
    return ConceptAlignmentCoherenceDiagnostics(
        vocabulary_drift_count=vocabulary_drift_count,
        suggestion_stability_count=len(fingerprints),
        term_use_consistency_count=term_use_consistency_count,
    )


def _bridge_loss_signals(report: BridgeLossReport) -> list[BridgeLossSignal]:
    signals: list[BridgeLossSignal] = []
    for entry in report.entries:
        if entry.scope != "instance":
            continue
        if entry.status == "preserved":
            continue
        severity: Literal["low", "medium", "high"] = (
            "high" if entry.status == "not_modeled" else "medium"
        )
        signals.append(
            BridgeLossSignal(
                signal_kind=f"{entry.feature_key}:{entry.status}",
                affected_anchors=sorted(entry.source_paths),
                severity=severity,
            )
        )
    return sorted(
        signals,
        key=lambda item: (item.signal_kind, tuple(item.affected_anchors), item.severity),
    )


def _build_alignment_suggestions(
    artifacts: list[tuple[str, str | None, ConceptIR]],
    *,
    max_suggestions: int,
) -> list[ConceptAlignmentSuggestion]:
    term_groups: dict[str, list[_AlignmentTermEntry]] = {}
    for artifact_id, doc_id, concept in artifacts:
        for term in concept.terms:
            vocabulary_key = _normalize_alignment_text(term.label)
            if not vocabulary_key:
                continue
            term_groups.setdefault(vocabulary_key, []).append(
                _AlignmentTermEntry(
                    artifact_id=artifact_id,
                    doc_id=doc_id,
                    concept=concept,
                    term_id=term.id,
                    label=term.label,
                )
            )

    used_suggestion_ids: set[str] = set()
    suggestions: list[ConceptAlignmentSuggestion] = []
    for vocabulary_key in sorted(term_groups.keys()):
        entries = sorted(
            term_groups[vocabulary_key],
            key=lambda item: (item.artifact_id, item.term_id, item.label),
        )
        artifact_ids = sorted({item.artifact_id for item in entries})
        if len(artifact_ids) < 2:
            continue

        term_refs = [
            ConceptAlignmentTermRef(
                artifact_id=entry.artifact_id,
                doc_id=entry.doc_id,
                concept_id=entry.concept.concept_id,
                term_id=entry.term_id,
                label=entry.label,
                normalized_label=vocabulary_key,
            )
            for entry in entries
        ]

        sense_refs: list[ConceptAlignmentSenseRef] = []
        signatures_by_artifact: dict[str, set[str]] = {}
        for entry in entries:
            senses = sorted(
                (sense for sense in entry.concept.senses if sense.term_id == entry.term_id),
                key=lambda sense: sense.id,
            )
            for sense in senses:
                gloss_signature = _normalize_alignment_text(sense.gloss)
                if not gloss_signature:
                    gloss_signature = _normalize_alignment_text(sense.id)
                signatures_by_artifact.setdefault(entry.artifact_id, set()).add(gloss_signature)
                sense_refs.append(
                    ConceptAlignmentSenseRef(
                        artifact_id=entry.artifact_id,
                        doc_id=entry.doc_id,
                        concept_id=entry.concept.concept_id,
                        sense_id=sense.id,
                        term_id=entry.term_id,
                        gloss=sense.gloss,
                        gloss_signature=gloss_signature,
                    )
                )
        sense_refs.sort(key=lambda item: (item.artifact_id, item.term_id, item.sense_id))
        doc_ids = sorted({item.doc_id for item in term_refs if item.doc_id is not None})

        suggestions.append(
            ConceptAlignmentSuggestion(
                suggestion_id=_next_alignment_suggestion_id(
                    kind="merge_candidate",
                    vocabulary_key=vocabulary_key,
                    used_ids=used_suggestion_ids,
                ),
                suggestion_fingerprint=_alignment_suggestion_fingerprint(
                    kind="merge_candidate",
                    vocabulary_key=vocabulary_key,
                    term_refs=term_refs,
                    sense_refs=sense_refs,
                ),
                kind="merge_candidate",
                vocabulary_key=vocabulary_key,
                reason=(
                    f"Term '{vocabulary_key}' appears across artifacts; "
                    "consider a shared vocabulary mapping."
                ),
                artifact_ids=artifact_ids,
                doc_ids=doc_ids,
                term_refs=term_refs,
                sense_refs=sense_refs,
            )
        )

        signature_profiles = {
            tuple(sorted(signatures_by_artifact.get(artifact_id, set())))
            for artifact_id in artifact_ids
        }
        if len(signature_profiles) > 1:
                suggestions.append(
                    ConceptAlignmentSuggestion(
                        suggestion_id=_next_alignment_suggestion_id(
                            kind="conflict_candidate",
                            vocabulary_key=vocabulary_key,
                            used_ids=used_suggestion_ids,
                        ),
                        suggestion_fingerprint=_alignment_suggestion_fingerprint(
                            kind="conflict_candidate",
                            vocabulary_key=vocabulary_key,
                            term_refs=term_refs,
                            sense_refs=sense_refs,
                        ),
                        kind="conflict_candidate",
                        vocabulary_key=vocabulary_key,
                        reason=(
                            f"Term '{vocabulary_key}' has divergent sense gloss signatures "
                            "across artifacts; review before merge."
                    ),
                    artifact_ids=artifact_ids,
                    doc_ids=doc_ids,
                    term_refs=term_refs,
                    sense_refs=sense_refs,
                )
            )

    suggestions.sort(
        key=lambda item: (
            _alignment_kind_rank(item.kind),
            item.vocabulary_key,
            item.suggestion_id,
        )
    )
    return suggestions[:max_suggestions]


def _map_concept_patch_error_code(raw_code: str) -> ConceptPatchErrorCode:
    error_map: dict[str, ConceptPatchErrorCode] = {
        "PATCH_OP_UNSUPPORTED": "PATCH_INVALID_OP",
        "PATCH_PATH_NOT_ALLOWED": "PATCH_PATH_FORBIDDEN",
        "PATCH_TEST_FAILED": "PATCH_TEST_FAILED",
        "PATCH_TOO_LARGE": "PATCH_SIZE_LIMIT",
        "REFERENCE_INTEGRITY": "PATCH_REF_INTEGRITY_VIOLATION",
    }
    return error_map.get(raw_code, "PATCH_APPLY_FAILED")


def _concept_patch_http_error_detail(exc: ConceptPatchValidationError) -> dict[str, Any]:
    errors = [
        ConceptApplyAmbiguityOptionError(
            op_index=err.op_index,
            path=err.path,
            code=_map_concept_patch_error_code(err.code),
            message=err.message,
        ).model_dump(mode="json")
        for err in exc.errors
    ]
    errors = sorted(errors, key=lambda item: (item["op_index"], item["path"], item["code"]))
    return {
        "code": "PATCH_INVALID",
        "message": "concept patch application failed",
        "errors": errors,
    }


def _apply_concept_patch_core(
    *,
    decision_endpoint: str,
    ir: ConceptIR,
    ir_hash: str | None,
    mode: KernelMode,
    source_text: str | None,
    doc_id: str | None,
    dry_run: bool,
    include_validator_runs: bool,
    patch_ops: list[JsonPatchOp] | None = None,
    patched_ir: ConceptIR | None = None,
) -> ConceptApplyAmbiguityOptionResponse:
    if (patch_ops is None) == (patched_ir is None):
        raise ValueError("provide exactly one of patch_ops or patched_ir")
    source_text, _ = _resolve_source_text_and_doc_id(
        source_text=source_text,
        doc_id=doc_id,
        require_source=False,
    )
    _require_ir_hash_match(ir=ir, ir_hash=ir_hash)

    patched = patched_ir
    if patch_ops is not None:
        try:
            patched = apply_concept_json_patch(ir, patch_ops)
        except ConceptPatchValidationError as exc:
            raise HTTPException(
                status_code=400,
                detail=_concept_patch_http_error_detail(exc),
            ) from exc

    assert patched is not None
    report, runs = check_concept_with_validator_runs(
        patched,
        mode=mode,
        source_text=source_text,
    )
    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS") and runs and not dry_run:
        _persist_validator_runs(runs=runs, artifact_id=None)
    run_inputs = [_validator_run_input_from_record(run) for run in runs]
    evidence_refs = _build_patch_evidence_refs(
        endpoint=decision_endpoint,
        base_ir_hash=_concept_ir_hash(ir),
        runs=run_inputs,
    )
    _require_patch_evidence_bindings(evidence_refs)

    return ConceptApplyAmbiguityOptionResponse(
        patched_ir=patched,
        check_report=report,
        evidence_refs=evidence_refs,
        validator_runs=run_inputs if include_validator_runs else None,
        mapping_trust=None,
        solver_trust="solver_backed" if runs else "kernel_only",
        proof_trust=None,
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


def _normalize_evidence_json_for_output(evidence_json: dict[str, Any]) -> dict[str, Any]:
    payload = dict(evidence_json)
    unsat_core = payload.get("unsat_core")
    if isinstance(unsat_core, list):
        payload["unsat_core"] = sorted(str(item) for item in unsat_core)
    model = payload.get("model")
    if isinstance(model, dict):
        payload["model"] = {str(key): model[key] for key in sorted(model.keys())}
    return payload


def _validator_run_input_from_record(run: ValidatorRunRecord) -> ValidatorRunInput:
    evidence = _normalize_evidence_json_for_output(
        run.result.evidence.model_dump(mode="json", exclude_none=True)
    )
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
        evidence_json=evidence,
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
    evidence = payload.get("evidence_json")
    if isinstance(evidence, dict):
        payload["evidence_json"] = _normalize_evidence_json_for_output(evidence)
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


def _concept_ir_hash(ir: ConceptIR) -> str:
    payload = ir.model_dump(mode="json", by_alias=True, exclude_none=True)
    return sha256_canonical_json(payload)


def _adeu_ir_hash(ir: AdeuIR) -> str:
    payload = ir.model_dump(mode="json", by_alias=True, exclude_none=True)
    return sha256_canonical_json(payload)


def _decision_stream_id(*, endpoint: str, ir_hash: str) -> str:
    cleaned_endpoint = endpoint.strip(" /") or "root"
    endpoint_key = cleaned_endpoint.replace("/", ":")
    digest = sha256_text(f"{cleaned_endpoint}:{ir_hash}")[:12]
    return f"decision:{endpoint_key}:{digest}"


def _sorted_unique_evidence_refs(refs: list[EvidenceRef]) -> list[EvidenceRef]:
    deduped: dict[tuple[str, str, str], EvidenceRef] = {}
    for ref in refs:
        deduped[(ref.kind, ref.ref, ref.note or "")] = ref
    return sorted(
        deduped.values(),
        key=lambda item: (item.kind, item.ref, item.note or ""),
    )


def _event_evidence_ref(*, endpoint: str, ir_hash: str, note: str | None = None) -> EvidenceRef:
    stream_id = _decision_stream_id(endpoint=endpoint, ir_hash=ir_hash)
    return EvidenceRef(kind="event", ref=f"event:{stream_id}#1", note=note)


def _validator_ref_id(run: ValidatorRunInput) -> str:
    if run.run_id:
        return run.run_id
    return f"{run.request_hash}:{run.formula_hash}"


def _validator_evidence_refs_from_runs(runs: list[ValidatorRunInput]) -> list[EvidenceRef]:
    refs = {f"validator:{_validator_ref_id(run)}" for run in runs}
    return [EvidenceRef(kind="validator", ref=ref) for ref in sorted(refs)]


def _build_patch_evidence_refs(
    *,
    endpoint: str,
    base_ir_hash: str,
    runs: list[ValidatorRunInput],
) -> list[EvidenceRef]:
    refs: list[EvidenceRef] = [
        _event_evidence_ref(
            endpoint=endpoint,
            ir_hash=base_ir_hash,
            note="patch_apply",
        ),
    ]
    refs.extend(_validator_evidence_refs_from_runs(runs))
    return _sorted_unique_evidence_refs(refs)


def _build_question_evidence_refs(
    *,
    endpoint: str,
    ir_hash: str,
    runs: list[ValidatorRunInput],
) -> list[EvidenceRef]:
    refs: list[EvidenceRef] = [
        _event_evidence_ref(
            endpoint=endpoint,
            ir_hash=ir_hash,
            note="question_generation",
        )
    ]
    refs.extend(_validator_evidence_refs_from_runs(runs))
    return _sorted_unique_evidence_refs(refs)


def _require_patch_evidence_bindings(evidence_refs: list[EvidenceRef]) -> None:
    has_event = any(ref.kind == "event" for ref in evidence_refs)
    has_validation_or_artifact = any(
        ref.kind in {"validator", "artifact"} for ref in evidence_refs
    )
    if has_event and has_validation_or_artifact:
        return
    raise HTTPException(
        status_code=500,
        detail={
            "code": "EVIDENCE_BINDING_MISSING",
            "message": "patch apply response is missing required evidence bindings",
        },
    )


def _require_ir_hash_match(*, ir: ConceptIR, ir_hash: str | None) -> None:
    if ir_hash is None:
        return
    expected = _concept_ir_hash(ir)
    if expected == ir_hash:
        return
    raise HTTPException(
        status_code=409,
        detail={
            "code": "STALE_IR",
            "message": "ir_hash precondition failed; refresh IR and retry",
            "expected_ir_hash": expected,
            "provided_ir_hash": ir_hash,
        },
    )


def _require_tournament_ir_hash_match(*, ir: ConceptIR, ir_hash: str | None) -> None:
    if ir_hash is None:
        return
    expected = _concept_ir_hash(ir)
    if expected == ir_hash:
        return
    raise HTTPException(
        status_code=409,
        detail={
            "code": "TOURNAMENT_STALE_IR_HASH_MISMATCH",
            "legacy_code": "STALE_IR",
            "message": "ir_hash precondition failed; refresh IR and retry",
            "expected_ir_hash": expected,
            "provided_ir_hash": ir_hash,
        },
    )


def _require_adeu_ir_hash_match(*, ir: AdeuIR, ir_hash: str | None) -> None:
    if ir_hash is None:
        return
    expected = _adeu_ir_hash(ir)
    if expected == ir_hash:
        return
    raise HTTPException(
        status_code=409,
        detail={
            "code": "STALE_IR",
            "message": "ir_hash precondition failed; refresh IR and retry",
            "expected_ir_hash": expected,
            "provided_ir_hash": ir_hash,
        },
    )


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


def _proof_detail_text(details: dict[str, Any], key: str) -> str | None:
    value = details.get(key)
    if isinstance(value, str) and value:
        return value
    return None


def _latest_required_proof_rows(
    proof_rows: list[ProofArtifactRow],
) -> dict[str, ProofArtifactRow]:
    by_kind: dict[str, ProofArtifactRow] = {}
    sorted_rows = sorted(
        proof_rows,
        key=lambda row: (row.created_at, row.proof_id),
        reverse=True,
    )
    for row in sorted_rows:
        obligation_kind = _proof_detail_text(row.details_json, "obligation_kind")
        if obligation_kind not in _PROOF_REQUIRED_OBLIGATION_KINDS:
            continue
        if obligation_kind in by_kind:
            continue
        by_kind[obligation_kind] = row
    return by_kind


def _artifact_trust_labels(
    *,
    validator_runs: list[ValidatorRunRow] | list[ValidatorRunRecord],
    proof_rows: list[ProofArtifactRow],
) -> tuple[SolverTrustLevel, ArtifactProofTrust]:
    fallback_solver_trust: SolverTrustLevel = "solver_backed" if validator_runs else "kernel_only"
    required_by_kind = _latest_required_proof_rows(proof_rows)
    required_rows: list[ProofArtifactRow] = []
    for obligation_kind in _PROOF_REQUIRED_OBLIGATION_KINDS:
        row = required_by_kind.get(obligation_kind)
        if row is None:
            return fallback_solver_trust, "no_required_proofs"
        required_rows.append(row)

    if any(row.backend != "lean" for row in required_rows):
        return fallback_solver_trust, "mock_backend_not_proof_checked"

    for row in required_rows:
        semantics_version = _proof_detail_text(row.details_json, "semantics_version")
        if semantics_version != _PROOF_SEMANTICS_VERSION_REQUIRED or row.status != "proved":
            return fallback_solver_trust, "lean_core_v1_partial_or_failed"

    return "proof_checked", "lean_core_v1_proved"


def _persist_proof_artifact(
    *,
    artifact_id: str,
    ir: AdeuIR,
    runs: list[ValidatorRunRecord],
    connection: sqlite3.Connection | None = None,
) -> list[ProofArtifactRow]:
    persisted_rows: list[ProofArtifactRow] = []
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
                proof_id=f"proof_{sha256_text(theorem_id + str(exc))[:16]}",
                backend=backend_kind,
                theorem_id=theorem_id,
                status="failed",
                proof_hash=sha256_text(theorem_src + str(exc)),
                inputs=obligation.inputs,
                details={"error": str(exc)},
            )

        details = dict(proof.details)
        details.setdefault("backend_proof_id", proof.proof_id)
        details.setdefault("semantics_version", obligation.semantics_version)
        details.setdefault("inputs_hash", obligation.metadata.get("inputs_hash"))
        details.setdefault("theorem_src_hash", obligation.metadata.get("theorem_src_hash"))
        details.setdefault("obligation_kind", obligation.obligation_kind)
        persisted_rows.append(
            create_proof_artifact(
                artifact_id=artifact_id,
                backend=proof.backend,
                theorem_id=proof.theorem_id,
                status=proof.status,
                proof_hash=proof.proof_hash,
                inputs_json=[
                    item.model_dump(mode="json", exclude_none=True) for item in proof.inputs
                ],
                details_json=details,
                connection=connection,
            )
        )
    return persisted_rows


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
    resolved_source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.source_text,
        doc_id=req.doc_id,
        require_source=False,
    )
    req = req.model_copy(update={"source_text": resolved_source_text})

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


def _question_priority_class(signal: str) -> int:
    if signal == "mic":
        return 0
    if signal == "forced_countermodel":
        return 1
    if signal == "disconnected_clusters":
        return 2
    return 3


def _severity_rank_value(value: ReasonSeverity | str | None) -> int:
    if isinstance(value, ReasonSeverity):
        severity = value.value
    else:
        severity = str(value or "").upper()
    if severity == ReasonSeverity.ERROR.value:
        return 0
    if severity == ReasonSeverity.WARN.value:
        return 1
    if severity == ReasonSeverity.INFO.value:
        return 2
    return 3


def _question_anchor_sets(question: ConceptQuestion) -> tuple[tuple[str, ...], tuple[str, ...]]:
    object_ids = tuple(
        sorted(
            {
                anchor.object_id
                for anchor in question.anchors
                if isinstance(anchor.object_id, str) and anchor.object_id
            }
        )
    )
    json_paths = tuple(
        sorted(
            {
                anchor.json_path
                for anchor in question.anchors
                if isinstance(anchor.json_path, str) and anchor.json_path
            }
        )
    )
    return object_ids, json_paths


def _question_anchor_key(question: ConceptQuestion) -> str:
    pairs = sorted(
        (
            anchor.object_id or "",
            anchor.json_path or "",
        )
        for anchor in question.anchors
    )
    return "|".join(f"{object_id}@{json_path}" for object_id, json_path in pairs)


def _question_template_id(question: ConceptQuestion) -> str:
    labels = sorted(
        {
            anchor.label
            for anchor in question.anchors
            if isinstance(anchor.label, str) and anchor.label
        }
    )
    suffix = labels[0] if labels else "generic"
    return f"{question.signal}:{suffix}"


def _normalize_question_prompt(prompt: str) -> str:
    normalized = re.sub(r"[^\w\s]", " ", prompt.lower())
    return " ".join(normalized.split())


def _question_normalized_text_hash(question: ConceptQuestion) -> str:
    return sha256_text(_normalize_question_prompt(question.prompt))


def _question_target_entity_ids(question: ConceptQuestion) -> tuple[str, ...]:
    object_ids, json_paths = _question_anchor_sets(question)
    targets = {f"obj:{object_id}" for object_id in object_ids}
    targets.update(f"path:{json_path}" for json_path in json_paths)
    return tuple(sorted(targets))


def _question_polarity(question: ConceptQuestion) -> str:
    return QUESTION_POLARITY_BY_SIGNAL.get(question.signal, "generic")


def _concept_term_component_sizes(ir: ConceptIR) -> dict[str, int]:
    sense_to_term = {sense.id: sense.term_id for sense in ir.senses}
    adjacency: dict[str, set[str]] = {term.id: set() for term in ir.terms}

    for link in ir.links:
        src_term = sense_to_term.get(link.src_sense_id)
        dst_term = sense_to_term.get(link.dst_sense_id)
        if src_term is None or dst_term is None:
            continue
        adjacency.setdefault(src_term, set()).add(dst_term)
        adjacency.setdefault(dst_term, set()).add(src_term)

    sizes: dict[str, int] = {}
    seen: set[str] = set()
    for term_id in sorted(adjacency.keys()):
        if term_id in seen:
            continue
        frontier = deque([term_id])
        seen.add(term_id)
        component: list[str] = []
        while frontier:
            current = frontier.popleft()
            component.append(current)
            for neighbor in sorted(adjacency.get(current, set())):
                if neighbor in seen:
                    continue
                seen.add(neighbor)
                frontier.append(neighbor)
        component_size = len(component)
        for node in component:
            sizes[node] = component_size

    return sizes


def _question_impact_score(
    question: ConceptQuestion,
    *,
    analysis: ConceptAnalysis,
    term_component_sizes: dict[str, int],
) -> int:
    if question.signal == "mic":
        object_ids, json_paths = _question_anchor_sets(question)
        object_id_set = set(object_ids)
        json_path_set = set(json_paths)
        matches = 0
        for constraint in analysis.mic.constraints:
            if constraint.object_id and constraint.object_id in object_id_set:
                matches += 1
                continue
            if constraint.json_path and constraint.json_path in json_path_set:
                matches += 1
        return max(1, matches)
    if question.signal == "forced_countermodel":
        return 1
    if question.signal == "disconnected_clusters":
        object_ids, _ = _question_anchor_sets(question)
        sizes = [
            term_component_sizes[term_id]
            for term_id in object_ids
            if term_id in term_component_sizes
        ]
        if not sizes:
            return 1
        return max(1, min(sizes))
    return 0


def _question_severity_rank(question: ConceptQuestion, *, report: CheckReport) -> int:
    object_ids, json_paths = _question_anchor_sets(question)
    object_id_set = set(object_ids)
    json_path_set = set(json_paths)

    best: int | None = None
    for reason in report.reason_codes:
        reason_object_id = reason.object_id
        reason_json_path = reason.json_path
        matches = bool(reason_object_id and reason_object_id in object_id_set) or bool(
            reason_json_path and reason_json_path in json_path_set
        )
        if not matches:
            continue
        rank = _severity_rank_value(reason.severity)
        if best is None or rank < best:
            best = rank

    if best is not None:
        return best
    return _question_priority_class(question.signal)


def _question_rank_tuple(
    question: ConceptQuestion,
    *,
    analysis: ConceptAnalysis,
    report: CheckReport,
    term_component_sizes: dict[str, int],
) -> tuple[int, int, int, str, str, str, str]:
    priority_class = _question_priority_class(question.signal)
    impact_score = _question_impact_score(
        question,
        analysis=analysis,
        term_component_sizes=term_component_sizes,
    )
    severity_rank = _question_severity_rank(question, report=report)
    anchor_key = _question_anchor_key(question)
    template_id = _question_template_id(question)
    question_text = question.prompt
    return (
        priority_class,
        -impact_score,
        severity_rank,
        anchor_key,
        template_id,
        question_text,
        question.question_id,
    )


def _question_dedupe_key(
    question: ConceptQuestion,
) -> tuple[str, tuple[str, ...], str, str]:
    return (
        question.signal,
        _question_target_entity_ids(question),
        _question_polarity(question),
        _question_normalized_text_hash(question),
    )


def _rank_and_dedupe_questions(
    *,
    questions: list[ConceptQuestion],
    analysis: ConceptAnalysis,
    report: CheckReport,
    ir: ConceptIR,
) -> list[ConceptQuestion]:
    term_component_sizes = _concept_term_component_sizes(ir)
    sorted_questions = sorted(
        questions,
        key=lambda item: _question_rank_tuple(
            item,
            analysis=analysis,
            report=report,
            term_component_sizes=term_component_sizes,
        ),
    )

    deduped: list[ConceptQuestion] = []
    seen: set[tuple[str, tuple[str, ...], str, str]] = set()
    for question in sorted_questions:
        dedupe_key = _question_dedupe_key(question)
        if dedupe_key in seen:
            continue
        seen.add(dedupe_key)
        deduped.append(question)
    return deduped


def _analysis_mic_count(analysis: ConceptAnalysis) -> int:
    if analysis.mic.status == "UNAVAILABLE":
        return 0
    return analysis.mic.constraint_count


def _analysis_countermodel_count(analysis: ConceptAnalysis) -> int:
    if analysis.forced.status == "UNAVAILABLE":
        return 0
    return analysis.forced.countermodel_count


def _is_do_no_harm_improvement(
    *,
    base_report: CheckReport,
    base_analysis: ConceptAnalysis,
    patched_report: CheckReport,
    patched_analysis: ConceptAnalysis,
) -> bool:
    if base_report.status != "PASS" and patched_report.status == "PASS":
        return True

    base_mic = _analysis_mic_count(base_analysis)
    patched_mic = _analysis_mic_count(patched_analysis)
    if patched_mic < base_mic:
        return True

    base_countermodels = _analysis_countermodel_count(base_analysis)
    patched_countermodels = _analysis_countermodel_count(patched_analysis)
    if patched_countermodels < base_countermodels:
        return True

    return False


def _check_status_score(status: str) -> int:
    if status == "PASS":
        return 3
    if status == "WARN":
        return 2
    if status == "REFUSE":
        return 1
    return 0


def _check_reason_count(report: CheckReport, *, severity: ReasonSeverity) -> int:
    return sum(1 for reason in report.reason_codes if reason.severity == severity)


def _tournament_objective_vector(
    *,
    report: CheckReport,
    analysis: ConceptAnalysis,
) -> tuple[int, int, int, int, int]:
    return (
        _check_status_score(report.status),
        -_check_reason_count(report, severity=ReasonSeverity.ERROR),
        -_check_reason_count(report, severity=ReasonSeverity.WARN),
        -_analysis_mic_count(analysis),
        -_analysis_countermodel_count(analysis),
    )


def _tournament_rank_key(
    candidate: _TournamentCandidateEvaluation,
) -> tuple[int, int, int, int, int, str]:
    objective = candidate.objective_vector
    return (
        -objective[0],
        -objective[1],
        -objective[2],
        -objective[3],
        -objective[4],
        candidate.candidate_id,
    )


def _analysis_for_response(
    *,
    analysis: ConceptAnalysis,
    include_analysis_details: bool,
    include_forced_details: bool,
) -> ConceptAnalysis:
    if not include_analysis_details:
        return strip_analysis_details(analysis)
    if not include_forced_details:
        return strip_forced_details(analysis)
    return analysis


def _tournament_candidate_id(
    *,
    base_ir_hash: str,
    question_id: str,
    patch_ops: list[JsonPatchOp],
) -> str:
    payload = {
        "base_ir_hash": base_ir_hash,
        "patch_ops_canonical": _question_patch_key(patch_ops),
        "question_id": question_id,
        "tournament_score_version": TOURNAMENT_SCORE_VERSION,
    }
    return sha256_canonical_json(payload)[:12]


class _TournamentCandidateEvaluation(NamedTuple):
    candidate_id: str
    question_id: str
    patch_ops: list[JsonPatchOp]
    objective_vector: tuple[int, int, int, int, int]
    improved: bool
    check_report: CheckReport
    analysis: ConceptAnalysis
    diff_report: DiffReport
    solver_trust: SolverTrustLevel


def _build_live_tournament_candidates(
    *,
    ir: ConceptIR,
    analysis: ConceptAnalysis,
    report: CheckReport,
    max_candidates: int,
) -> tuple[list[ConceptTournamentCandidateInput], bool]:
    raw_questions = build_concept_questions(
        ir,
        analysis,
        max_questions=DEFAULT_MAX_QUESTIONS,
        max_answers_per_question=DEFAULT_MAX_ANSWERS_PER_QUESTION,
    )
    ranked_questions = _rank_and_dedupe_questions(
        questions=raw_questions,
        analysis=analysis,
        report=report,
        ir=ir,
    )

    seen: set[tuple[str, str]] = set()
    candidates: list[ConceptTournamentCandidateInput] = []
    for question in ranked_questions:
        for answer in question.answers:
            patch_ops = answer.patch or []
            if not patch_ops:
                continue
            dedupe_key = (question.question_id, _question_patch_key(patch_ops))
            if dedupe_key in seen:
                continue
            seen.add(dedupe_key)
            candidates.append(
                ConceptTournamentCandidateInput(
                    question_id=question.question_id,
                    patch_ops=patch_ops,
                )
            )

    truncated = len(candidates) > max_candidates
    return candidates[:max_candidates], truncated


def _evaluate_tournament_candidate(
    *,
    ir: ConceptIR,
    source_text: str | None,
    mode: KernelMode,
    base_run_inputs: list[ValidatorRunInput],
    base_ir_hash: str,
    base_objective: tuple[int, int, int, int, int],
    candidate: ConceptTournamentCandidateInput,
    include_analysis_details: bool,
    include_forced_details: bool,
    remaining_solver_calls: int,
) -> tuple[_TournamentCandidateEvaluation | None, int]:
    try:
        applied = _apply_concept_patch_core(
            decision_endpoint="/concepts/tournament",
            ir=ir,
            ir_hash=None,
            mode=mode,
            source_text=source_text,
            doc_id=None,
            dry_run=True,
            include_validator_runs=True,
            patch_ops=candidate.patch_ops,
        )
    except HTTPException:
        return None, 0

    candidate_run_inputs = applied.validator_runs or []
    used_solver_calls = 1 if candidate_run_inputs else 0
    remaining_after_apply = max(0, remaining_solver_calls - used_solver_calls)
    concept_runs = [_concept_run_ref_from_input(run) for run in candidate_run_inputs]
    selected = pick_latest_run(concept_runs)

    if selected is None or remaining_after_apply <= 0:
        patched_analysis = unavailable_analysis(details="tournament analysis budget exhausted")
    else:
        mic_budget, forced_budget = _analysis_budget_split(remaining_after_apply)
        patched_analysis = analyze_concept(
            applied.patched_ir,
            run=selected,
            max_shrink_iters=max(1, min(mic_budget, QUESTION_MIC_SHRINK_ITERS_MAX)),
            max_solver_calls=mic_budget,
            max_forced_checks=max(0, forced_budget - 1),
            max_solver_calls_total=forced_budget,
        )
        analysis_solver_calls = (
            patched_analysis.mic.solver_calls + patched_analysis.forced.solver_calls
        )
        used_solver_calls += min(remaining_after_apply, analysis_solver_calls)

    left_backend, left_timeout_ms = _extract_backend_timeout(base_run_inputs)
    right_backend, right_timeout_ms = _extract_backend_timeout(candidate_run_inputs)
    diff_report = build_diff_report(
        ir,
        applied.patched_ir,
        left_id=ir.concept_id,
        right_id=applied.patched_ir.concept_id,
        left_runs=base_run_inputs,
        right_runs=candidate_run_inputs,
        summary_run_source="provided",
        summary_recompute_mode=mode.value,
        summary_left_backend=left_backend,
        summary_right_backend=right_backend,
        summary_left_timeout_ms=left_timeout_ms,
        summary_right_timeout_ms=right_timeout_ms,
    )

    objective = _tournament_objective_vector(
        report=applied.check_report,
        analysis=patched_analysis,
    )
    candidate_id = _tournament_candidate_id(
        base_ir_hash=base_ir_hash,
        question_id=candidate.question_id,
        patch_ops=candidate.patch_ops,
    )

    return (
        _TournamentCandidateEvaluation(
            candidate_id=candidate_id,
            question_id=candidate.question_id,
            patch_ops=candidate.patch_ops,
            objective_vector=objective,
            improved=objective > base_objective,
            check_report=applied.check_report,
            analysis=_analysis_for_response(
                analysis=patched_analysis,
                include_analysis_details=include_analysis_details,
                include_forced_details=include_forced_details,
            ),
            diff_report=diff_report,
            solver_trust="solver_backed" if candidate_run_inputs else "kernel_only",
        ),
        used_solver_calls,
    )


def _analysis_budget_split(remaining_solver_calls: int) -> tuple[int, int]:
    forced_budget = max(
        1,
        min(
            QUESTION_FORCED_BUDGET_MAX,
            remaining_solver_calls // QUESTION_FORCED_BUDGET_DIVISOR,
        ),
    )
    mic_budget = max(0, remaining_solver_calls - forced_budget)
    return mic_budget, forced_budget


def _evaluate_question_answer_dry_run(
    *,
    req: ConceptQuestionsRequest,
    base_report: CheckReport,
    base_analysis: ConceptAnalysis,
    patch_ops: list[JsonPatchOp],
    remaining_solver_calls: int,
) -> tuple[bool, int]:
    if not patch_ops:
        return True, 0

    try:
        applied = _apply_concept_patch_core(
            decision_endpoint="/concepts/questions",
            ir=req.ir,
            ir_hash=None,
            mode=req.mode,
            source_text=req.source_text,
            doc_id=req.doc_id,
            dry_run=True,
            include_validator_runs=True,
            patch_ops=patch_ops,
        )
    except HTTPException:
        return False, 0

    # One check run is consumed by the dry-run apply call.
    used_solver_calls = 1
    remaining_after_check = max(0, remaining_solver_calls - used_solver_calls)

    run_inputs = applied.validator_runs or []
    concept_runs = [_concept_run_ref_from_input(run) for run in run_inputs]
    selected = pick_latest_run(concept_runs)

    if selected is None or remaining_after_check <= 0:
        patched_analysis = unavailable_analysis(details="do-no-harm analysis budget exhausted")
    else:
        mic_budget, forced_budget = _analysis_budget_split(remaining_after_check)
        patched_analysis = analyze_concept(
            applied.patched_ir,
            run=selected,
            max_shrink_iters=max(1, min(mic_budget, QUESTION_MIC_SHRINK_ITERS_MAX)),
            max_solver_calls=mic_budget,
            max_forced_checks=max(0, forced_budget - 1),
            max_solver_calls_total=forced_budget,
        )
        analysis_solver_calls = (
            patched_analysis.mic.solver_calls + patched_analysis.forced.solver_calls
        )
        used_solver_calls += min(remaining_after_check, analysis_solver_calls)

    keep = _is_do_no_harm_improvement(
        base_report=base_report,
        base_analysis=base_analysis,
        patched_report=applied.check_report,
        patched_analysis=patched_analysis,
    )
    return keep, used_solver_calls


def _question_patch_key(patch_ops: list[JsonPatchOp]) -> str:
    payload = [op.model_dump(mode="json", by_alias=True, exclude_none=True) for op in patch_ops]
    return canonical_json(payload)


class _AdeuObjectRef(NamedTuple):
    object_id: str
    json_path: str
    span: Any | None


def _json_path_index(path: str, *, prefix: str) -> int | None:
    if not path.startswith(prefix):
        return None
    token = path[len(prefix) :].split("/", 1)[0]
    if not token:
        return None
    try:
        index = int(token)
    except ValueError:
        return None
    if index < 0:
        return None
    return index


def _concept_object_id_from_anchor(
    *,
    anchor: ConceptQuestionAnchor,
    concept_ir: ConceptIR,
) -> str | None:
    if isinstance(anchor.object_id, str) and anchor.object_id:
        return anchor.object_id

    json_path = anchor.json_path or ""
    for prefix, entries in (
        ("/terms/", concept_ir.terms),
        ("/senses/", concept_ir.senses),
        ("/claims/", concept_ir.claims),
        ("/links/", concept_ir.links),
        ("/ambiguity/", concept_ir.ambiguity),
    ):
        idx = _json_path_index(json_path, prefix=prefix)
        if idx is None:
            continue
        if 0 <= idx < len(entries):
            return entries[idx].id
    return None


def _build_concept_to_adeu_map(bridge_manifest: BridgeManifest) -> dict[str, list[str]]:
    grouped: dict[str, set[str]] = {}
    for entry in bridge_manifest.entries:
        grouped.setdefault(entry.concept_object_id, set()).add(entry.adeu_object_id)
    return {concept_id: sorted(object_ids) for concept_id, object_ids in grouped.items()}


def _build_adeu_object_refs(ir: AdeuIR) -> dict[str, _AdeuObjectRef]:
    refs: dict[str, _AdeuObjectRef] = {}

    def _add_refs_from_items(
        *,
        items: list[Any],
        key_prefix: str,
        json_path_prefix: str,
    ) -> None:
        for idx, item in enumerate(sorted(items, key=lambda entry: entry.id)):
            refs[f"{key_prefix}/{item.id}"] = _AdeuObjectRef(
                object_id=item.id,
                json_path=f"/{json_path_prefix}/{idx}",
                span=item.provenance.span if item.provenance else None,
            )

    _add_refs_from_items(
        items=ir.O.entities,
        key_prefix="O.entities",
        json_path_prefix="O/entities",
    )
    _add_refs_from_items(
        items=ir.O.definitions,
        key_prefix="O.definitions",
        json_path_prefix="O/definitions",
    )
    _add_refs_from_items(
        items=ir.D_norm.statements,
        key_prefix="D_norm.statements",
        json_path_prefix="D_norm/statements",
    )
    _add_refs_from_items(
        items=ir.D_norm.exceptions,
        key_prefix="D_norm.exceptions",
        json_path_prefix="D_norm/exceptions",
    )

    return refs


def _validate_adeu_anchor_span(
    *,
    span: Any | None,
    source_text: str | None,
    question_id: str,
    adeu_object_id: str,
) -> Any | None:
    if source_text is None or span is None:
        return None

    start = getattr(span, "start", None)
    end = getattr(span, "end", None)
    if not isinstance(start, int) or not isinstance(end, int):
        raise HTTPException(
            status_code=400,
            detail={
                "code": "ADEU_QUESTIONS_ANCHOR_UNRESOLVED",
                "message": "anchor span is invalid",
                "question_id": question_id,
                "adeu_object_id": adeu_object_id,
            },
        )

    if start < 0 or end > len(source_text) or start >= end:
        raise HTTPException(
            status_code=400,
            detail={
                "code": "ADEU_QUESTIONS_ANCHOR_UNRESOLVED",
                "message": "anchor span is out of bounds for source_text",
                "question_id": question_id,
                "adeu_object_id": adeu_object_id,
                "span_start": start,
                "span_end": end,
                "source_text_length": len(source_text),
            },
        )
    return span


def _project_concept_questions_to_adeu(
    *,
    questions: list[ConceptQuestion],
    concept_ir: ConceptIR,
    adeu_ir: AdeuIR,
    bridge_manifest: BridgeManifest,
    source_text: str | None,
) -> list[ConceptQuestion]:
    concept_to_adeu = _build_concept_to_adeu_map(bridge_manifest)
    adeu_refs = _build_adeu_object_refs(adeu_ir)

    projected_questions: list[ConceptQuestion] = []
    for question in questions:
        projected_anchors: list[ConceptQuestionAnchor] = []
        seen_keys: set[tuple[str, str, str, int, int]] = set()

        for anchor in question.anchors:
            concept_object_id = _concept_object_id_from_anchor(anchor=anchor, concept_ir=concept_ir)
            if concept_object_id is None:
                raise HTTPException(
                    status_code=400,
                    detail={
                        "code": "ADEU_QUESTIONS_ANCHOR_UNRESOLVED",
                        "message": "could not resolve concept anchor to concept object",
                        "question_id": question.question_id,
                        "concept_json_path": anchor.json_path,
                    },
                )

            adeu_object_keys = concept_to_adeu.get(concept_object_id, [])
            if not adeu_object_keys:
                raise HTTPException(
                    status_code=400,
                    detail={
                        "code": "ADEU_QUESTIONS_ANCHOR_UNRESOLVED",
                        "message": "no ADEU mapping for concept anchor object",
                        "question_id": question.question_id,
                        "concept_object_id": concept_object_id,
                    },
                )

            resolved_count = 0
            for adeu_object_key in adeu_object_keys:
                resolved = adeu_refs.get(adeu_object_key)
                if resolved is None:
                    continue

                span = _validate_adeu_anchor_span(
                    span=resolved.span,
                    source_text=source_text,
                    question_id=question.question_id,
                    adeu_object_id=resolved.object_id,
                )
                start = span.start if span is not None else -1
                end = span.end if span is not None else -1
                dedupe_key = (
                    resolved.object_id,
                    resolved.json_path,
                    anchor.label or "",
                    start,
                    end,
                )
                if dedupe_key in seen_keys:
                    continue
                seen_keys.add(dedupe_key)
                projected_anchors.append(
                    ConceptQuestionAnchor(
                        object_id=resolved.object_id,
                        json_path=resolved.json_path,
                        label=anchor.label,
                        span=span,
                    )
                )
                resolved_count += 1

            if resolved_count == 0:
                raise HTTPException(
                    status_code=400,
                    detail={
                        "code": "ADEU_QUESTIONS_ANCHOR_UNRESOLVED",
                        "message": "ADEU anchor mapping resolved to no concrete ADEU objects",
                        "question_id": question.question_id,
                        "concept_object_id": concept_object_id,
                    },
                )

        if not projected_anchors:
            raise HTTPException(
                status_code=400,
                detail={
                    "code": "ADEU_QUESTIONS_ANCHOR_UNRESOLVED",
                    "message": "question has no resolvable ADEU anchors",
                    "question_id": question.question_id,
                },
            )

        projected_questions.append(question.model_copy(update={"anchors": projected_anchors}))

    return projected_questions


class _DoNoHarmFilterResult(NamedTuple):
    questions: list[ConceptQuestion]
    used_dry_runs: int
    used_solver_calls: int
    truncated: bool
    truncation_reason: str | None


def _filter_question_answers_do_no_harm(
    *,
    req: ConceptQuestionsRequest,
    report: CheckReport,
    analysis: ConceptAnalysis,
    questions: list[ConceptQuestion],
) -> _DoNoHarmFilterResult:
    max_dry_run_evals = MAX_QUESTION_DRY_RUN_EVALS_TOTAL
    max_solver_calls = MAX_QUESTION_SOLVER_CALLS_TOTAL
    remaining_dry_run_evals = max_dry_run_evals
    remaining_solver_calls = max_solver_calls
    patch_cache: dict[str, tuple[bool, int]] = {}
    truncation_reason: str | None = None

    filtered_questions: list[ConceptQuestion] = []
    for question in questions:
        kept_answers: list[AmbiguityOption] = []
        for answer in question.answers:
            patch_ops = answer.patch or []
            if not patch_ops:
                kept_answers.append(answer)
                continue

            patch_key = _question_patch_key(patch_ops)
            cached = patch_cache.get(patch_key)
            if cached is not None:
                keep, _ = cached
                if keep:
                    kept_answers.append(answer)
                continue

            if remaining_dry_run_evals <= 0:
                # Fail closed when out of budget: only keep patch answers that were verified.
                if truncation_reason is None:
                    truncation_reason = QUESTION_TRUNCATION_REASON_DRY_RUN_CAP
                continue
            if remaining_solver_calls <= 0:
                # Fail closed when out of budget: only keep patch answers that were verified.
                if truncation_reason is None:
                    truncation_reason = QUESTION_TRUNCATION_REASON_SOLVER_CALL_CAP
                continue

            keep, used_solver_calls = _evaluate_question_answer_dry_run(
                req=req,
                base_report=report,
                base_analysis=analysis,
                patch_ops=patch_ops,
                remaining_solver_calls=remaining_solver_calls,
            )
            patch_cache[patch_key] = (keep, used_solver_calls)
            remaining_dry_run_evals -= 1
            remaining_solver_calls = max(0, remaining_solver_calls - used_solver_calls)

            if keep:
                kept_answers.append(answer)

        if not kept_answers:
            continue
        filtered_questions.append(question.model_copy(update={"answers": kept_answers}))

    return _DoNoHarmFilterResult(
        questions=filtered_questions,
        used_dry_runs=max_dry_run_evals - remaining_dry_run_evals,
        used_solver_calls=max_solver_calls - remaining_solver_calls,
        truncated=truncation_reason is not None,
        truncation_reason=truncation_reason,
    )


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
    source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.source_text,
        doc_id=req.doc_id,
        require_source=False,
    )
    report, runs = check_concept_with_validator_runs(
        req.ir,
        mode=req.mode,
        source_text=source_text,
    )
    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS") and runs:
        _persist_validator_runs(runs=runs, artifact_id=None)
    return report


@app.post("/concepts/analyze", response_model=ConceptAnalyzeResponse)
def analyze_concept_variant(req: ConceptAnalyzeRequest) -> ConceptAnalyzeResponse:
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


@app.post("/concepts/questions", response_model=ConceptQuestionsResponse)
def concept_questions_endpoint(req: ConceptQuestionsRequest) -> ConceptQuestionsResponse:
    source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.source_text,
        doc_id=req.doc_id,
        require_source=False,
    )
    _require_ir_hash_match(ir=req.ir, ir_hash=req.expected_ir_hash)

    report, records = check_concept_with_validator_runs(
        req.ir,
        mode=req.mode,
        source_text=source_text,
    )

    run_inputs = [_validator_run_input_from_record(record) for record in records]
    concept_runs = [_concept_run_ref_from_input(run) for run in run_inputs]
    selected = pick_latest_run(concept_runs)

    analysis = analyze_concept(req.ir, run=selected)
    if not req.include_forced_details:
        analysis = strip_forced_details(analysis)

    max_questions = DEFAULT_MAX_QUESTIONS
    max_answers = DEFAULT_MAX_ANSWERS_PER_QUESTION
    raw_questions = build_concept_questions(
        req.ir,
        analysis,
        max_questions=max_questions,
        max_answers_per_question=max_answers,
    )
    ranked_questions = _rank_and_dedupe_questions(
        questions=raw_questions,
        analysis=analysis,
        report=report,
        ir=req.ir,
    )
    filtered_result = _filter_question_answers_do_no_harm(
        req=req.model_copy(update={"source_text": source_text, "doc_id": None}),
        report=report,
        analysis=analysis,
        questions=ranked_questions,
    )
    questions = filtered_result.questions[:max_questions]
    truncated = filtered_result.truncated
    truncation_reason = filtered_result.truncation_reason
    if len(filtered_result.questions) > max_questions and truncation_reason is None:
        truncated = True
        truncation_reason = QUESTION_TRUNCATION_REASON_MAX_QUESTIONS

    return ConceptQuestionsResponse(
        check_report=report,
        questions=questions,
        evidence_refs=_build_question_evidence_refs(
            endpoint="/concepts/questions",
            ir_hash=_concept_ir_hash(req.ir),
            runs=run_inputs,
        ),
        question_count=len(questions),
        max_questions=max_questions,
        max_answers_per_question=max_answers,
        question_rank_version=CONCEPTS_QUESTION_RANK_VERSION,
        rationale_version=CONCEPTS_RATIONALE_VERSION,
        budget_report=QuestionsBudgetReport(
            budget_version=QUESTIONS_BUDGET_VERSION,
            max_solver_calls=MAX_QUESTION_SOLVER_CALLS_TOTAL,
            used_solver_calls=filtered_result.used_solver_calls,
            max_dry_runs=MAX_QUESTION_DRY_RUN_EVALS_TOTAL,
            used_dry_runs=filtered_result.used_dry_runs,
            truncated=truncated,
            truncation_reason=truncation_reason,
        ),
        bridge_loss_signals=[],
        mapping_trust=None,
        solver_trust="solver_backed" if records else "kernel_only",
        proof_trust=None,
    )


@app.post("/concepts/tournament", response_model=ConceptTournamentResponse)
def concept_tournament_endpoint(req: ConceptTournamentRequest) -> ConceptTournamentResponse:
    source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.source_text,
        doc_id=req.doc_id,
        require_source=False,
    )
    _require_tournament_ir_hash_match(ir=req.ir, ir_hash=req.expected_ir_hash)

    report, records = check_concept_with_validator_runs(
        req.ir,
        mode=req.mode,
        source_text=source_text,
    )
    base_run_inputs = [_validator_run_input_from_record(record) for record in records]
    concept_runs = [_concept_run_ref_from_input(run) for run in base_run_inputs]
    selected = pick_latest_run(concept_runs)
    base_analysis = analyze_concept(req.ir, run=selected)
    base_objective = _tournament_objective_vector(report=report, analysis=base_analysis)
    base_ir_hash = _concept_ir_hash(req.ir)

    generated_truncated = False
    if req.tournament_mode == "live_generation":
        if req.provider != "mock":
            raise HTTPException(
                status_code=502,
                detail={
                    "code": "TOURNAMENT_PROVIDER_ERROR",
                    "message": f"live_generation provider is unsupported: {req.provider}",
                },
            )
        candidates, generated_truncated = _build_live_tournament_candidates(
            ir=req.ir,
            analysis=base_analysis,
            report=report,
            max_candidates=req.max_candidates,
        )
    else:
        candidates = list(req.candidates or [])

    if not candidates:
        raise HTTPException(
            status_code=400,
            detail={
                "code": "TOURNAMENT_NO_CANDIDATES",
                "message": "no tournament candidates available for evaluation",
            },
        )

    truncation_reason: str | None = None
    if generated_truncated:
        truncation_reason = QUESTION_TRUNCATION_REASON_CANDIDATE_CAP
    if len(candidates) > req.max_candidates:
        candidates = candidates[: req.max_candidates]
        if truncation_reason is None:
            truncation_reason = QUESTION_TRUNCATION_REASON_CANDIDATE_CAP

    max_solver_calls = req.max_solver_calls or MAX_TOURNAMENT_SOLVER_CALLS_TOTAL
    max_dry_runs = req.max_dry_runs or MAX_TOURNAMENT_DRY_RUN_EVALS_TOTAL
    remaining_solver_calls = max_solver_calls
    remaining_dry_runs = max_dry_runs
    evaluations: list[_TournamentCandidateEvaluation] = []

    for candidate in candidates:
        if remaining_dry_runs <= 0:
            truncation_reason = (
                truncation_reason or QUESTION_TRUNCATION_REASON_DRY_RUN_CAP
            )
            break
        if remaining_solver_calls <= 0:
            truncation_reason = (
                truncation_reason or QUESTION_TRUNCATION_REASON_SOLVER_CALL_CAP
            )
            break

        remaining_dry_runs -= 1
        evaluation, used_solver_calls = _evaluate_tournament_candidate(
            ir=req.ir,
            source_text=source_text,
            mode=req.mode,
            base_run_inputs=base_run_inputs,
            base_ir_hash=base_ir_hash,
            base_objective=base_objective,
            candidate=candidate,
            include_analysis_details=req.include_analysis_details,
            include_forced_details=req.include_forced_details,
            remaining_solver_calls=remaining_solver_calls,
        )
        remaining_solver_calls = max(0, remaining_solver_calls - used_solver_calls)
        if evaluation is not None:
            evaluations.append(evaluation)

    if not evaluations:
        raise HTTPException(
            status_code=400,
            detail={
                "code": "TOURNAMENT_NO_CANDIDATES",
                "message": "no evaluable tournament candidates after validation",
            },
        )

    ranked = sorted(evaluations, key=_tournament_rank_key)
    rank_by_id = {candidate.candidate_id: idx for idx, candidate in enumerate(ranked)}
    selected_candidate = next((candidate for candidate in ranked if candidate.improved), None)
    no_safe_improvement = selected_candidate is None
    top_ranked = ranked[: min(req.top_k, len(ranked))]
    used_solver_calls = max_solver_calls - remaining_solver_calls
    used_dry_runs = max_dry_runs - remaining_dry_runs

    return ConceptTournamentResponse(
        tournament_mode=req.tournament_mode,
        provider=req.provider,
        tournament_score_version=TOURNAMENT_SCORE_VERSION,
        base_ir_hash=base_ir_hash,
        base_objective_vector=[*base_objective],
        score_metadata=TournamentScoreMetadata(
            score_version=TOURNAMENT_SCORE_VERSION,
            objective_dimensions=list(TOURNAMENT_OBJECTIVE_DIMENSIONS),
            tie_break_order=TOURNAMENT_TIE_BREAK_ORDER,
        ),
        no_safe_improvement=no_safe_improvement,
        selected_candidate_id=(
            None if selected_candidate is None else selected_candidate.candidate_id
        ),
        candidate_count=len(candidates),
        evaluated_count=len(evaluations),
        candidates=[
            ConceptTournamentCandidateResult(
                candidate_id=item.candidate_id,
                question_id=item.question_id,
                rank=rank_by_id[item.candidate_id],
                improved=item.improved,
                objective_vector=[*item.objective_vector],
                patch_ops=item.patch_ops,
                check_report=item.check_report,
                analysis=item.analysis,
                diff_report=item.diff_report,
                score_version=TOURNAMENT_SCORE_VERSION,
                tie_break_provenance=TournamentTieBreakProvenance(
                    stable_id=item.candidate_id,
                    objective_dimensions=list(TOURNAMENT_OBJECTIVE_DIMENSIONS),
                    tie_break_order=TOURNAMENT_TIE_BREAK_ORDER,
                ),
                bridge_loss_signals=[],
                mapping_trust=None,
                solver_trust=item.solver_trust,
                proof_trust=None,
            )
            for item in top_ranked
        ],
        budget_report=QuestionsBudgetReport(
            budget_version=QUESTIONS_BUDGET_VERSION,
            max_solver_calls=max_solver_calls,
            used_solver_calls=used_solver_calls,
            max_dry_runs=max_dry_runs,
            used_dry_runs=used_dry_runs,
            truncated=truncation_reason is not None,
            truncation_reason=truncation_reason,
        ),
        bridge_loss_signals=[],
        mapping_trust=None,
        solver_trust="solver_backed" if records or used_solver_calls > 0 else "kernel_only",
        proof_trust=None,
    )


@app.post("/adeu/questions", response_model=AdeuQuestionsResponse)
def adeu_questions_endpoint(req: AdeuQuestionsRequest) -> AdeuQuestionsResponse:
    source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.source_text,
        doc_id=None,
        require_source=False,
    )
    _require_adeu_ir_hash_match(ir=req.ir, ir_hash=req.expected_ir_hash)

    lifted = lift_adeu_to_concepts(req.ir)
    bridge_loss_report = build_bridge_loss_report(req.ir)
    bridge_loss_signals = _bridge_loss_signals(bridge_loss_report)
    report, records = check_concept_with_validator_runs(
        lifted.concept_ir,
        mode=req.mode,
        source_text=source_text,
    )
    run_inputs = [_validator_run_input_from_record(record) for record in records]
    concept_runs = [_concept_run_ref_from_input(run) for run in run_inputs]
    selected = pick_latest_run(concept_runs)

    analysis = analyze_concept(lifted.concept_ir, run=selected)
    max_questions = DEFAULT_MAX_QUESTIONS
    max_answers = DEFAULT_MAX_ANSWERS_PER_QUESTION
    raw_questions = build_concept_questions(
        lifted.concept_ir,
        analysis,
        max_questions=max_questions,
        max_answers_per_question=max_answers,
    )
    ranked_questions = _rank_and_dedupe_questions(
        questions=raw_questions,
        analysis=analysis,
        report=report,
        ir=lifted.concept_ir,
    )
    filtered_result = _filter_question_answers_do_no_harm(
        req=ConceptQuestionsRequest(
            ir=lifted.concept_ir,
            source_text=source_text,
            mode=req.mode,
            include_forced_details=True,
        ),
        report=report,
        analysis=analysis,
        questions=ranked_questions,
    )
    limited_questions = filtered_result.questions[:max_questions]
    projected_questions = _project_concept_questions_to_adeu(
        questions=limited_questions,
        concept_ir=lifted.concept_ir,
        adeu_ir=req.ir,
        bridge_manifest=lifted.bridge_manifest,
        source_text=source_text,
    )

    truncated = filtered_result.truncated
    truncation_reason = filtered_result.truncation_reason
    if len(filtered_result.questions) > max_questions and truncation_reason is None:
        truncated = True
        truncation_reason = QUESTION_TRUNCATION_REASON_MAX_QUESTIONS

    return AdeuQuestionsResponse(
        check_report=report,
        questions=projected_questions,
        evidence_refs=_build_question_evidence_refs(
            endpoint="/adeu/questions",
            ir_hash=_adeu_ir_hash(req.ir),
            runs=run_inputs,
        ),
        question_count=len(projected_questions),
        max_questions=max_questions,
        max_answers_per_question=max_answers,
        question_rank_version=ADEU_QUESTION_RANK_VERSION,
        rationale_version=ADEU_RATIONALE_VERSION,
        bridge_manifest=lifted.bridge_manifest,
        bridge_mapping_version=lifted.bridge_mapping_version,
        mapping_hash=lifted.mapping_hash,
        bridge_loss_signals=bridge_loss_signals,
        budget_report=QuestionsBudgetReport(
            budget_version=QUESTIONS_BUDGET_VERSION,
            max_solver_calls=MAX_QUESTION_SOLVER_CALLS_TOTAL,
            used_solver_calls=filtered_result.used_solver_calls,
            max_dry_runs=MAX_QUESTION_DRY_RUN_EVALS_TOTAL,
            used_dry_runs=filtered_result.used_dry_runs,
            truncated=truncated,
            truncation_reason=truncation_reason,
        ),
        mapping_trust="derived_bridge",
        solver_trust="solver_backed" if records else "kernel_only",
        proof_trust=None,
        validator_runs=run_inputs if req.include_validator_runs else None,
        analysis=analysis if req.include_analysis_details else None,
    )


@app.post("/adeu/analyze_concepts", response_model=AdeuAnalyzeConceptsResponse)
def analyze_adeu_as_concepts(req: AdeuAnalyzeConceptsRequest) -> AdeuAnalyzeConceptsResponse:
    source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.source_text,
        doc_id=req.doc_id,
        require_source=False,
    )

    lifted = lift_adeu_to_concepts(req.ir)
    report, records = check_concept_with_validator_runs(
        lifted.concept_ir,
        mode=req.mode,
        source_text=source_text,
    )
    if _env_flag("ADEU_PERSIST_VALIDATOR_RUNS") and records:
        _persist_validator_runs(runs=records, artifact_id=None)
    run_inputs = [_validator_run_input_from_record(record) for record in records]
    concept_runs = [_concept_run_ref_from_input(run) for run in run_inputs]
    selected = pick_latest_run(concept_runs)
    analysis = analyze_concept(lifted.concept_ir, run=selected)
    if not req.include_analysis_details:
        analysis = strip_analysis_details(analysis)
    elif not req.include_forced_details:
        analysis = strip_forced_details(analysis)

    return AdeuAnalyzeConceptsResponse(
        concept_ir=lifted.concept_ir,
        check_report=report,
        analysis=analysis,
        bridge_manifest=lifted.bridge_manifest,
        bridge_loss_report=build_bridge_loss_report(req.ir),
        bridge_mapping_version=lifted.bridge_mapping_version,
        mapping_hash=lifted.mapping_hash,
        mapping_trust="derived_bridge",
        solver_trust="solver_backed" if records else "kernel_only",
        proof_trust=None,
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
    source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.source_text,
        doc_id=req.doc_id,
        require_source=True,
    )
    assert source_text is not None
    source_text = source_text.strip()
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


@app.post("/documents", response_model=DocumentResponse)
def create_document_endpoint(req: DocumentCreateRequest) -> DocumentResponse:
    _enforce_source_text_size(req.source_text)
    try:
        row = create_document(
            doc_id=req.doc_id,
            domain=req.domain,
            source_text=req.source_text,
            metadata_json=req.metadata or {},
        )
    except ValueError as exc:
        raise HTTPException(
            status_code=409,
            detail={
                "code": "DOC_ALREADY_EXISTS",
                "message": str(exc),
                "doc_id": req.doc_id,
            },
        ) from exc
    return DocumentResponse(
        doc_id=row.doc_id,
        domain=row.domain,
        source_text=row.source_text,
        created_at=row.created_at,
        metadata=row.metadata_json,
    )


@app.get("/documents/{doc_id}", response_model=DocumentResponse)
def get_document_endpoint(doc_id: str) -> DocumentResponse:
    row = get_document(doc_id=doc_id)
    if row is None:
        raise HTTPException(
            status_code=404,
            detail={
                "code": "DOC_NOT_FOUND",
                "message": f"document not found for doc_id={doc_id!r}",
                "doc_id": doc_id,
            },
        )
    return DocumentResponse(
        doc_id=row.doc_id,
        domain=row.domain,
        source_text=row.source_text,
        created_at=row.created_at,
        metadata=row.metadata_json,
    )


@app.get("/documents", response_model=DocumentListResponse)
def list_documents_endpoint(
    domain: str | None = None,
    created_after: str | None = None,
    created_before: str | None = None,
    limit: int = Query(DEFAULT_LIST_LIMIT, ge=1, le=MAX_LIST_LIMIT),
    offset: int = Query(0, ge=0, le=MAX_LIST_OFFSET),
) -> DocumentListResponse:
    try:
        rows = list_documents(
            domain=domain,
            created_after=created_after,
            created_before=created_before,
            limit=limit,
            offset=offset,
        )
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return DocumentListResponse(
        items=[
            DocumentSummary(
                doc_id=row.doc_id,
                domain=row.domain,
                created_at=row.created_at,
            )
            for row in rows
        ]
    )


@app.post("/concepts/artifacts", response_model=ConceptArtifactCreateResponse)
def create_concept_artifact_endpoint(
    req: ConceptArtifactCreateRequest,
) -> ConceptArtifactCreateResponse:
    source_text, resolved_doc_id = _resolve_source_text_and_doc_id(
        source_text=req.source_text,
        doc_id=req.doc_id,
        require_source=True,
    )
    assert source_text is not None
    report, runs = check_concept_with_validator_runs(
        req.ir,
        mode=req.mode,
        source_text=source_text,
    )
    if report.status == "REFUSE":
        raise HTTPException(status_code=400, detail="refused by kernel")

    num_errors = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.ERROR)
    num_warns = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.WARN)
    run_inputs = [_validator_run_input_from_record(record) for record in runs]
    concept_runs = [_concept_run_ref_from_input(run) for run in run_inputs]
    selected = pick_latest_run(concept_runs)
    analysis = analyze_concept(req.ir, run=selected) if selected is not None else None

    with storage_transaction() as connection:
        row = create_concept_artifact(
            schema_version=req.ir.schema_version,
            artifact_version=1,
            source_text=source_text,
            doc_id=resolved_doc_id if resolved_doc_id is not None else req.ir.context.doc_id,
            status=report.status,
            num_errors=num_errors,
            num_warns=num_warns,
            ir_json=req.ir.model_dump(mode="json", exclude_none=True),
            check_report_json=report.model_dump(mode="json", exclude_none=True),
            analysis_json=analysis.model_dump(mode="json", exclude_none=True) if analysis else None,
            connection=connection,
        )
        if runs:
            _persist_validator_runs(
                runs=runs,
                artifact_id=None,
                concept_artifact_id=row.artifact_id,
                connection=connection,
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
    limit: int = Query(DEFAULT_LIST_LIMIT, ge=1, le=MAX_LIST_LIMIT),
    offset: int = Query(0, ge=0, le=MAX_LIST_OFFSET),
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


@app.post("/concepts/align", response_model=ConceptAlignResponse)
def align_concepts_endpoint(req: ConceptAlignRequest) -> ConceptAlignResponse:
    artifact_ids = _resolve_alignment_artifact_ids(req)
    artifacts = _collect_alignment_artifacts(artifact_ids)
    suggestions = _build_alignment_suggestions(
        artifacts,
        max_suggestions=req.max_suggestions,
    )
    return ConceptAlignResponse(
        artifacts=[
            ConceptAlignmentArtifactRef(
                artifact_id=artifact_id,
                doc_id=doc_id,
                concept_id=concept.concept_id,
            )
            for artifact_id, doc_id, concept in artifacts
        ],
        suggestion_count=len(suggestions),
        suggestions=suggestions,
        alignment_stats=_alignment_stats(suggestions),
        coherence_diagnostics=_alignment_coherence_diagnostics(suggestions),
        mapping_trust="derived_alignment",
        solver_trust="kernel_only",
        proof_trust=None,
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
    left_source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.left_source_text,
        doc_id=req.left_doc_id,
        require_source=False,
        source_field="left_source_text",
    )
    right_source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.right_source_text,
        doc_id=req.right_doc_id,
        require_source=False,
        source_field="right_source_text",
    )
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
            source_text=left_source_text,
        ),
        right_recompute_fn=lambda: check_concept_with_validator_runs(
            req.right_ir,
            mode=req.mode,
            source_text=right_source_text,
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

    left_source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.left_source_text,
        doc_id=req.left_doc_id,
        require_source=False,
        source_field="left_source_text",
    )
    right_source_text, _ = _resolve_source_text_and_doc_id(
        source_text=req.right_source_text,
        doc_id=req.right_doc_id,
        require_source=False,
        source_field="right_source_text",
    )

    left_runs, left_source, left_report, left_mismatch, _ = _resolve_explain_runs(
        inline_runs=req.left_validator_runs,
        recompute_fn=lambda: check_concept_with_validator_runs(
            req.left_ir,
            mode=req.mode,
            source_text=left_source_text,
        ),
    )
    right_runs, right_source, right_report, right_mismatch, _ = _resolve_explain_runs(
        inline_runs=req.right_validator_runs,
        recompute_fn=lambda: check_concept_with_validator_runs(
            req.right_ir,
            mode=req.mode,
            source_text=right_source_text,
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
            source_text=left_source_text,
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
            source_text=left_source_text,
            solver_status=None,
            solver_error=None,
            solver_unsat_core=None,
        )

    if req.right_validator_runs is not None:
        right_report = check_concept_with_solver_status(
            req.right_ir,
            mode=req.mode,
            source_text=right_source_text,
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
            source_text=right_source_text,
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
            else DEFAULT_EXPLAIN_ANALYSIS_BUDGET
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


@app.post(
    "/concepts/apply_ambiguity_option",
    response_model=ConceptApplyAmbiguityOptionResponse,
)
def apply_concept_ambiguity_option_endpoint(
    req: ConceptApplyAmbiguityOptionRequest,
) -> ConceptApplyAmbiguityOptionResponse:
    try:
        patched = apply_concept_ambiguity_option(
            req.ir,
            ambiguity_id=req.ambiguity_id,
            option_id=req.option_id,
            variants_by_id=req.variants_by_id,
        )
    except ConceptPatchValidationError as exc:
        raise HTTPException(
            status_code=400,
            detail=_concept_patch_http_error_detail(exc),
        ) from exc

    return _apply_concept_patch_core(
        decision_endpoint="/concepts/apply_ambiguity_option",
        ir=req.ir,
        ir_hash=req.ir_hash,
        mode=req.mode,
        source_text=req.source_text,
        doc_id=req.doc_id,
        dry_run=req.dry_run,
        include_validator_runs=req.include_validator_runs,
        patched_ir=patched,
    )


@app.post("/concepts/apply_patch", response_model=ConceptApplyAmbiguityOptionResponse)
def apply_concept_patch_endpoint(
    req: ConceptApplyPatchRequest,
) -> ConceptApplyAmbiguityOptionResponse:
    return _apply_concept_patch_core(
        decision_endpoint="/concepts/apply_patch",
        ir=req.ir,
        ir_hash=req.ir_hash,
        mode=req.mode,
        source_text=req.source_text,
        doc_id=req.doc_id,
        dry_run=req.dry_run,
        include_validator_runs=req.include_validator_runs,
        patch_ops=req.patch_ops,
    )


@app.post("/artifacts", response_model=ArtifactCreateResponse)
def create_artifact_endpoint(req: ArtifactCreateRequest) -> ArtifactCreateResponse:
    report, runs = check_with_validator_runs(req.ir, mode=req.mode)
    if report.status == "REFUSE":
        raise HTTPException(status_code=400, detail="refused by kernel")

    num_errors = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.ERROR)
    num_warns = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.WARN)
    proof_rows: list[ProofArtifactRow] = []

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
        proof_rows = _persist_proof_artifact(
            artifact_id=row.artifact_id,
            ir=req.ir,
            runs=runs,
            connection=connection,
        )
    solver_trust, proof_trust = _artifact_trust_labels(
        validator_runs=runs,
        proof_rows=proof_rows,
    )
    return ArtifactCreateResponse(
        artifact_id=row.artifact_id,
        created_at=row.created_at,
        check_report=report,
        solver_trust=solver_trust,
        proof_trust=proof_trust,
    )


@app.get("/artifacts", response_model=ArtifactListResponse)
def list_artifacts_endpoint(
    doc_id: str | None = None,
    status: Literal["PASS", "WARN", "REFUSE"] | None = None,
    created_after: str | None = None,
    created_before: str | None = None,
    limit: int = Query(DEFAULT_LIST_LIMIT, ge=1, le=MAX_LIST_LIMIT),
    offset: int = Query(0, ge=0, le=MAX_LIST_OFFSET),
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

    artifact_ids = [row.artifact_id for row in items]
    validator_rows_by_artifact = list_validator_runs_for_artifacts(artifact_ids=artifact_ids)
    proof_rows_by_artifact = list_proof_artifacts_for_artifacts(artifact_ids=artifact_ids)

    summaries: list[ArtifactSummary] = []
    for row in items:
        validator_rows = validator_rows_by_artifact.get(row.artifact_id, [])
        proof_rows = proof_rows_by_artifact.get(row.artifact_id, [])
        solver_trust, proof_trust = _artifact_trust_labels(
            validator_runs=validator_rows,
            proof_rows=proof_rows,
        )
        summaries.append(
            ArtifactSummary(
                artifact_id=row.artifact_id,
                created_at=row.created_at,
                doc_id=row.doc_id,
                jurisdiction=row.jurisdiction,
                status=row.status,
                num_errors=row.num_errors,
                num_warns=row.num_warns,
                solver_trust=solver_trust,
                proof_trust=proof_trust,
            )
        )

    return ArtifactListResponse(
        items=summaries
    )


@app.get("/artifacts/{artifact_id}", response_model=ArtifactGetResponse)
def get_artifact_endpoint(artifact_id: str) -> ArtifactGetResponse:
    row = get_artifact(artifact_id=artifact_id)
    if row is None:
        raise HTTPException(status_code=404, detail="not found")
    validator_rows = list_validator_runs(artifact_id=artifact_id)
    proof_rows = list_proof_artifacts(artifact_id=artifact_id)
    solver_trust, proof_trust = _artifact_trust_labels(
        validator_runs=validator_rows,
        proof_rows=proof_rows,
    )
    return ArtifactGetResponse(
        artifact_id=row.artifact_id,
        created_at=row.created_at,
        clause_text=row.clause_text,
        ir=AdeuIR.model_validate(row.ir_json),
        check_report=CheckReport.model_validate(row.check_report_json),
        solver_trust=solver_trust,
        proof_trust=proof_trust,
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
