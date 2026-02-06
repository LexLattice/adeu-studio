from __future__ import annotations

import hashlib
import os
from datetime import datetime, timezone
from typing import Any, Literal

from adeu_explain import DiffReport, ValidatorRunInput, build_diff_report
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

from .id_canonicalization import canonicalize_ir_ids
from .mock_provider import load_fixture_bundles
from .puzzle_id_canonicalization import canonicalize_puzzle_ids
from .puzzle_mock_provider import get_puzzle_fixture_bundle
from .puzzle_source_features import extract_puzzle_source_features
from .scoring import ranking_sort_key, score_key
from .source_features import extract_source_features
from .storage import (
    create_artifact,
    create_proof_artifact,
    create_validator_run,
    get_artifact,
    list_artifacts,
    list_proof_artifacts,
    list_validator_runs,
)


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


class PuzzleProposeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    puzzle_text: str = Field(min_length=1)
    provider: Literal["mock", "openai"] = "mock"
    mode: KernelMode = KernelMode.LAX
    context_override: dict[str, Any] | None = None
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
    left_validator_runs: list[ValidatorRunInput] | None = None
    right_validator_runs: list[ValidatorRunInput] | None = None
    left_artifact_id: str | None = None
    right_artifact_id: str | None = None


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


def _env_flag(name: str) -> bool:
    return os.environ.get(name, "").strip() == "1"


def _persist_validator_runs(
    *,
    runs: list[ValidatorRunRecord],
    artifact_id: str | None,
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
            backend=run.result.backend,
            backend_version=run.result.backend_version,
            timeout_ms=run.result.timeout_ms,
            options_json=run.result.options,
            request_hash=run.result.request_hash,
            formula_hash=run.result.formula_hash,
            status=run.result.status,
            evidence_json=run.result.evidence.model_dump(mode="json", exclude_none=True),
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


@app.post("/diff", response_model=DiffReport)
def diff_endpoint(req: DiffRequest) -> DiffReport:
    # v1 precedence lock: inline runs win and DB lookup is intentionally out of scope.
    left_runs = req.left_validator_runs if req.left_validator_runs is not None else []
    right_runs = req.right_validator_runs if req.right_validator_runs is not None else []
    return build_diff_report(
        req.left_ir,
        req.right_ir,
        left_id=req.left_ir.ir_id,
        right_id=req.right_ir.ir_id,
        left_runs=left_runs,
        right_runs=right_runs,
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

    row = create_artifact(
        clause_text=req.clause_text,
        doc_id=req.ir.context.doc_id,
        jurisdiction=req.ir.context.jurisdiction,
        status=report.status,
        num_errors=num_errors,
        num_warns=num_warns,
        ir_json=req.ir.model_dump(mode="json", exclude_none=True),
        check_report_json=report.model_dump(mode="json", exclude_none=True),
    )
    if runs:
        _persist_validator_runs(runs=runs, artifact_id=row.artifact_id)
    _persist_proof_artifact(artifact_id=row.artifact_id, ir=req.ir, runs=runs)
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
