from __future__ import annotations

from datetime import datetime, timezone
from typing import Literal

from adeu_ir import AdeuIR, CheckReport, Context, ReasonSeverity, TraceItem
from adeu_kernel import KernelMode, PatchValidationError, apply_ambiguity_option, check
from fastapi import FastAPI, HTTPException, Query
from pydantic import BaseModel, ConfigDict, Field

from .id_canonicalization import canonicalize_ir_ids
from .mock_provider import load_fixture_bundles
from .scoring import ranking_sort_key, score_key
from .source_features import extract_source_features
from .storage import create_artifact, get_artifact, list_artifacts


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


app = FastAPI(title="ADEU Studio API")


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
    return check(req.ir, mode=req.mode)


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
    report = check(req.ir, mode=req.mode)
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


@app.get("/healthz")
def healthz() -> dict[str, str]:
    return {"status": "ok"}
