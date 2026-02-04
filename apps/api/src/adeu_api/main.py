from __future__ import annotations

from typing import Any, Literal

from adeu_ir import CheckReport
from adeu_kernel import KernelMode, check
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel, Field

from .mock_provider import load_fixture_bundles
from .storage import create_artifact, get_artifact


class ProposeRequest(BaseModel):
    clause_text: str = Field(min_length=1)
    provider: Literal["mock"] = "mock"


class ProposeResponse(BaseModel):
    candidates: list[dict[str, Any]]
    provider: str


class CheckRequest(BaseModel):
    ir: dict[str, Any]
    mode: KernelMode = KernelMode.LAX


class ArtifactCreateRequest(BaseModel):
    clause_text: str = Field(min_length=1)
    ir: dict[str, Any]
    mode: KernelMode = KernelMode.STRICT


class ArtifactCreateResponse(BaseModel):
    artifact_id: str
    created_at: str
    check_report: dict[str, Any]


class ArtifactGetResponse(BaseModel):
    artifact_id: str
    created_at: str
    clause_text: str
    ir: dict[str, Any]
    check_report: dict[str, Any]


app = FastAPI(title="ADEU Studio API")


@app.post("/propose", response_model=ProposeResponse)
def propose(req: ProposeRequest) -> ProposeResponse:
    bundles = load_fixture_bundles()
    clause = req.clause_text.strip()
    bundle = bundles.get(clause)
    if bundle is None:
        return ProposeResponse(candidates=[], provider="mock")

    return ProposeResponse(
        candidates=[c.model_dump(mode="json", exclude_none=True) for c in bundle.proposals],
        provider="mock",
    )


@app.post("/check", response_model=CheckReport)
def check_variant(req: CheckRequest) -> CheckReport:
    return check(req.ir, mode=req.mode)


@app.post("/artifacts", response_model=ArtifactCreateResponse)
def create_artifact_endpoint(req: ArtifactCreateRequest) -> ArtifactCreateResponse:
    report = check(req.ir, mode=req.mode)
    if report.status == "REFUSE":
        raise HTTPException(status_code=400, detail="refused by kernel")

    row = create_artifact(
        clause_text=req.clause_text,
        ir_json=req.ir,
        check_report_json=report.model_dump(mode="json", exclude_none=True),
    )
    return ArtifactCreateResponse(
        artifact_id=row.artifact_id,
        created_at=row.created_at,
        check_report=row.check_report_json,
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
        ir=row.ir_json,
        check_report=row.check_report_json,
    )


@app.get("/healthz")
def healthz() -> dict[str, str]:
    return {"status": "ok"}
