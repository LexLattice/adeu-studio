from __future__ import annotations

from typing import Literal

from adeu_paper_semantics import (
    ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA,
    PaperSemanticWorkerRequest,
)
from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.domain_registry import WarrantTag as DomainWarrantTag
from urm_runtime.hashing import sha256_canonical_json

WarrantTag = DomainWarrantTag
ADEU_PAPER_SEMANTIC_WORKER_BRIDGE_RESULT_SCHEMA = "adeu_paper_semantic_worker_bridge_result@1"
SEMANTIC_DECOMPOSITION_TEMPLATE_ID = "paper.semantic_decomposition.v0"
SEMANTIC_DECOMPOSITION_TOOL_NAME = "paper.run_semantic_decomposition"
SEMANTIC_DECOMPOSITION_TEMPLATE_VERSION = "v0"

BridgeStatus = Literal[
    "completed_checked",
    "completed_checked_idempotent_replay",
    "fail_closed_invalid_request",
    "fail_closed_bridge_config_mismatch",
]


class PaperTemplateMeta(BaseModel):
    model_config = ConfigDict(extra="forbid")

    template_id: str = Field(min_length=1)
    template_version: str = Field(min_length=1)
    schema_version: str = Field(min_length=1)
    domain_pack_id: str = Field(min_length=1)
    domain_pack_version: str = Field(min_length=1)
    role: str = Field(min_length=1)
    description: str = Field(min_length=1)


class IngestTextArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_text: str = Field(min_length=1)
    title: str | None = Field(default=None, min_length=1)


class ExtractAbstractArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_text: str = Field(min_length=1)


class CheckConstraintsArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    abstract_text: str = Field(min_length=1)
    min_words: int = Field(default=30, ge=1, le=500)
    max_words: int = Field(default=300, ge=1, le=1000)


class EmitArtifactArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    title: str | None = Field(default=None, min_length=1)
    abstract_text: str = Field(min_length=1)
    checks: dict[str, bool] = Field(default_factory=dict)


def compute_bridge_result_id(bridge_hash: str) -> str:
    return f"paper_semantic_bridge:{bridge_hash[:16]}"


class RunSemanticDecompositionArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    worker_request: PaperSemanticWorkerRequest


class PaperSemanticWorkerBridgeResult(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal[ADEU_PAPER_SEMANTIC_WORKER_BRIDGE_RESULT_SCHEMA] = Field(
        default=ADEU_PAPER_SEMANTIC_WORKER_BRIDGE_RESULT_SCHEMA,
        alias="schema",
    )
    bridge_result_id: str
    bridge_status: BridgeStatus
    request_ref: str | None = None
    request_hash: str | None = None
    tool_name: Literal[SEMANTIC_DECOMPOSITION_TOOL_NAME] = SEMANTIC_DECOMPOSITION_TOOL_NAME
    template_id: Literal[SEMANTIC_DECOMPOSITION_TEMPLATE_ID] = SEMANTIC_DECOMPOSITION_TEMPLATE_ID
    template_version: Literal[SEMANTIC_DECOMPOSITION_TEMPLATE_VERSION] = (
        SEMANTIC_DECOMPOSITION_TEMPLATE_VERSION
    )
    domain_pack_id: str = Field(min_length=1)
    domain_pack_version: str = Field(min_length=1)
    provider: Literal["codex"] = "codex"
    role: Literal["pipeline_worker"] = "pipeline_worker"
    warrant_tag: Literal["checked"] = "checked"
    artifact_ref: str | None = None
    worker_id: str | None = None
    evidence_id: str | None = None
    worker_status: Literal["ok", "failed", "cancelled"] | None = None
    idempotent_replay: bool = False
    return_schema: Literal[ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA] = (
        ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA
    )
    bridge_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticWorkerBridgeResult":
        if self.bridge_status == "completed_checked":
            if self.idempotent_replay:
                raise ValueError("completed_checked may not set idempotent_replay")
        elif self.bridge_status == "completed_checked_idempotent_replay":
            if not self.idempotent_replay:
                raise ValueError("completed_checked_idempotent_replay requires idempotent_replay")
        else:
            if self.bridge_status == "fail_closed_invalid_request" and self.worker_id is not None:
                raise ValueError("invalid requests may not carry worker refs")
            if self.bridge_status == "fail_closed_invalid_request" and self.evidence_id is not None:
                raise ValueError("invalid requests may not carry evidence refs")
            if (
                self.bridge_status == "fail_closed_invalid_request"
                and self.worker_status is not None
            ):
                raise ValueError("invalid requests may not carry worker status")
            if (
                self.bridge_status == "fail_closed_invalid_request"
                and self.artifact_ref is not None
            ):
                raise ValueError("invalid requests may not carry artifact refs")
        if self.artifact_ref is not None and self.worker_status != "ok":
            raise ValueError("artifact_ref requires worker_status ok")
        if self.worker_status is not None and (self.worker_id is None or self.evidence_id is None):
            raise ValueError("worker_status requires worker_id and evidence_id")
        basis = self.model_dump(
            mode="json",
            by_alias=True,
            exclude={"bridge_result_id", "bridge_hash"},
            exclude_none=False,
        )
        expected_bridge_hash = sha256_canonical_json(basis)
        if self.bridge_hash != expected_bridge_hash:
            raise ValueError("bridge_hash must match canonical bridge payload")
        expected_bridge_result_id = compute_bridge_result_id(self.bridge_hash)
        if self.bridge_result_id != expected_bridge_result_id:
            raise ValueError("bridge_result_id must match canonical bridge identity")
        return self
