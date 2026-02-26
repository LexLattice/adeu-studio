from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

CoreIRProposalSchemaVersion = Literal["adeu_core_ir_proposal@0.1"]
CoreIRProposalProviderKind = Literal["mock", "openai", "codex"]
ADEU_CORE_IR_PROPOSAL_SCHEMA = "adeu_core_ir_proposal@0.1"


class CoreIRProposalNotProducedReason(BaseModel):
    model_config = ConfigDict(extra="forbid")

    artifact_family: str = Field(min_length=1)
    reason_code: str = Field(min_length=1)
    message: str | None = None


class CoreIRProposalSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    candidate_count: int = Field(ge=0)
    assertion_node_count: int = Field(ge=0)
    relation_edge_count: int = Field(ge=0)
    logic_tree_max_depth: int = Field(ge=0)
    lane_ref_count: int = Field(ge=0)
    integrity_ref_count: int = Field(ge=0)


class AdeuCoreIRProposal(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: CoreIRProposalSchemaVersion = ADEU_CORE_IR_PROPOSAL_SCHEMA
    client_request_id: str = Field(min_length=1)
    surface_id: Literal["adeu_core_ir.propose"] = "adeu_core_ir.propose"
    provider: CoreIRProposalProviderKind
    core_ir_artifact_ref: str = Field(min_length=1)
    lane_artifact_refs: list[str] = Field(default_factory=list)
    integrity_artifact_refs: list[str] = Field(default_factory=list)
    not_produced_reasons: list[CoreIRProposalNotProducedReason] = Field(default_factory=list)
    summary: CoreIRProposalSummary

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuCoreIRProposal":
        if any(not value for value in self.lane_artifact_refs):
            raise ValueError("lane_artifact_refs must not contain empty refs")
        if self.lane_artifact_refs != sorted(self.lane_artifact_refs):
            raise ValueError("lane_artifact_refs must be lexicographically sorted")
        if len(set(self.lane_artifact_refs)) != len(self.lane_artifact_refs):
            raise ValueError("lane_artifact_refs must not contain duplicates")

        if any(not value for value in self.integrity_artifact_refs):
            raise ValueError("integrity_artifact_refs must not contain empty refs")
        if self.integrity_artifact_refs != sorted(self.integrity_artifact_refs):
            raise ValueError("integrity_artifact_refs must be lexicographically sorted")
        if len(set(self.integrity_artifact_refs)) != len(self.integrity_artifact_refs):
            raise ValueError("integrity_artifact_refs must not contain duplicates")

        reason_pairs = [
            (reason.artifact_family, reason.reason_code) for reason in self.not_produced_reasons
        ]
        if reason_pairs != sorted(reason_pairs):
            raise ValueError(
                "not_produced_reasons must be lexicographically sorted by artifact_family/reason_code"
            )
        if len(set(reason_pairs)) != len(reason_pairs):
            raise ValueError("not_produced_reasons must not contain duplicate entries")

        if self.summary.lane_ref_count != len(self.lane_artifact_refs):
            raise ValueError("summary.lane_ref_count must match lane_artifact_refs")
        if self.summary.integrity_ref_count != len(self.integrity_artifact_refs):
            raise ValueError("summary.integrity_ref_count must match integrity_artifact_refs")
        return self


def canonicalize_core_ir_proposal_payload(payload: AdeuCoreIRProposal | dict[str, Any]) -> dict[str, Any]:
    normalized = (
        payload if isinstance(payload, AdeuCoreIRProposal) else AdeuCoreIRProposal.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
