from __future__ import annotations

from typing import Any, Literal

from adeu_ir import ProofInput
from pydantic import BaseModel, ConfigDict, Field

LeanResultStatus = Literal["proved", "failed"]
DEFAULT_SEMANTICS_VERSION = "adeu.lean.core.v1"
OBLIGATION_KINDS = (
    "pred_closed_world",
    "exception_gating",
    "conflict_soundness",
)


class LeanRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    theorem_id: str = Field(min_length=1)
    theorem_src: str = Field(min_length=1)
    semantics_version: str = DEFAULT_SEMANTICS_VERSION
    obligation_kind: str | None = None
    inputs: list[ProofInput] = Field(default_factory=list)
    metadata: dict[str, Any] = Field(default_factory=dict)


class LeanResult(BaseModel):
    model_config = ConfigDict(extra="forbid")
    theorem_id: str = Field(min_length=1)
    status: LeanResultStatus
    proof_hash: str = Field(min_length=1)
    lean_version: str | None = None
    details: dict[str, Any] = Field(default_factory=dict)
