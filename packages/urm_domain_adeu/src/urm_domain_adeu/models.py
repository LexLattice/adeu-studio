from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field
from urm_runtime.domain_registry import WarrantTag as DomainWarrantTag

WarrantTag = DomainWarrantTag


class TemplateMeta(BaseModel):
    model_config = ConfigDict(extra="forbid")

    template_id: str = Field(min_length=1)
    template_version: str = Field(min_length=1)
    schema_version: str = Field(min_length=1)
    domain_pack_id: str = Field(min_length=1)
    domain_pack_version: str = Field(min_length=1)
    role: str = Field(min_length=1)
    description: str = Field(min_length=1)


class AppStateSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid")

    counts: dict[str, int] = Field(default_factory=dict)
    active_copilot_session_id: str | None = None
    active_copilot_writes_allowed: bool = False
    codex_version: str | None = None
    codex_exec_available: bool | None = None
    codex_app_server_available: bool | None = None


class WorkflowRunRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    worker_id: str
    evidence_id: str
    status: Literal["ok", "failed", "cancelled"]
    template_id: str
    template_version: str


class EvidenceBundle(BaseModel):
    model_config = ConfigDict(extra="forbid")

    evidence_id: str
    source: str
    role: str
    status: str
    started_at: str
    ended_at: str | None = None
    raw_jsonl_path: str | None = None
    raw_jsonl: str | None = None
    purged: bool = False
    metadata: dict[str, Any] = Field(default_factory=dict)
    error: dict[str, Any] | None = None


class RunWorkflowArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    template_id: str = Field(min_length=1)
    inputs: dict[str, Any] = Field(default_factory=dict)
    mode: Literal["read_only", "writes_allowed"] = "read_only"
    client_request_id: str | None = None
    output_schema_path: str | None = None
    cwd: str | None = None
    timeout_secs: int = Field(default=120, ge=1, le=6 * 60 * 60)


class ReadEvidenceArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    evidence_id: str = Field(min_length=1)
    max_bytes: int = Field(default=200_000, ge=1, le=5_000_000)
