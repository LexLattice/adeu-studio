from __future__ import annotations

from datetime import datetime
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field


class TaskEnvelope(BaseModel):
    model_config = ConfigDict(extra="forbid")

    role: str = Field(min_length=1)
    template_id: str = Field(min_length=1)
    template_version: str | None = None
    schema_version: str | None = None
    domain_pack_id: str | None = None
    domain_pack_version: str | None = None
    inputs: dict[str, Any] = Field(default_factory=dict)
    constraints: dict[str, Any] = Field(default_factory=dict)


class WorkerRunRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    role: str = "pipeline_worker"
    client_request_id: str = Field(min_length=1)
    prompt: str = Field(min_length=1)
    output_schema_path: str | None = None
    cwd: str | None = None
    timeout_secs: int = Field(default=120, ge=1, le=6 * 60 * 60)
    template_id: str | None = None
    template_version: str | None = None
    schema_version: str | None = None
    domain_pack_id: str | None = None
    domain_pack_version: str | None = None

    def idempotency_payload(self) -> dict[str, Any]:
        payload = self.model_dump(mode="json", exclude={"client_request_id"})
        return payload


class NormalizedEvent(BaseModel):
    model_config = ConfigDict(extra="forbid")

    seq: int
    ts: datetime
    source: Literal["worker_exec", "copilot_app_server"]
    event_kind: str
    payload: dict[str, Any] = Field(default_factory=dict)
    raw_line: str


class WorkerRunResult(BaseModel):
    model_config = ConfigDict(extra="forbid")

    worker_id: str
    status: Literal["ok", "failed", "cancelled"]
    exit_code: int | None = None
    evidence_id: str
    raw_jsonl_path: str
    normalized_event_count: int
    artifact_candidate: Any | None = None
    parse_degraded: bool = False
    error: dict[str, Any] | None = None
    idempotent_replay: bool = False


class CopilotSessionStartRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    client_request_id: str = Field(min_length=1)
    cwd: str | None = None

    def idempotency_payload(self) -> dict[str, Any]:
        return self.model_dump(mode="json", exclude={"client_request_id"})


class CopilotSessionSendRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    session_id: str = Field(min_length=1)
    client_request_id: str = Field(min_length=1)
    message: dict[str, Any]

    def idempotency_payload(self) -> dict[str, Any]:
        return self.model_dump(mode="json", exclude={"client_request_id"})


class CopilotModeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    session_id: str = Field(min_length=1)
    writes_allowed: bool


class CopilotStopRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    session_id: str = Field(min_length=1)


class CopilotSessionResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    session_id: str
    status: Literal["starting", "running", "stopped", "failed"]
    app_server_unavailable: bool = False
    idempotent_replay: bool = False


class ToolCallRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    role: str = Field(default="copilot", min_length=1)
    session_id: str | None = None
    tool_name: str = Field(min_length=1)
    arguments: dict[str, Any] = Field(default_factory=dict)


class ToolCallResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    tool_name: str
    warrant: Literal["observed", "derived", "checked", "hypothesis", "unknown"]
    result: Any
