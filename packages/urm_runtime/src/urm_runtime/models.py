from __future__ import annotations

from datetime import datetime
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field


class TaskEnvelope(BaseModel):
    model_config = ConfigDict(extra="forbid")

    role: str = Field(min_length=1)
    template_id: str = Field(min_length=1)
    template_version: str = Field(min_length=1)
    schema_version: str = Field(min_length=1)
    domain_pack_id: str = Field(min_length=1)
    domain_pack_version: str = Field(min_length=1)
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
    template_id: str = Field(min_length=1)
    template_version: str = Field(min_length=1)
    schema_version: str = Field(min_length=1)
    domain_pack_id: str = Field(min_length=1)
    domain_pack_version: str = Field(min_length=1)

    def idempotency_payload(self) -> dict[str, Any]:
        payload = self.model_dump(mode="json", exclude={"client_request_id"})
        return payload


class URMEventSource(BaseModel):
    model_config = ConfigDict(extra="forbid")

    component: str = Field(min_length=1)
    version: str = Field(min_length=1)
    provider: str = Field(min_length=1)


class URMEventContext(BaseModel):
    model_config = ConfigDict(extra="forbid")

    session_id: str | None = None
    run_id: str | None = None
    role: str = Field(min_length=1)
    endpoint: str = Field(min_length=1)
    ir_hash: str | None = None


class NormalizedEvent(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal["urm-events@1"] = Field(default="urm-events@1", alias="schema")
    event: str = Field(min_length=1)
    stream_id: str = Field(min_length=1)
    seq: int
    ts: datetime
    source: URMEventSource
    context: URMEventContext
    detail: dict[str, Any] = Field(default_factory=dict)
    # Backward-compatible projection used by existing SSE/UI callers.
    event_kind: str | None = None
    payload: dict[str, Any] = Field(default_factory=dict)
    raw_line: str | None = None


class WorkerRunResult(BaseModel):
    model_config = ConfigDict(extra="forbid")

    worker_id: str
    status: Literal["ok", "failed", "cancelled"]
    exit_code: int | None = None
    evidence_id: str
    raw_jsonl_path: str
    urm_events_path: str | None = None
    normalized_event_count: int
    artifact_candidate: Any | None = None
    parse_degraded: bool = False
    invalid_schema: bool = False
    schema_validation_errors: list[str] = Field(default_factory=list)
    error: dict[str, Any] | None = None
    idempotent_replay: bool = False


class WorkerCancelResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    worker_id: str
    status: Literal["running", "ok", "failed", "cancelled"]
    idempotent_replay: bool = False
    error: dict[str, Any] | None = None


class WorkerCancelRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"


class CopilotSessionStartRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    client_request_id: str = Field(min_length=1)
    cwd: str | None = None
    profile_id: str = Field(default="default", min_length=1)

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
    approval_id: str | None = None


class CopilotStopRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    session_id: str = Field(min_length=1)


class CopilotSessionResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    session_id: str
    status: Literal["starting", "running", "stopped", "failed"]
    profile_id: str = Field(default="default", min_length=1)
    profile_version: str = Field(default="profile.v1", min_length=1)
    app_server_unavailable: bool = False
    idempotent_replay: bool = False


class CopilotSteerRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    session_id: str = Field(min_length=1)
    client_request_id: str = Field(min_length=1)
    text: str = Field(min_length=1)
    steer_intent_class: Literal["clarify", "reprioritize", "constraint", "other"] = "other"
    target_turn_id: str | None = Field(default=None, min_length=1)
    use_last_turn: bool = False

    def idempotency_payload(self) -> dict[str, Any]:
        return self.model_dump(mode="json", exclude={"client_request_id"})


class CopilotSteerResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    session_id: str
    status: Literal["starting", "running", "stopped", "failed"]
    target_turn_id: str
    accepted_turn_id: str
    idempotent_replay: bool = False


class AgentSpawnRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    session_id: str = Field(min_length=1)
    client_request_id: str = Field(min_length=1)
    prompt: str = Field(min_length=1)
    target_turn_id: str | None = Field(default=None, min_length=1)
    use_last_turn: bool = False
    profile_id: str | None = Field(default=None, min_length=1)

    def idempotency_payload(self) -> dict[str, Any]:
        return self.model_dump(mode="json", exclude={"client_request_id"})


class AgentSpawnResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    child_id: str
    parent_session_id: str
    status: Literal["running", "completed", "failed", "cancelled"]
    parent_stream_id: str
    child_stream_id: str
    target_turn_id: str
    profile_id: str = Field(default="default", min_length=1)
    profile_version: str = Field(default="profile.v1", min_length=1)
    idempotent_replay: bool = False
    error: dict[str, Any] | None = None
    budget_snapshot: dict[str, int] = Field(default_factory=dict)
    inherited_policy_hash: str | None = None


class AgentCancelRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    client_request_id: str = Field(min_length=1)

    def idempotency_payload(self) -> dict[str, Any]:
        return self.model_dump(mode="json", exclude={"client_request_id"})


class AgentCancelResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    child_id: str
    status: Literal["running", "completed", "failed", "cancelled"]
    idempotent_replay: bool = False
    error: dict[str, Any] | None = None


class ToolCallRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    role: str = Field(default="copilot", min_length=1)
    session_id: str | None = None
    approval_id: str | None = None
    tool_name: str = Field(min_length=1)
    arguments: dict[str, Any] = Field(default_factory=dict)


class ToolCallResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    tool_name: str
    warrant: Literal["observed", "derived", "checked", "hypothesis", "unknown"]
    result: Any
    policy_trace: dict[str, Any] | None = None


class ApprovalIssueRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    session_id: str = Field(min_length=1)
    action_kind: str = Field(min_length=1)
    action_payload: dict[str, Any] = Field(default_factory=dict)
    expires_in_secs: int | None = Field(default=None, ge=1, le=24 * 60 * 60)


class ApprovalIssueResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    approval_id: str
    session_id: str
    action_kind: str
    action_hash: str
    expires_at: datetime


class ApprovalRevokeRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    provider: Literal["codex"] = "codex"
    approval_id: str = Field(min_length=1)


class ApprovalRevokeResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    approval_id: str
    revoked: bool
    idempotent_replay: bool = False
