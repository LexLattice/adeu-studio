from __future__ import annotations

import sqlite3
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from urm_runtime.config import URMRuntimeConfig
from urm_runtime.errors import URMError
from urm_runtime.models import TaskEnvelope, WorkerRunRequest, WorkerRunResult
from urm_runtime.storage import db_path_from_config, get_evidence_record, transaction
from urm_runtime.worker import CodexExecWorkerRunner

from .models import (
    AppStateSnapshot,
    EvidenceBundle,
    ReadEvidenceArgs,
    RunWorkflowArgs,
    TemplateMeta,
    WarrantTag,
    WorkflowRunRef,
)

DOMAIN_PACK_ID = "urm_domain_adeu"
DOMAIN_PACK_VERSION = "0.0.0"
DEFAULT_WORKFLOW_TEMPLATE_ID = "adeu.workflow.pipeline_worker.v0"
SUPPORTED_TOOL_NAMES: frozenset[str] = frozenset(
    {
        "adeu.get_app_state",
        "adeu.list_templates",
        "adeu.run_workflow",
        "adeu.read_evidence",
        "urm.spawn_worker",
    }
)

_TEMPLATES: tuple[TemplateMeta, ...] = (
    TemplateMeta(
        template_id=DEFAULT_WORKFLOW_TEMPLATE_ID,
        template_version="v0",
        schema_version="urm.workflow.v0",
        domain_pack_id=DOMAIN_PACK_ID,
        domain_pack_version=DOMAIN_PACK_VERSION,
        role="pipeline_worker",
        description="Run a short-lived read-only Codex exec workflow with evidence capture.",
    ),
)

_TABLES_FOR_APP_STATE: tuple[str, ...] = (
    "artifacts",
    "concept_artifacts",
    "documents",
    "urm_worker_run",
    "urm_evidence_record",
    "urm_copilot_session",
)


@dataclass
class ADEUDomainTools:
    config: URMRuntimeConfig
    worker_runner: CodexExecWorkerRunner
    domain_pack_id: str = DOMAIN_PACK_ID
    domain_pack_version: str = DOMAIN_PACK_VERSION

    @classmethod
    def from_config(cls, *, config: URMRuntimeConfig | None = None) -> "ADEUDomainTools":
        resolved = config or URMRuntimeConfig.from_env()
        return cls(config=resolved, worker_runner=CodexExecWorkerRunner(config=resolved))

    def list_templates(self) -> list[TemplateMeta]:
        return sorted(_TEMPLATES, key=lambda template: template.template_id)

    def get_app_state(self) -> AppStateSnapshot:
        db_path = db_path_from_config(self.config)
        counts: dict[str, int] = {}
        active_session_id: str | None = None
        active_writes_allowed = False
        codex_version: str | None = None
        codex_exec_available: bool | None = None
        codex_app_server_available: bool | None = None

        with sqlite3.connect(db_path) as con:
            for table_name in _TABLES_FOR_APP_STATE:
                counts[table_name] = _count_rows_if_exists(con=con, table_name=table_name)

            if _table_exists(con=con, table_name="urm_copilot_session"):
                row = con.execute(
                    """
                    SELECT copilot_session_id, writes_allowed
                    FROM urm_copilot_session
                    WHERE status IN ('starting', 'running')
                    ORDER BY started_at DESC, copilot_session_id ASC
                    LIMIT 1
                    """
                ).fetchone()
                if row is not None:
                    active_session_id = str(row[0])
                    active_writes_allowed = bool(row[1])

            if _table_exists(con=con, table_name="urm_codex_capability_probe"):
                row = con.execute(
                    """
                    SELECT codex_version, exec_available, app_server_available
                    FROM urm_codex_capability_probe
                    ORDER BY created_at DESC, probe_id ASC
                    LIMIT 1
                    """
                ).fetchone()
                if row is not None:
                    codex_version = str(row[0]) if row[0] is not None else None
                    codex_exec_available = bool(row[1])
                    codex_app_server_available = bool(row[2])

        return AppStateSnapshot(
            counts=counts,
            active_copilot_session_id=active_session_id,
            active_copilot_writes_allowed=active_writes_allowed,
            codex_version=codex_version,
            codex_exec_available=codex_exec_available,
            codex_app_server_available=codex_app_server_available,
        )

    def run_workflow(self, arguments: dict[str, Any]) -> WorkflowRunRef:
        args = RunWorkflowArgs.model_validate(arguments)
        if args.mode != "read_only":
            raise URMError(
                code="URM_POLICY_DENIED",
                message="run_workflow only supports read_only mode in v0",
                context={"mode": args.mode},
            )
        template = self._require_template(args.template_id)
        prompt = _extract_prompt(args.inputs)
        client_request_id = args.client_request_id or uuid.uuid4().hex
        request = WorkerRunRequest(
            provider="codex",
            role=template.role,
            client_request_id=client_request_id,
            prompt=prompt,
            output_schema_path=args.output_schema_path,
            cwd=args.cwd,
            timeout_secs=args.timeout_secs,
            template_id=template.template_id,
            template_version=template.template_version,
            schema_version=template.schema_version,
            domain_pack_id=template.domain_pack_id,
            domain_pack_version=template.domain_pack_version,
        )
        result = self.worker_runner.run(request)
        return WorkflowRunRef(
            worker_id=result.worker_id,
            evidence_id=result.evidence_id,
            status=result.status,
            template_id=template.template_id,
            template_version=template.template_version,
        )

    def spawn_worker(self, arguments: dict[str, Any]) -> WorkerRunResult:
        task_raw = arguments.get("task_envelope")
        if task_raw is None:
            raise URMError(
                code="URM_POLICY_DENIED",
                message="'task_envelope' is required for urm.spawn_worker",
                context={"tool_name": "urm.spawn_worker"},
            )
        envelope = TaskEnvelope.model_validate(task_raw)
        prompt = _extract_prompt(envelope.inputs)
        client_request_id = str(arguments.get("client_request_id") or uuid.uuid4().hex)
        timeout_raw = arguments.get("timeout_secs")
        timeout_secs = int(timeout_raw) if timeout_raw is not None else 120
        output_schema_path = (
            str(arguments["output_schema_path"]) if "output_schema_path" in arguments else None
        )
        cwd = str(arguments["cwd"]) if "cwd" in arguments else None
        request = WorkerRunRequest(
            provider="codex",
            role=envelope.role,
            client_request_id=client_request_id,
            prompt=prompt,
            output_schema_path=output_schema_path,
            cwd=cwd,
            timeout_secs=timeout_secs,
            template_id=envelope.template_id,
            template_version=envelope.template_version,
            schema_version=envelope.schema_version,
            domain_pack_id=envelope.domain_pack_id or DOMAIN_PACK_ID,
            domain_pack_version=envelope.domain_pack_version or DOMAIN_PACK_VERSION,
        )
        return self.worker_runner.run(request)

    def read_evidence(self, arguments: dict[str, Any]) -> EvidenceBundle:
        args = ReadEvidenceArgs.model_validate(arguments)
        db_path = db_path_from_config(self.config)
        with transaction(db_path=db_path) as con:
            row = get_evidence_record(con=con, evidence_id=args.evidence_id)
        if row is None:
            raise URMError(
                code="URM_NOT_FOUND",
                message="evidence not found",
                status_code=404,
                context={"evidence_id": args.evidence_id},
            )

        if row.purged_at is not None:
            return EvidenceBundle(
                evidence_id=row.evidence_id,
                source=row.source,
                role=row.role,
                status=row.status,
                started_at=row.started_at,
                ended_at=row.ended_at,
                raw_jsonl_path=None,
                raw_jsonl=None,
                purged=True,
                metadata={**row.metadata_json, "purge_reason": row.purge_reason},
                error=row.error_json,
            )

        raw_path = _resolve_evidence_path(
            config=self.config,
            relative_path=row.raw_jsonl_path,
        )
        if not raw_path.exists():
            raise URMError(
                code="URM_EVIDENCE_PURGED",
                message="evidence file is unavailable on disk",
                status_code=404,
                context={"evidence_id": args.evidence_id},
            )

        raw_payload = raw_path.read_bytes()
        truncated = len(raw_payload) > args.max_bytes
        if truncated:
            raw_payload = raw_payload[: args.max_bytes]
        metadata = dict(row.metadata_json)
        if truncated:
            metadata["read_truncated"] = True
            metadata["read_max_bytes"] = args.max_bytes

        return EvidenceBundle(
            evidence_id=row.evidence_id,
            source=row.source,
            role=row.role,
            status=row.status,
            started_at=row.started_at,
            ended_at=row.ended_at,
            raw_jsonl_path=row.raw_jsonl_path,
            raw_jsonl=raw_payload.decode("utf-8", errors="replace"),
            purged=False,
            metadata=metadata,
            error=row.error_json,
        )

    def call_tool(self, *, tool_name: str, arguments: dict[str, Any]) -> tuple[Any, WarrantTag]:
        if not self.supports_tool(tool_name=tool_name):
            raise URMError(
                code="URM_POLICY_DENIED",
                message="unsupported tool name",
                context={"tool_name": tool_name},
            )
        if tool_name == "adeu.get_app_state":
            return self.get_app_state().model_dump(mode="json"), "observed"
        if tool_name == "adeu.list_templates":
            templates = [template.model_dump(mode="json") for template in self.list_templates()]
            return {"templates": templates}, "observed"
        if tool_name == "adeu.run_workflow":
            return self.run_workflow(arguments).model_dump(mode="json"), "checked"
        if tool_name == "adeu.read_evidence":
            return self.read_evidence(arguments).model_dump(mode="json"), "observed"
        if tool_name == "urm.spawn_worker":
            result = self.spawn_worker(arguments)
            return result.model_dump(mode="json"), "checked"
        raise AssertionError("unreachable: tool name validated via supports_tool")

    def supports_tool(self, *, tool_name: str) -> bool:
        return tool_name in SUPPORTED_TOOL_NAMES

    def _require_template(self, template_id: str) -> TemplateMeta:
        for template in _TEMPLATES:
            if template.template_id == template_id:
                return template
        raise URMError(
            code="URM_POLICY_DENIED",
            message="unknown template_id",
            context={"template_id": template_id},
        )


def _table_exists(*, con: sqlite3.Connection, table_name: str) -> bool:
    row = con.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name = ?",
        (table_name,),
    ).fetchone()
    return row is not None


def _count_rows_if_exists(*, con: sqlite3.Connection, table_name: str) -> int:
    if not _table_exists(con=con, table_name=table_name):
        return 0
    row = con.execute(f"SELECT COUNT(*) FROM {table_name}").fetchone()
    return int(row[0]) if row is not None else 0


def _extract_prompt(inputs: dict[str, Any]) -> str:
    prompt = str(inputs.get("prompt", "")).strip()
    if not prompt:
        raise URMError(
            code="URM_POLICY_DENIED",
            message="workflow inputs must include a non-empty prompt",
            context={"required_input": "prompt"},
        )
    return prompt


def _resolve_evidence_path(*, config: URMRuntimeConfig, relative_path: str) -> Path:
    path = Path(relative_path)
    if path.is_absolute():
        raise URMError(
            code="URM_POLICY_DENIED",
            message="evidence path must be relative",
            context={"raw_jsonl_path": relative_path},
        )
    resolved = (config.var_root / path).resolve()
    root = config.evidence_root.resolve()
    if not resolved.is_relative_to(root):
        raise URMError(
            code="URM_POLICY_DENIED",
            message="evidence path is outside configured evidence root",
            context={"raw_jsonl_path": relative_path},
        )
    return resolved
