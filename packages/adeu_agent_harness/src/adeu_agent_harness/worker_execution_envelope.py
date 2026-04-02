from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

from .attestation import (
    ATTESTATION_OUTPUT_SCHEMA,
    ATTESTATION_VERIFICATION_RESULT_SCHEMA,
)
from .attestation import (
    PROVIDER_ID as ATTESTATION_PROVIDER_ID,
)
from .compile import load_verified_taskpack_snapshot
from .compiled_taskpack_binding import (
    COMPILED_POLICY_TASKPACK_BINDING_SCHEMA,
    CompiledPolicyTaskpackBinding,
)
from .run_taskpack import RUNNER_PROVENANCE_SCHEMA, RUNNER_RESULT_SCHEMA
from .verify_taskpack_run import VERIFICATION_RESULT_SCHEMA

TASK_RUN_BOUNDARY_INSTANCE_SCHEMA = "task_run_boundary_instance@1"
WORKER_EXECUTION_ATTESTATION_SCHEMA = "worker_execution_attestation@1"
WORKER_EXECUTION_PROVENANCE_SCHEMA = "worker_execution_provenance@1"
WORKER_EXECUTION_ENVELOPE_ERROR_SCHEMA = "worker_execution_envelope_error@1"

CompiledBindingSourceKind = Literal["released_compiled_policy_taskpack_binding_ref"]
WorkerSubjectKind = Literal["repo_internal_single_codex_worker"]
ExecutionAdapterKind = Literal["released_taskpack_runner_adapter"]
RepoRefKind = Literal["exact_execution_repository_identity"]
PromptAuthorityPosture = Literal["projection_only_conflict_fail_closed"]

AHK5801_INPUT_INVALID = "AHK5801"
AHK5802_SCHEMA_MISMATCH = "AHK5802"
AHK5803_CARDINALITY_VIOLATION = "AHK5803"
AHK5804_LINEAGE_UNRESOLVED = "AHK5804"
AHK5805_LINEAGE_MISMATCH = "AHK5805"
AHK5806_HASH_DRIFT = "AHK5806"
AHK5807_PROMPT_AUTHORITY_DRIFT = "AHK5807"

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")


def _stable_payload_hash(value: Any) -> str:
    return sha256_canonical_json(value)


def _serialize_payload(payload: dict[str, Any]) -> str:
    return canonical_json(payload) + "\n"


class TaskRunBoundaryInstance(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["task_run_boundary_instance@1"] = TASK_RUN_BOUNDARY_INSTANCE_SCHEMA
    boundary_instance_id: str = Field(min_length=1)
    compiled_binding_source_kind: CompiledBindingSourceKind
    compiled_binding_ref: str = Field(min_length=1)
    compiled_boundary_identity_hash: str = Field(min_length=1)
    repo_ref_kind: RepoRefKind
    repo_ref: str = Field(min_length=1)
    task_instance_identity: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    worker_subject_kind: WorkerSubjectKind
    worker_subject_ref: str = Field(min_length=1)
    execution_adapter_kind: ExecutionAdapterKind
    execution_adapter_ref: str = Field(min_length=1)
    worker_provider_id: str = Field(min_length=1)
    worker_model_id: str = Field(min_length=1)
    taskpack_manifest_ref: str = Field(min_length=1)
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "TaskRunBoundaryInstance":
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


class WorkerExecutionAttestation(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["worker_execution_attestation@1"] = WORKER_EXECUTION_ATTESTATION_SCHEMA
    worker_execution_attestation_id: str = Field(min_length=1)
    boundary_instance_ref: str = Field(min_length=1)
    compiled_binding_ref: str = Field(min_length=1)
    runner_result_ref: str = Field(min_length=1)
    runner_result_hash: str | None = None
    runner_provenance_ref: str = Field(min_length=1)
    runner_provenance_hash: str = Field(min_length=1)
    verification_result_ref: str | None = None
    verification_result_hash: str | None = None
    attestation_validator_result_ref: str | None = None
    attestation_validator_result_hash: str | None = None
    prompt_authority_posture: PromptAuthorityPosture
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "WorkerExecutionAttestation":
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


class WorkerExecutionProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["worker_execution_provenance@1"] = WORKER_EXECUTION_PROVENANCE_SCHEMA
    worker_execution_provenance_id: str = Field(min_length=1)
    boundary_instance_ref: str = Field(min_length=1)
    runner_provenance_ref: str = Field(min_length=1)
    runner_provenance_hash: str = Field(min_length=1)
    repo_ref: str = Field(min_length=1)
    task_instance_identity: str = Field(min_length=1)
    worker_provider_id: str = Field(min_length=1)
    worker_model_id: str = Field(min_length=1)
    execution_adapter_ref: str = Field(min_length=1)
    emitted_artifact_refs: list[str]
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "WorkerExecutionProvenance":
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


@dataclass(frozen=True)
class WorkerExecutionEnvelopeResult:
    boundary_instance: TaskRunBoundaryInstance
    boundary_instance_path: Path
    worker_execution_attestation: WorkerExecutionAttestation
    worker_execution_attestation_path: Path
    worker_execution_provenance: WorkerExecutionProvenance
    worker_execution_provenance_path: Path


class WorkerExecutionEnvelopeError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": WORKER_EXECUTION_ENVELOPE_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *,
    code: str,
    message: str,
    details: dict[str, Any] | None = None,
) -> WorkerExecutionEnvelopeError:
    return WorkerExecutionEnvelopeError(code=code, message=message, details=details)


def _normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="path must not be empty",
            details={"path": raw_path},
        )
    if path_text.startswith("/"):
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="absolute paths are forbidden",
            details={"path": raw_path},
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.match(path_text):
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="windows absolute paths are forbidden",
            details={"path": raw_path},
        )

    segments: list[str] = []
    for segment in path_text.split("/"):
        if segment in ("", "."):
            continue
        if segment == "..":
            if not segments:
                raise _fail(
                    code=AHK5801_INPUT_INVALID,
                    message="path escapes repository root",
                    details={"path": raw_path},
                )
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="path resolves to repository root",
            details={"path": raw_path},
        )
    return "/".join(segments)


def _safe_join(root: Path, rel_path: str) -> Path:
    normalized = _normalize_relative_path(rel_path)
    path = (root / normalized).resolve()
    root_resolved = root.resolve()
    try:
        path.relative_to(root_resolved)
    except ValueError as exc:
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="resolved path escapes repository root",
            details={"path": rel_path},
        ) from exc
    return path


def _to_repo_relative(path: Path, *, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_serialize_payload(payload), encoding="utf-8")


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=AHK5804_LINEAGE_UNRESOLVED,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except OSError as exc:
        raise _fail(
            code=AHK5804_LINEAGE_UNRESOLVED,
            message="required json path cannot be read",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_exactly_one(values: list[str] | None, *, field_name: str) -> str:
    if not isinstance(values, list) or len(values) != 1:
        count = len(values) if isinstance(values, list) else None
        raise _fail(
            code=AHK5803_CARDINALITY_VIOLATION,
            message=f"{field_name} must contain exactly one value",
            details={"field_name": field_name, "count": count},
        )
    value = values[0]
    if not isinstance(value, str) or not value.strip():
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message=f"{field_name} must contain exactly one non-empty string",
            details={"field_name": field_name},
        )
    return value.strip()


def _require_non_empty(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message=f"{field_name} must not be empty",
            details={"field_name": field_name},
        )
    return normalized


def _split_ref(raw_ref: str, *, field_name: str) -> tuple[str, str]:
    if "#" not in raw_ref:
        raise _fail(
            code=AHK5804_LINEAGE_UNRESOLVED,
            message=f"{field_name} must include a # fragment",
            details={"field_name": field_name, "ref": raw_ref},
        )
    path_text, fragment = raw_ref.split("#", 1)
    normalized_path = _normalize_relative_path(path_text)
    fragment = fragment.strip()
    if not fragment:
        raise _fail(
            code=AHK5804_LINEAGE_UNRESOLVED,
            message=f"{field_name} fragment must not be empty",
            details={"field_name": field_name, "ref": raw_ref},
        )
    return normalized_path, fragment


def _expected_repo_ref(*, snapshot_id: str, snapshot_sha256: str) -> str:
    return f"repo_identity:{snapshot_id}:{snapshot_sha256}"


def _validate_repo_ref(*, repo_ref: str, snapshot_id: str, snapshot_sha256: str) -> None:
    expected = _expected_repo_ref(snapshot_id=snapshot_id, snapshot_sha256=snapshot_sha256)
    if repo_ref != expected:
        raise _fail(
            code=AHK5805_LINEAGE_MISMATCH,
            message="repo_ref must resolve to the exact execution repository identity",
            details={
                "repo_ref": repo_ref,
                "expected_repo_ref": expected,
                "snapshot_id": snapshot_id,
                "snapshot_sha256": snapshot_sha256,
            },
        )


def _derive_boundary_instance_id(
    *,
    compiled_boundary_identity_hash: str,
    repo_ref: str,
    task_instance_identity: str,
    execution_adapter_ref: str,
    worker_provider_id: str,
    worker_model_id: str,
) -> str:
    digest = _stable_payload_hash(
        {
            "compiled_boundary_identity_hash": compiled_boundary_identity_hash,
            "repo_ref": repo_ref,
            "task_instance_identity": task_instance_identity,
            "execution_adapter_ref": execution_adapter_ref,
            "worker_provider_id": worker_provider_id,
            "worker_model_id": worker_model_id,
        }
    )
    return f"task_run_boundary_instance:{digest}"


def _derive_attestation_id(
    *,
    boundary_instance_id: str,
    runner_result_ref: str,
    runner_provenance_hash: str,
    verification_result_hash: str | None,
    attestation_validator_result_hash: str | None,
) -> str:
    digest = _stable_payload_hash(
        {
            "boundary_instance_id": boundary_instance_id,
            "runner_result_ref": runner_result_ref,
            "runner_provenance_hash": runner_provenance_hash,
            "verification_result_hash": verification_result_hash,
            "attestation_validator_result_hash": attestation_validator_result_hash,
        }
    )
    return f"worker_execution_attestation:{digest}"


def _derive_provenance_id(
    *,
    boundary_instance_id: str,
    runner_provenance_hash: str,
    emitted_artifact_refs: list[str],
) -> str:
    digest = _stable_payload_hash(
        {
            "boundary_instance_id": boundary_instance_id,
            "runner_provenance_hash": runner_provenance_hash,
            "emitted_artifact_refs": emitted_artifact_refs,
        }
    )
    return f"worker_execution_provenance:{digest}"


def _canonical_payload_hash(payload: dict[str, Any]) -> str:
    return sha256_canonical_json(payload)


def _validate_runner_result(payload: dict[str, Any], *, ref: str) -> str:
    if payload.get("schema") != RUNNER_RESULT_SCHEMA:
        raise _fail(
            code=AHK5802_SCHEMA_MISMATCH,
            message="runner result schema mismatch",
            details={
                "runner_result_ref": ref,
                "expected_schema": RUNNER_RESULT_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    provenance_path = payload.get("provenance_path")
    provenance_hash = payload.get("provenance_hash")
    candidate_hash = payload.get("candidate_change_plan_hash")
    if not isinstance(provenance_path, str) or not provenance_path.strip():
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="runner result provenance_path is missing or invalid",
            details={"runner_result_ref": ref},
        )
    if not isinstance(provenance_hash, str) or not provenance_hash.strip():
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="runner result provenance_hash is missing or invalid",
            details={"runner_result_ref": ref},
        )
    if not isinstance(candidate_hash, str) or not candidate_hash.strip():
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="runner result candidate_change_plan_hash is missing or invalid",
            details={"runner_result_ref": ref},
        )
    return _canonical_payload_hash(payload)


def _recompute_runner_provenance_hash(payload: dict[str, Any]) -> str:
    return sha256_canonical_json(
        {
            "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
            "adapter_id": payload["adapter_id"],
            "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
            "policy_validation_result": payload["policy_validation_result"],
            "exit_status": payload["exit_status"],
        }
    )


def _validate_runner_provenance(payload: dict[str, Any], *, ref: str) -> tuple[str, str]:
    if payload.get("schema") != RUNNER_PROVENANCE_SCHEMA:
        raise _fail(
            code=AHK5802_SCHEMA_MISMATCH,
            message="runner provenance schema mismatch",
            details={
                "runner_provenance_ref": ref,
                "expected_schema": RUNNER_PROVENANCE_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    for field in (
        "taskpack_manifest_hash",
        "adapter_id",
        "candidate_change_plan_hash",
        "policy_validation_result",
        "exit_status",
        "provenance_hash",
    ):
        if field not in payload:
            raise _fail(
                code=AHK5801_INPUT_INVALID,
                message="runner provenance is missing a required field",
                details={"runner_provenance_ref": ref, "field": field},
            )
    observed_hash = payload.get("provenance_hash")
    recomputed_hash = _recompute_runner_provenance_hash(payload)
    if observed_hash != recomputed_hash:
        raise _fail(
            code=AHK5806_HASH_DRIFT,
            message="runner provenance hash drift detected",
            details={
                "runner_provenance_ref": ref,
                "observed_provenance_hash": observed_hash,
                "recomputed_provenance_hash": recomputed_hash,
            },
        )
    return recomputed_hash, _canonical_payload_hash(payload)


def _recompute_verification_result_hash(payload: dict[str, Any]) -> str:
    return sha256_canonical_json(
        {
            "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
            "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
            "runner_provenance_hash": payload["runner_provenance_hash"],
            "verification_result": payload["verification_result"],
            "exit_status": payload["exit_status"],
        }
    )


def _validate_verification_result(payload: dict[str, Any], *, ref: str) -> str:
    if payload.get("schema") != VERIFICATION_RESULT_SCHEMA:
        raise _fail(
            code=AHK5802_SCHEMA_MISMATCH,
            message="verification result schema mismatch",
            details={
                "verification_result_ref": ref,
                "expected_schema": VERIFICATION_RESULT_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    observed_hash = payload.get("verified_result_hash")
    if not isinstance(observed_hash, str) or not observed_hash.strip():
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="verification result verified_result_hash is missing or invalid",
            details={"verification_result_ref": ref},
        )
    recomputed_hash = _recompute_verification_result_hash(payload)
    if observed_hash != recomputed_hash:
        raise _fail(
            code=AHK5806_HASH_DRIFT,
            message="verification result hash drift detected",
            details={
                "verification_result_ref": ref,
                "observed_verified_result_hash": observed_hash,
                "recomputed_verified_result_hash": recomputed_hash,
            },
        )
    return observed_hash


def _recompute_attestation_verification_result_hash(payload: dict[str, Any]) -> str:
    subject = dict(payload)
    subject.pop("result_hash", None)
    return sha256_canonical_json(subject)


def _validate_attestation_verification_result(payload: dict[str, Any], *, ref: str) -> str:
    if payload.get("schema") != ATTESTATION_VERIFICATION_RESULT_SCHEMA:
        raise _fail(
            code=AHK5802_SCHEMA_MISMATCH,
            message="attestation verification result schema mismatch",
            details={
                "attestation_verification_result_ref": ref,
                "expected_schema": ATTESTATION_VERIFICATION_RESULT_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    observed_hash = payload.get("result_hash")
    if not isinstance(observed_hash, str) or not observed_hash.strip():
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="attestation verification result result_hash is missing or invalid",
            details={"attestation_verification_result_ref": ref},
        )
    recomputed_hash = _recompute_attestation_verification_result_hash(payload)
    if observed_hash != recomputed_hash:
        raise _fail(
            code=AHK5806_HASH_DRIFT,
            message="attestation verification result hash drift detected",
            details={
                "attestation_verification_result_ref": ref,
                "observed_result_hash": observed_hash,
                "recomputed_result_hash": recomputed_hash,
            },
        )
    return observed_hash


def _validate_attestation_validator_result(payload: dict[str, Any], *, ref: str) -> str:
    if payload.get("schema") != ATTESTATION_OUTPUT_SCHEMA:
        raise _fail(
            code=AHK5802_SCHEMA_MISMATCH,
            message="attestation validator result schema mismatch",
            details={
                "attestation_validator_result_ref": ref,
                "expected_schema": ATTESTATION_OUTPUT_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    for field in (
        "attestation_verification_result_path",
        "attestation_verification_result_hash",
        "attested_verified_result_path",
        "attested_verified_result_hash",
        "local_verified_result_path",
        "local_verified_result_hash",
    ):
        if field not in payload:
            raise _fail(
                code=AHK5801_INPUT_INVALID,
                message="attestation validator result is missing a required field",
                details={"attestation_validator_result_ref": ref, "field": field},
            )
    return _canonical_payload_hash(payload)


def _load_compiled_binding(
    root: Path,
    compiled_binding_ref: str,
) -> tuple[Path, dict[str, Any], CompiledPolicyTaskpackBinding]:
    compiled_binding_path = _safe_join(root, compiled_binding_ref)
    payload = _load_json_object(compiled_binding_path)
    if payload.get("schema") != COMPILED_POLICY_TASKPACK_BINDING_SCHEMA:
        raise _fail(
            code=AHK5802_SCHEMA_MISMATCH,
            message="compiled binding schema mismatch",
            details={
                "compiled_binding_ref": compiled_binding_ref,
                "expected_schema": COMPILED_POLICY_TASKPACK_BINDING_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    try:
        compiled_binding = CompiledPolicyTaskpackBinding.model_validate(payload)
    except ValueError as exc:
        raise _fail(
            code=AHK5801_INPUT_INVALID,
            message="compiled binding payload is invalid",
            details={"compiled_binding_ref": compiled_binding_ref, "error": str(exc)},
        ) from exc
    observed_semantic_hash = payload.get("semantic_hash")
    if observed_semantic_hash != compiled_binding.semantic_hash:
        raise _fail(
            code=AHK5806_HASH_DRIFT,
            message="compiled binding semantic_hash field drift detected",
            details={
                "compiled_binding_ref": compiled_binding_ref,
                "payload_semantic_hash": observed_semantic_hash,
                "computed_semantic_hash": compiled_binding.semantic_hash,
            },
        )
    return compiled_binding_path, payload, compiled_binding


def _validate_compiled_binding_snapshot(
    *,
    root: Path,
    compiled_binding: CompiledPolicyTaskpackBinding,
) -> None:
    manifest_path = _safe_join(root, compiled_binding.taskpack_manifest_ref)
    snapshot = load_verified_taskpack_snapshot(
        out_dir=manifest_path.parent.relative_to(root).as_posix(),
        repo_root_path=root,
    )
    if snapshot.manifest_hash != compiled_binding.manifest_sha256:
        raise _fail(
            code=AHK5806_HASH_DRIFT,
            message=(
                "compiled binding manifest hash drift detected against "
                "verified taskpack snapshot"
            ),
            details={
                "compiled_binding_ref": compiled_binding.compiled_binding_id,
                "compiled_manifest_sha256": compiled_binding.manifest_sha256,
                "snapshot_manifest_hash": snapshot.manifest_hash,
            },
        )
    manifest_ref = _to_repo_relative(snapshot.manifest_path, root=root)
    if manifest_ref != compiled_binding.taskpack_manifest_ref:
        raise _fail(
            code=AHK5805_LINEAGE_MISMATCH,
            message="compiled binding taskpack_manifest_ref drift detected",
            details={
                "compiled_binding_taskpack_manifest_ref": compiled_binding.taskpack_manifest_ref,
                "snapshot_manifest_ref": manifest_ref,
            },
        )


def _resolve_adapter_ref(root: Path, execution_adapter_ref: str) -> tuple[str, str]:
    registry_rel, adapter_id = _split_ref(
        execution_adapter_ref,
        field_name="execution_adapter_refs",
    )
    payload = _load_json_object(_safe_join(root, registry_rel))
    if payload.get("schema") != "taskpack_runner_adapter_registry@1":
        raise _fail(
            code=AHK5802_SCHEMA_MISMATCH,
            message="execution adapter registry schema mismatch",
            details={
                "execution_adapter_ref": execution_adapter_ref,
                "expected_schema": "taskpack_runner_adapter_registry@1",
                "observed_schema": payload.get("schema"),
            },
        )
    adapters = payload.get("adapters")
    if not isinstance(adapters, list):
        raise _fail(
            code=AHK5804_LINEAGE_UNRESOLVED,
            message="execution adapter registry adapters list is missing",
            details={"execution_adapter_ref": execution_adapter_ref},
        )
    matches = [
        entry
        for entry in adapters
        if isinstance(entry, dict) and entry.get("adapter_id") == adapter_id
    ]
    if len(matches) != 1:
        raise _fail(
            code=AHK5804_LINEAGE_UNRESOLVED,
            message="execution adapter ref must resolve exactly one adapter_id",
            details={
                "execution_adapter_ref": execution_adapter_ref,
                "adapter_id": adapter_id,
                "match_count": len(matches),
            },
        )
    return registry_rel, adapter_id


def build_v48c_worker_execution_envelope(
    *,
    compiled_binding_refs: list[str],
    repo_refs: list[str],
    task_instance_identities: list[str],
    worker_provider_ids: list[str],
    worker_model_ids: list[str],
    execution_adapter_refs: list[str],
    runner_result_refs: list[str],
    runner_provenance_refs: list[str],
    verification_result_refs: list[str] | None,
    attestation_validator_result_refs: list[str] | None,
    prompt_authority_postures: list[str],
    out_dir: str | Path,
    repo_root_path: Path | None = None,
) -> WorkerExecutionEnvelopeResult:
    root = repo_root(anchor=repo_root_path or Path(__file__))

    compiled_binding_ref = _require_exactly_one(
        compiled_binding_refs,
        field_name="compiled_binding_refs",
    )
    repo_ref = _require_exactly_one(repo_refs, field_name="repo_refs")
    task_instance_identity = _require_exactly_one(
        task_instance_identities,
        field_name="task_instance_identities",
    )
    worker_provider_id = _require_exactly_one(
        worker_provider_ids,
        field_name="worker_provider_ids",
    )
    worker_model_id = _require_exactly_one(
        worker_model_ids,
        field_name="worker_model_ids",
    )
    execution_adapter_ref = _require_exactly_one(
        execution_adapter_refs,
        field_name="execution_adapter_refs",
    )
    runner_result_ref = _require_exactly_one(
        runner_result_refs,
        field_name="runner_result_refs",
    )
    runner_provenance_ref = _require_exactly_one(
        runner_provenance_refs,
        field_name="runner_provenance_refs",
    )
    prompt_authority_posture = _require_exactly_one(
        prompt_authority_postures,
        field_name="prompt_authority_postures",
    )
    verification_result_ref = (
        _require_exactly_one(verification_result_refs, field_name="verification_result_refs")
        if verification_result_refs
        else None
    )
    attestation_validator_result_ref = (
        _require_exactly_one(
            attestation_validator_result_refs,
            field_name="attestation_validator_result_refs",
        )
        if attestation_validator_result_refs
        else None
    )
    task_instance_identity = _require_non_empty(
        task_instance_identity,
        field_name="task_instance_identity",
    )
    worker_provider_id = _require_non_empty(
        worker_provider_id,
        field_name="worker_provider_id",
    )
    worker_model_id = _require_non_empty(
        worker_model_id,
        field_name="worker_model_id",
    )
    if prompt_authority_posture != "projection_only_conflict_fail_closed":
        raise _fail(
            code=AHK5807_PROMPT_AUTHORITY_DRIFT,
            message="prompt authority posture is outside the released V48-C surface",
            details={"prompt_authority_posture": prompt_authority_posture},
        )
    if worker_provider_id == ATTESTATION_PROVIDER_ID or worker_model_id == ATTESTATION_PROVIDER_ID:
        raise _fail(
            code=AHK5805_LINEAGE_MISMATCH,
            message="worker provider/model identity may not be inferred from attestation provider",
            details={
                "worker_provider_id": worker_provider_id,
                "worker_model_id": worker_model_id,
                "attestation_provider_id": ATTESTATION_PROVIDER_ID,
            },
        )

    compiled_binding_path, _compiled_binding_payload, compiled_binding = _load_compiled_binding(
        root,
        compiled_binding_ref,
    )
    _validate_compiled_binding_snapshot(root=root, compiled_binding=compiled_binding)
    _validate_repo_ref(
        repo_ref=repo_ref,
        snapshot_id=compiled_binding.snapshot_id,
        snapshot_sha256=compiled_binding.snapshot_sha256,
    )
    _resolve_adapter_ref(root, execution_adapter_ref)

    runner_result_path = _safe_join(root, runner_result_ref)
    runner_result_payload = _load_json_object(runner_result_path)
    runner_result_hash = _validate_runner_result(runner_result_payload, ref=runner_result_ref)

    runner_provenance_path = _safe_join(root, runner_provenance_ref)
    runner_provenance_payload = _load_json_object(runner_provenance_path)
    runner_provenance_subject_hash, runner_provenance_artifact_hash = _validate_runner_provenance(
        runner_provenance_payload,
        ref=runner_provenance_ref,
    )

    if runner_result_payload["provenance_path"] != runner_provenance_ref:
        raise _fail(
            code=AHK5805_LINEAGE_MISMATCH,
            message="runner result provenance_path must match the bound runner_provenance_ref",
            details={
                "runner_result_ref": runner_result_ref,
                "runner_result_provenance_path": runner_result_payload["provenance_path"],
                "runner_provenance_ref": runner_provenance_ref,
            },
        )
    if runner_result_payload["provenance_hash"] != runner_provenance_subject_hash:
        raise _fail(
            code=AHK5806_HASH_DRIFT,
            message="runner result provenance_hash must match the bound runner_provenance hash",
            details={
                "runner_result_ref": runner_result_ref,
                "runner_result_provenance_hash": runner_result_payload["provenance_hash"],
                "runner_provenance_hash": runner_provenance_subject_hash,
            },
        )
    if runner_provenance_payload["taskpack_manifest_hash"] != compiled_binding.manifest_sha256:
        raise _fail(
            code=AHK5805_LINEAGE_MISMATCH,
            message=(
                "runner provenance taskpack_manifest_hash must match "
                "the compiled binding manifest"
            ),
            details={
                "runner_provenance_ref": runner_provenance_ref,
                "runner_provenance_taskpack_manifest_hash": runner_provenance_payload[
                    "taskpack_manifest_hash"
                ],
                "compiled_binding_manifest_sha256": compiled_binding.manifest_sha256,
            },
        )
    _, adapter_id = _resolve_adapter_ref(root, execution_adapter_ref)
    if runner_provenance_payload["adapter_id"] != adapter_id:
        raise _fail(
            code=AHK5805_LINEAGE_MISMATCH,
            message="runner provenance adapter_id must match the bound execution adapter ref",
            details={
                "runner_provenance_ref": runner_provenance_ref,
                "runner_provenance_adapter_id": runner_provenance_payload["adapter_id"],
                "execution_adapter_ref": execution_adapter_ref,
                "execution_adapter_id": adapter_id,
            },
        )

    verification_result_hash: str | None = None
    if verification_result_ref is not None:
        verification_result_path = _safe_join(root, verification_result_ref)
        verification_result_payload = _load_json_object(verification_result_path)
        verification_result_hash = _validate_verification_result(
            verification_result_payload,
            ref=verification_result_ref,
        )
        if (
            verification_result_payload["taskpack_manifest_hash"]
            != compiled_binding.manifest_sha256
        ):
            raise _fail(
                code=AHK5805_LINEAGE_MISMATCH,
                message=(
                    "verification result manifest hash must match "
                    "the compiled binding manifest"
                ),
                details={
                    "verification_result_ref": verification_result_ref,
                    "verification_result_manifest_hash": verification_result_payload[
                        "taskpack_manifest_hash"
                    ],
                    "compiled_binding_manifest_sha256": compiled_binding.manifest_sha256,
                },
            )
        if verification_result_payload["runner_provenance_hash"] != runner_provenance_subject_hash:
            raise _fail(
                code=AHK5806_HASH_DRIFT,
                message=(
                    "verification result runner_provenance_hash must match "
                    "the bound runner provenance"
                ),
                details={
                    "verification_result_ref": verification_result_ref,
                    "verification_result_runner_provenance_hash": verification_result_payload[
                        "runner_provenance_hash"
                    ],
                    "runner_provenance_hash": runner_provenance_subject_hash,
                },
            )
        verified_artifacts = verification_result_payload.get("verified_artifacts")
        if not isinstance(verified_artifacts, dict):
            raise _fail(
                code=AHK5801_INPUT_INVALID,
                message="verification result verified_artifacts payload is missing or invalid",
                details={"verification_result_ref": verification_result_ref},
            )
        if verified_artifacts.get("runner_result_path") != runner_result_ref:
            raise _fail(
                code=AHK5805_LINEAGE_MISMATCH,
                message="verification result runner_result_path must match the bound runner result",
                details={
                    "verification_result_ref": verification_result_ref,
                    "verified_runner_result_path": verified_artifacts.get("runner_result_path"),
                    "runner_result_ref": runner_result_ref,
                },
            )
        if verified_artifacts.get("runner_provenance_path") != runner_provenance_ref:
            raise _fail(
                code=AHK5805_LINEAGE_MISMATCH,
                message=(
                    "verification result runner_provenance_path must match the "
                    "bound runner provenance"
                ),
                details={
                    "verification_result_ref": verification_result_ref,
                    "verified_runner_provenance_path": verified_artifacts.get(
                        "runner_provenance_path"
                    ),
                    "runner_provenance_ref": runner_provenance_ref,
                },
            )

    attestation_validator_result_hash: str | None = None
    if attestation_validator_result_ref is not None:
        attestation_validator_result_path = _safe_join(root, attestation_validator_result_ref)
        attestation_validator_payload = _load_json_object(attestation_validator_result_path)
        attestation_validator_result_hash = _validate_attestation_validator_result(
            attestation_validator_payload,
            ref=attestation_validator_result_ref,
        )
        attestation_verification_result_ref = attestation_validator_payload[
            "attestation_verification_result_path"
        ]
        attestation_verification_result_path = _safe_join(root, attestation_verification_result_ref)
        attestation_verification_result_payload = _load_json_object(
            attestation_verification_result_path
        )
        attestation_verification_result_hash = _validate_attestation_verification_result(
            attestation_verification_result_payload,
            ref=attestation_verification_result_ref,
        )
        if (
            attestation_validator_payload["attestation_verification_result_hash"]
            != attestation_verification_result_hash
        ):
            raise _fail(
                code=AHK5806_HASH_DRIFT,
                message=(
                    "attestation validator result must carry the hash of its bound "
                    "attestation verification result"
                ),
                details={
                    "attestation_validator_result_ref": attestation_validator_result_ref,
                    "carried_attestation_verification_result_hash": attestation_validator_payload[
                        "attestation_verification_result_hash"
                    ],
                    "resolved_attestation_verification_result_hash": (
                        attestation_verification_result_hash
                    ),
                },
            )
        if (
            attestation_verification_result_payload["taskpack_manifest_hash"]
            != compiled_binding.manifest_sha256
        ):
            raise _fail(
                code=AHK5805_LINEAGE_MISMATCH,
                message=(
                    "attestation verification result manifest hash must match the "
                    "compiled binding manifest"
                ),
                details={
                    "attestation_validator_result_ref": attestation_validator_result_ref,
                    "attestation_verification_result_path": attestation_verification_result_ref,
                    "attestation_verification_manifest_hash": (
                        attestation_verification_result_payload["taskpack_manifest_hash"]
                    ),
                    "compiled_binding_manifest_sha256": compiled_binding.manifest_sha256,
                },
            )
        if (
            attestation_verification_result_payload["runner_provenance_hash"]
            != runner_provenance_artifact_hash
        ):
            raise _fail(
                code=AHK5806_HASH_DRIFT,
                message=(
                    "attestation verification result runner_provenance_hash must match "
                    "the bound runner provenance"
                ),
                details={
                    "attestation_validator_result_ref": attestation_validator_result_ref,
                    "attestation_verification_result_path": attestation_verification_result_ref,
                    "attestation_verification_runner_provenance_hash": (
                        attestation_verification_result_payload["runner_provenance_hash"]
                    ),
                    "runner_provenance_hash": runner_provenance_artifact_hash,
                },
            )
        if attestation_verification_result_payload["provider_id"] != ATTESTATION_PROVIDER_ID:
            raise _fail(
                code=AHK5805_LINEAGE_MISMATCH,
                message="attestation verification result provider_id drift detected",
                details={
                    "attestation_verification_result_path": attestation_verification_result_ref,
                    "observed_provider_id": attestation_verification_result_payload["provider_id"],
                    "expected_provider_id": ATTESTATION_PROVIDER_ID,
                },
            )
        if verification_result_hash is not None and (
            attestation_validator_payload["local_verified_result_hash"] != verification_result_hash
        ):
            raise _fail(
                code=AHK5806_HASH_DRIFT,
                message=(
                    "attestation validator local_verified_result_hash must match "
                    "the bound verification result hash"
                ),
                details={
                    "attestation_validator_result_ref": attestation_validator_result_ref,
                    "local_verified_result_hash": attestation_validator_payload[
                        "local_verified_result_hash"
                    ],
                    "verification_result_hash": verification_result_hash,
                },
            )

    out_dir_path = _safe_join(root, str(out_dir))
    boundary_instance_path = out_dir_path / "task_run_boundary_instance.json"
    worker_execution_attestation_path = out_dir_path / "worker_execution_attestation.json"
    worker_execution_provenance_path = out_dir_path / "worker_execution_provenance.json"

    boundary_instance_ref = _to_repo_relative(boundary_instance_path, root=root)
    emitted_artifact_refs = sorted(
        [
            *{runner_result_ref, runner_provenance_ref},
            *([verification_result_ref] if verification_result_ref is not None else []),
            *(
                [attestation_validator_result_ref]
                if attestation_validator_result_ref is not None
                else []
            ),
        ]
    )
    boundary_instance = TaskRunBoundaryInstance(
        boundary_instance_id=_derive_boundary_instance_id(
            compiled_boundary_identity_hash=compiled_binding.compiled_boundary_identity_hash,
            repo_ref=repo_ref,
            task_instance_identity=task_instance_identity,
            execution_adapter_ref=execution_adapter_ref,
            worker_provider_id=worker_provider_id,
            worker_model_id=worker_model_id,
        ),
        compiled_binding_source_kind="released_compiled_policy_taskpack_binding_ref",
        compiled_binding_ref=compiled_binding_ref,
        compiled_boundary_identity_hash=compiled_binding.compiled_boundary_identity_hash,
        repo_ref_kind="exact_execution_repository_identity",
        repo_ref=repo_ref,
        task_instance_identity=task_instance_identity,
        snapshot_id=compiled_binding.snapshot_id,
        snapshot_sha256=compiled_binding.snapshot_sha256,
        worker_subject_kind=compiled_binding.worker_subject_kind,
        worker_subject_ref=compiled_binding.worker_subject_ref,
        execution_adapter_kind="released_taskpack_runner_adapter",
        execution_adapter_ref=execution_adapter_ref,
        worker_provider_id=worker_provider_id,
        worker_model_id=worker_model_id,
        taskpack_manifest_ref=compiled_binding.taskpack_manifest_ref,
        semantic_hash="0" * 64,
    )
    worker_execution_attestation = WorkerExecutionAttestation(
        worker_execution_attestation_id=_derive_attestation_id(
            boundary_instance_id=boundary_instance.boundary_instance_id,
            runner_result_ref=runner_result_ref,
            runner_provenance_hash=runner_provenance_artifact_hash,
            verification_result_hash=verification_result_hash,
            attestation_validator_result_hash=attestation_validator_result_hash,
        ),
        boundary_instance_ref=boundary_instance_ref,
        compiled_binding_ref=compiled_binding_ref,
        runner_result_ref=runner_result_ref,
        runner_result_hash=runner_result_hash,
        runner_provenance_ref=runner_provenance_ref,
        runner_provenance_hash=runner_provenance_artifact_hash,
        verification_result_ref=verification_result_ref,
        verification_result_hash=verification_result_hash,
        attestation_validator_result_ref=attestation_validator_result_ref,
        attestation_validator_result_hash=attestation_validator_result_hash,
        prompt_authority_posture="projection_only_conflict_fail_closed",
        semantic_hash="0" * 64,
    )
    worker_execution_provenance = WorkerExecutionProvenance(
        worker_execution_provenance_id=_derive_provenance_id(
            boundary_instance_id=boundary_instance.boundary_instance_id,
            runner_provenance_hash=runner_provenance_artifact_hash,
            emitted_artifact_refs=emitted_artifact_refs,
        ),
        boundary_instance_ref=boundary_instance_ref,
        runner_provenance_ref=runner_provenance_ref,
        runner_provenance_hash=runner_provenance_artifact_hash,
        repo_ref=repo_ref,
        task_instance_identity=task_instance_identity,
        worker_provider_id=worker_provider_id,
        worker_model_id=worker_model_id,
        execution_adapter_ref=execution_adapter_ref,
        emitted_artifact_refs=emitted_artifact_refs,
        semantic_hash="0" * 64,
    )

    _write_json(
        boundary_instance_path,
        boundary_instance.model_dump(mode="json", exclude_none=True),
    )
    _write_json(
        worker_execution_attestation_path,
        worker_execution_attestation.model_dump(mode="json", exclude_none=True),
    )
    _write_json(
        worker_execution_provenance_path,
        worker_execution_provenance.model_dump(mode="json", exclude_none=True),
    )

    return WorkerExecutionEnvelopeResult(
        boundary_instance=boundary_instance,
        boundary_instance_path=boundary_instance_path,
        worker_execution_attestation=worker_execution_attestation,
        worker_execution_attestation_path=worker_execution_attestation_path,
        worker_execution_provenance=worker_execution_provenance,
        worker_execution_provenance_path=worker_execution_provenance_path,
    )
