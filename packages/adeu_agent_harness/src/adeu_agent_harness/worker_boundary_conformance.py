from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, ValidationError, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

from .compiled_taskpack_binding import (
    COMPILED_POLICY_TASKPACK_BINDING_SCHEMA,
    CompiledPolicyTaskpackBinding,
)
from .run_taskpack import (
    _load_allowlist_payload,
    _load_commands_payload,
    _load_forbidden_payload,
    _normalize_relative_path,
    _path_matches_prefix,
)
from .worker_execution_envelope import (
    TASK_RUN_BOUNDARY_INSTANCE_SCHEMA,
    WORKER_EXECUTION_ATTESTATION_SCHEMA,
    WORKER_EXECUTION_PROVENANCE_SCHEMA,
    TaskRunBoundaryInstance,
    WorkerExecutionAttestation,
    WorkerExecutionProvenance,
)

WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA = "worker_boundary_conformance_report@1"
WORKER_BOUNDARY_CONFORMANCE_ERROR_SCHEMA = "worker_boundary_conformance_error@1"

_FILESYSTEM_MUTATION_SET_SCHEMA = "worker_filesystem_mutation_set@1"
_COMMAND_INVOCATION_LOG_SCHEMA = "worker_command_invocation_log@1"
_EMITTED_ARTIFACT_SET_SCHEMA = "worker_emitted_artifact_set@1"
_EXECUTION_REPOSITORY_IDENTITY_SCHEMA = "worker_execution_repository_identity@1"

ObservedActionCarrierKind = Literal[
    "filesystem_mutation_set_ref",
    "command_invocation_log_ref",
    "emitted_artifact_set_ref",
    "branch_ref_identity_ref",
]
CarrierSourceOfTruth = Literal[
    "observed_execution_state_change_or_governed_replay_artifact",
    "runner_observed_command_events_or_governed_replay_artifact",
    "observed_materialized_run_outputs_or_governed_replay_artifact",
    "exact_execution_repository_identity_capture",
]
CarrierObservationScope = Literal[
    "same_exact_run_pre_post_repo_state",
    "same_exact_run_command_event_stream",
    "same_exact_run_materialized_outputs",
    "same_exact_run_execution_repository_identity",
]
CheckFamily = Literal[
    "lineage_match",
    "filesystem_mutation_scope",
    "command_invocation_scope",
    "emitted_artifact_coherence",
    "execution_repository_identity_match",
    "prompt_conflict",
]
CheckJudgment = Literal["pass", "fail", "incomplete_evidence"]
OverallJudgment = Literal["conformant", "non_conformant", "incomplete_evidence"]
PromptAuthorityPosture = Literal["projection_only_conflict_fail_closed"]
WorkerSubjectKind = Literal["repo_internal_single_codex_worker"]
WorkerScopePosture = Literal["single_worker_only"]
MutationOperationKind = Literal["create", "update", "delete"]

AHK5901_INPUT_INVALID = "AHK5901"
AHK5902_SCHEMA_MISMATCH = "AHK5902"
AHK5903_CARDINALITY_VIOLATION = "AHK5903"
AHK5904_LINEAGE_UNRESOLVED = "AHK5904"
AHK5905_LINEAGE_MISMATCH = "AHK5905"
AHK5906_OBSERVED_CARRIER_INVALID = "AHK5906"
AHK5907_HASH_DRIFT = "AHK5907"
AHK5908_AUTHORITY_DRIFT = "AHK5908"

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")


def _stable_payload_hash(value: Any) -> str:
    return sha256_canonical_json(value)


def _serialize_payload(payload: dict[str, Any]) -> str:
    return canonical_json(payload) + "\n"


class _FilesystemMutation(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    path: str = Field(min_length=1)
    operation_kind: MutationOperationKind

    @model_validator(mode="after")
    def _normalize(self) -> "_FilesystemMutation":
        self.path = _normalize_relative_path(self.path)
        return self


class _FilesystemMutationSet(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["worker_filesystem_mutation_set@1"] = _FILESYSTEM_MUTATION_SET_SCHEMA
    repo_ref: str = Field(min_length=1)
    task_instance_identity: str = Field(min_length=1)
    carrier_source_of_truth: Literal[
        "observed_execution_state_change_or_governed_replay_artifact"
    ]
    carrier_observation_scope: Literal["same_exact_run_pre_post_repo_state"]
    mutations: list[_FilesystemMutation]
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_FilesystemMutationSet":
        self.mutations = sorted(
            self.mutations,
            key=lambda item: (item.path, item.operation_kind),
        )
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


class _CommandInvocation(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    command_id: str = Field(min_length=1)
    run: str = Field(min_length=1)
    working_directory_or_repo_root: str = Field(min_length=1)
    env_overrides: dict[str, str]
    observed_effects: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _normalize(self) -> "_CommandInvocation":
        if self.working_directory_or_repo_root != "repo_root":
            self.working_directory_or_repo_root = _normalize_relative_path(
                self.working_directory_or_repo_root
            )
        self.env_overrides = {key: self.env_overrides[key] for key in sorted(self.env_overrides)}
        self.observed_effects = sorted(
            set(
                effect.strip()
                for effect in self.observed_effects
                if effect.strip()
            )
        )
        return self


class _CommandInvocationLog(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["worker_command_invocation_log@1"] = _COMMAND_INVOCATION_LOG_SCHEMA
    repo_ref: str = Field(min_length=1)
    task_instance_identity: str = Field(min_length=1)
    carrier_source_of_truth: Literal[
        "runner_observed_command_events_or_governed_replay_artifact"
    ]
    carrier_observation_scope: Literal["same_exact_run_command_event_stream"]
    invocations: list[_CommandInvocation]
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_CommandInvocationLog":
        self.invocations = sorted(
            self.invocations,
            key=lambda item: (item.run, item.command_id),
        )
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


class _EmittedArtifactSet(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["worker_emitted_artifact_set@1"] = _EMITTED_ARTIFACT_SET_SCHEMA
    repo_ref: str = Field(min_length=1)
    task_instance_identity: str = Field(min_length=1)
    carrier_source_of_truth: Literal[
        "observed_materialized_run_outputs_or_governed_replay_artifact"
    ]
    carrier_observation_scope: Literal["same_exact_run_materialized_outputs"]
    artifact_refs: list[str]
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_EmittedArtifactSet":
        normalized = sorted(
            {
                _normalize_relative_path(ref)
                for ref in self.artifact_refs
                if isinstance(ref, str) and ref.strip()
            }
        )
        self.artifact_refs = normalized
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


class _ExecutionRepositoryIdentity(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["worker_execution_repository_identity@1"] = (
        _EXECUTION_REPOSITORY_IDENTITY_SCHEMA
    )
    repo_ref: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    task_instance_identity: str = Field(min_length=1)
    branch_ref: str = Field(min_length=1)
    commit_sha: str = Field(min_length=1)
    carrier_source_of_truth: Literal["exact_execution_repository_identity_capture"]
    carrier_observation_scope: Literal["same_exact_run_execution_repository_identity"]
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_ExecutionRepositoryIdentity":
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


class ObservedActionCarrier(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    observed_action_carrier_kind: ObservedActionCarrierKind
    carrier_ref: str = Field(min_length=1)
    carrier_source_of_truth: CarrierSourceOfTruth
    carrier_observation_scope: CarrierObservationScope


class WorkerBoundaryConformanceCheck(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    check_id: str = Field(min_length=1)
    check_family: CheckFamily
    judgment: CheckJudgment
    detail: dict[str, Any]
    supporting_observed_action_refs: list[str]


class WorkerBoundaryConformanceReport(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["worker_boundary_conformance_report@1"] = (
        WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA
    )
    worker_boundary_conformance_report_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    compiled_binding_ref: str = Field(min_length=1)
    boundary_instance_ref: str = Field(min_length=1)
    worker_execution_attestation_ref: str = Field(min_length=1)
    worker_execution_provenance_ref: str = Field(min_length=1)
    repo_ref: str = Field(min_length=1)
    task_instance_identity: str = Field(min_length=1)
    worker_subject_kind: WorkerSubjectKind
    worker_subject_ref: str = Field(min_length=1)
    worker_scope_posture: WorkerScopePosture
    filesystem_mutation_set_ref: str = Field(min_length=1)
    command_invocation_log_ref: str = Field(min_length=1)
    emitted_artifact_set_ref: str = Field(min_length=1)
    branch_ref_identity_ref: str = Field(min_length=1)
    observed_action_carriers: list[ObservedActionCarrier]
    conformance_checks: list[WorkerBoundaryConformanceCheck]
    overall_judgment: OverallJudgment
    supporting_diagnostic_ids: list[str]
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "WorkerBoundaryConformanceReport":
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


@dataclass(frozen=True)
class WorkerBoundaryConformanceResult:
    report: WorkerBoundaryConformanceReport
    report_path: Path


class WorkerBoundaryConformanceError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": WORKER_BOUNDARY_CONFORMANCE_ERROR_SCHEMA,
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
) -> WorkerBoundaryConformanceError:
    return WorkerBoundaryConformanceError(code=code, message=message, details=details)


def _normalize_relative_ref(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise _fail(
            code=AHK5901_INPUT_INVALID,
            message="path must not be empty",
            details={"path": raw_path},
        )
    if path_text.startswith("/"):
        raise _fail(
            code=AHK5901_INPUT_INVALID,
            message="absolute paths are forbidden",
            details={"path": raw_path},
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.match(path_text):
        raise _fail(
            code=AHK5901_INPUT_INVALID,
            message="windows absolute paths are forbidden",
            details={"path": raw_path},
        )
    return _normalize_relative_path(path_text)


def _safe_join(root: Path, rel_path: str) -> Path:
    normalized = _normalize_relative_ref(rel_path)
    path = (root / normalized).resolve()
    root_resolved = root.resolve()
    try:
        path.relative_to(root_resolved)
    except ValueError as exc:
        raise _fail(
            code=AHK5901_INPUT_INVALID,
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
            code=AHK5904_LINEAGE_UNRESOLVED,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except OSError as exc:
        raise _fail(
            code=AHK5904_LINEAGE_UNRESOLVED,
            message="required json path cannot be read",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK5901_INPUT_INVALID,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK5901_INPUT_INVALID,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_exactly_one(values: list[str] | None, *, field_name: str) -> str:
    if not isinstance(values, list) or len(values) != 1:
        count = len(values) if isinstance(values, list) else None
        raise _fail(
            code=AHK5903_CARDINALITY_VIOLATION,
            message=f"{field_name} must contain exactly one value",
            details={"field_name": field_name, "count": count},
        )
    value = values[0]
    if not isinstance(value, str) or not value.strip():
        raise _fail(
            code=AHK5901_INPUT_INVALID,
            message=f"{field_name} must contain exactly one non-empty string",
            details={"field_name": field_name},
        )
    return value.strip()


def _load_model(
    path: Path,
    *,
    model: type[BaseModel],
    expected_schema: str,
    field_name: str,
) -> BaseModel:
    payload = _load_json_object(path)
    observed_schema = payload.get("schema")
    if observed_schema != expected_schema:
        raise _fail(
            code=AHK5902_SCHEMA_MISMATCH,
            message=f"{field_name} schema mismatch",
            details={
                field_name: str(path),
                "expected_schema": expected_schema,
                "observed_schema": observed_schema,
            },
        )
    try:
        return model.model_validate(payload)
    except ValidationError as exc:
        raise _fail(
            code=AHK5906_OBSERVED_CARRIER_INVALID,
            message=f"{field_name} payload failed validation",
            details={"path": str(path), "error": str(exc)},
        ) from exc


def _diagnostic_id_for(check_family: CheckFamily, judgment: CheckJudgment) -> str | None:
    if judgment == "pass":
        return None
    base = {
        "lineage_match": "lineage_mismatch",
        "filesystem_mutation_scope": "off_boundary_mutation",
        "command_invocation_scope": "command_drift",
        "emitted_artifact_coherence": "emitted_artifact_drift",
        "execution_repository_identity_match": "execution_repository_identity_mismatch",
        "prompt_conflict": "prompt_conflict",
    }[check_family]
    if judgment == "incomplete_evidence":
        return f"incomplete_evidence:{base}"
    return base


def _make_check(
    *,
    check_family: CheckFamily,
    judgment: CheckJudgment,
    detail: dict[str, Any],
    supporting_observed_action_refs: list[str],
) -> WorkerBoundaryConformanceCheck:
    digest = _stable_payload_hash(
        {
            "check_family": check_family,
            "judgment": judgment,
            "detail": detail,
            "supporting_observed_action_refs": supporting_observed_action_refs,
        }
    )
    return WorkerBoundaryConformanceCheck(
        check_id=f"{check_family}:{digest[:12]}",
        check_family=check_family,
        judgment=judgment,
        detail=detail,
        supporting_observed_action_refs=sorted(set(supporting_observed_action_refs)),
    )


def _derive_report_id(
    *,
    boundary_instance_ref: str,
    worker_execution_attestation_ref: str,
    worker_execution_provenance_ref: str,
    filesystem_mutation_set_ref: str,
    command_invocation_log_ref: str,
    emitted_artifact_set_ref: str,
    branch_ref_identity_ref: str,
) -> str:
    digest = _stable_payload_hash(
        {
            "boundary_instance_ref": boundary_instance_ref,
            "worker_execution_attestation_ref": worker_execution_attestation_ref,
            "worker_execution_provenance_ref": worker_execution_provenance_ref,
            "filesystem_mutation_set_ref": filesystem_mutation_set_ref,
            "command_invocation_log_ref": command_invocation_log_ref,
            "emitted_artifact_set_ref": emitted_artifact_set_ref,
            "branch_ref_identity_ref": branch_ref_identity_ref,
        }
    )
    return f"worker_boundary_conformance_report:{digest}"


def _load_compiled_binding(path: Path) -> CompiledPolicyTaskpackBinding:
    return _load_model(
        path,
        model=CompiledPolicyTaskpackBinding,
        expected_schema=COMPILED_POLICY_TASKPACK_BINDING_SCHEMA,
        field_name="compiled_binding_ref",
    )  # type: ignore[return-value]


def _load_boundary_instance(path: Path) -> TaskRunBoundaryInstance:
    return _load_model(
        path,
        model=TaskRunBoundaryInstance,
        expected_schema=TASK_RUN_BOUNDARY_INSTANCE_SCHEMA,
        field_name="boundary_instance_ref",
    )  # type: ignore[return-value]


def _load_attestation(path: Path) -> WorkerExecutionAttestation:
    return _load_model(
        path,
        model=WorkerExecutionAttestation,
        expected_schema=WORKER_EXECUTION_ATTESTATION_SCHEMA,
        field_name="worker_execution_attestation_ref",
    )  # type: ignore[return-value]


def _load_provenance(path: Path) -> WorkerExecutionProvenance:
    return _load_model(
        path,
        model=WorkerExecutionProvenance,
        expected_schema=WORKER_EXECUTION_PROVENANCE_SCHEMA,
        field_name="worker_execution_provenance_ref",
    )  # type: ignore[return-value]


def _require_lineage(condition: bool, *, message: str, details: dict[str, Any]) -> None:
    if not condition:
        raise _fail(
            code=AHK5905_LINEAGE_MISMATCH,
            message=message,
            details=details,
        )


def _load_filesystem_mutation_set(path: Path) -> _FilesystemMutationSet:
    return _load_model(
        path,
        model=_FilesystemMutationSet,
        expected_schema=_FILESYSTEM_MUTATION_SET_SCHEMA,
        field_name="filesystem_mutation_set_ref",
    )  # type: ignore[return-value]


def _load_command_invocation_log(path: Path) -> _CommandInvocationLog:
    return _load_model(
        path,
        model=_CommandInvocationLog,
        expected_schema=_COMMAND_INVOCATION_LOG_SCHEMA,
        field_name="command_invocation_log_ref",
    )  # type: ignore[return-value]


def _load_emitted_artifact_set(path: Path) -> _EmittedArtifactSet:
    return _load_model(
        path,
        model=_EmittedArtifactSet,
        expected_schema=_EMITTED_ARTIFACT_SET_SCHEMA,
        field_name="emitted_artifact_set_ref",
    )  # type: ignore[return-value]


def _load_execution_repository_identity(path: Path) -> _ExecutionRepositoryIdentity:
    return _load_model(
        path,
        model=_ExecutionRepositoryIdentity,
        expected_schema=_EXECUTION_REPOSITORY_IDENTITY_SCHEMA,
        field_name="branch_ref_identity_ref",
    )  # type: ignore[return-value]


def _validate_envelope_lineage(
    *,
    compiled_binding_ref: str,
    compiled_binding: CompiledPolicyTaskpackBinding,
    boundary_instance_ref: str,
    boundary_instance: TaskRunBoundaryInstance,
    worker_execution_attestation_ref: str,
    worker_execution_attestation: WorkerExecutionAttestation,
    worker_execution_provenance_ref: str,
    worker_execution_provenance: WorkerExecutionProvenance,
) -> None:
    _require_lineage(
        boundary_instance.compiled_binding_ref == compiled_binding_ref,
        message="boundary instance must bind the same compiled binding ref consumed by conformance",
        details={
            "boundary_instance_ref": boundary_instance_ref,
            "compiled_binding_ref": compiled_binding_ref,
            "observed_compiled_binding_ref": boundary_instance.compiled_binding_ref,
        },
    )
    _require_lineage(
        compiled_binding.compiled_boundary_identity_hash
        == boundary_instance.compiled_boundary_identity_hash,
        message="boundary instance compiled boundary identity hash must match compiled binding",
        details={
            "boundary_instance_ref": boundary_instance_ref,
            "compiled_binding_ref": compiled_binding_ref,
        },
    )
    _require_lineage(
        compiled_binding.snapshot_id == boundary_instance.snapshot_id
        and compiled_binding.snapshot_sha256 == boundary_instance.snapshot_sha256,
        message="compiled binding snapshot must match boundary instance snapshot",
        details={
            "compiled_binding_ref": compiled_binding_ref,
            "boundary_instance_ref": boundary_instance_ref,
        },
    )
    _require_lineage(
        compiled_binding.worker_subject_kind == boundary_instance.worker_subject_kind
        and compiled_binding.worker_subject_ref == boundary_instance.worker_subject_ref,
        message="compiled binding worker subject must match boundary instance worker subject",
        details={
            "compiled_binding_ref": compiled_binding_ref,
            "boundary_instance_ref": boundary_instance_ref,
        },
    )
    _require_lineage(
        worker_execution_attestation.boundary_instance_ref == boundary_instance_ref,
        message="worker execution attestation must bind the same boundary instance",
        details={
            "worker_execution_attestation_ref": worker_execution_attestation_ref,
            "boundary_instance_ref": boundary_instance_ref,
            "observed_boundary_instance_ref": worker_execution_attestation.boundary_instance_ref,
        },
    )
    _require_lineage(
        worker_execution_attestation.compiled_binding_ref == compiled_binding_ref,
        message="worker execution attestation must bind the same compiled binding",
        details={
            "worker_execution_attestation_ref": worker_execution_attestation_ref,
            "compiled_binding_ref": compiled_binding_ref,
            "observed_compiled_binding_ref": worker_execution_attestation.compiled_binding_ref,
        },
    )
    _require_lineage(
        worker_execution_provenance.boundary_instance_ref == boundary_instance_ref,
        message="worker execution provenance must bind the same boundary instance",
        details={
            "worker_execution_provenance_ref": worker_execution_provenance_ref,
            "boundary_instance_ref": boundary_instance_ref,
            "observed_boundary_instance_ref": worker_execution_provenance.boundary_instance_ref,
        },
    )
    _require_lineage(
        worker_execution_attestation.runner_provenance_ref
        == worker_execution_provenance.runner_provenance_ref,
        message="worker execution attestation and provenance must bind the same runner provenance",
        details={
            "worker_execution_attestation_ref": worker_execution_attestation_ref,
            "worker_execution_provenance_ref": worker_execution_provenance_ref,
        },
    )
    _require_lineage(
        worker_execution_attestation.runner_provenance_hash
        == worker_execution_provenance.runner_provenance_hash,
        message=(
            "worker execution attestation and provenance must bind the same "
            "runner provenance hash"
        ),
        details={
            "worker_execution_attestation_ref": worker_execution_attestation_ref,
            "worker_execution_provenance_ref": worker_execution_provenance_ref,
        },
    )
    _require_lineage(
        worker_execution_provenance.repo_ref == boundary_instance.repo_ref,
        message="worker execution provenance repo_ref must match boundary instance repo_ref",
        details={
            "worker_execution_provenance_ref": worker_execution_provenance_ref,
            "boundary_instance_ref": boundary_instance_ref,
        },
    )
    _require_lineage(
        worker_execution_provenance.task_instance_identity
        == boundary_instance.task_instance_identity,
        message=(
            "worker execution provenance task identity must match boundary "
            "instance task identity"
        ),
        details={
            "worker_execution_provenance_ref": worker_execution_provenance_ref,
            "boundary_instance_ref": boundary_instance_ref,
        },
    )
    _require_lineage(
        worker_execution_provenance.worker_provider_id == boundary_instance.worker_provider_id
        and worker_execution_provenance.worker_model_id == boundary_instance.worker_model_id
        and worker_execution_provenance.execution_adapter_ref
        == boundary_instance.execution_adapter_ref,
        message=(
            "worker execution provenance worker/provider/model/adapter must "
            "match boundary instance"
        ),
        details={
            "worker_execution_provenance_ref": worker_execution_provenance_ref,
            "boundary_instance_ref": boundary_instance_ref,
        },
    )


def build_v48d_worker_boundary_conformance_report(
    *,
    boundary_instance_refs: list[str] | None,
    worker_execution_attestation_refs: list[str] | None,
    worker_execution_provenance_refs: list[str] | None,
    filesystem_mutation_set_refs: list[str] | None,
    command_invocation_log_refs: list[str] | None,
    emitted_artifact_set_refs: list[str] | None,
    branch_ref_identity_refs: list[str] | None,
    out_dir: str,
    repo_root_path: str | Path | None = None,
) -> WorkerBoundaryConformanceResult:
    root = (
        repo_root(anchor=Path(__file__))
        if repo_root_path is None
        else Path(repo_root_path).resolve()
    )

    boundary_instance_ref = _require_exactly_one(
        boundary_instance_refs,
        field_name="boundary_instance_refs",
    )
    worker_execution_attestation_ref = _require_exactly_one(
        worker_execution_attestation_refs,
        field_name="worker_execution_attestation_refs",
    )
    worker_execution_provenance_ref = _require_exactly_one(
        worker_execution_provenance_refs,
        field_name="worker_execution_provenance_refs",
    )
    filesystem_mutation_set_ref = _require_exactly_one(
        filesystem_mutation_set_refs,
        field_name="filesystem_mutation_set_refs",
    )
    command_invocation_log_ref = _require_exactly_one(
        command_invocation_log_refs,
        field_name="command_invocation_log_refs",
    )
    emitted_artifact_set_ref = _require_exactly_one(
        emitted_artifact_set_refs,
        field_name="emitted_artifact_set_refs",
    )
    branch_ref_identity_ref = _require_exactly_one(
        branch_ref_identity_refs,
        field_name="branch_ref_identity_refs",
    )

    boundary_instance_path = _safe_join(root, boundary_instance_ref)
    worker_execution_attestation_path = _safe_join(root, worker_execution_attestation_ref)
    worker_execution_provenance_path = _safe_join(root, worker_execution_provenance_ref)
    filesystem_mutation_set_path = _safe_join(root, filesystem_mutation_set_ref)
    command_invocation_log_path = _safe_join(root, command_invocation_log_ref)
    emitted_artifact_set_path = _safe_join(root, emitted_artifact_set_ref)
    branch_ref_identity_path = _safe_join(root, branch_ref_identity_ref)

    boundary_instance = _load_boundary_instance(boundary_instance_path)
    worker_execution_attestation = _load_attestation(worker_execution_attestation_path)
    worker_execution_provenance = _load_provenance(worker_execution_provenance_path)

    compiled_binding_path = _safe_join(root, boundary_instance.compiled_binding_ref)
    compiled_binding = _load_compiled_binding(compiled_binding_path)

    _validate_envelope_lineage(
        compiled_binding_ref=boundary_instance.compiled_binding_ref,
        compiled_binding=compiled_binding,
        boundary_instance_ref=boundary_instance_ref,
        boundary_instance=boundary_instance,
        worker_execution_attestation_ref=worker_execution_attestation_ref,
        worker_execution_attestation=worker_execution_attestation,
        worker_execution_provenance_ref=worker_execution_provenance_ref,
        worker_execution_provenance=worker_execution_provenance,
    )

    filesystem_mutation_set = _load_filesystem_mutation_set(filesystem_mutation_set_path)
    command_invocation_log = _load_command_invocation_log(command_invocation_log_path)
    emitted_artifact_set = _load_emitted_artifact_set(emitted_artifact_set_path)
    branch_ref_identity = _load_execution_repository_identity(branch_ref_identity_path)

    for field_name, repo_ref_value, task_identity in (
        (
            "filesystem_mutation_set_ref",
            filesystem_mutation_set.repo_ref,
            filesystem_mutation_set.task_instance_identity,
        ),
        (
            "command_invocation_log_ref",
            command_invocation_log.repo_ref,
            command_invocation_log.task_instance_identity,
        ),
        (
            "emitted_artifact_set_ref",
            emitted_artifact_set.repo_ref,
            emitted_artifact_set.task_instance_identity,
        ),
        (
            "branch_ref_identity_ref",
            branch_ref_identity.repo_ref,
            branch_ref_identity.task_instance_identity,
        ),
    ):
        _require_lineage(
            repo_ref_value == boundary_instance.repo_ref,
            message=f"{field_name} repo_ref must match boundary instance repo_ref",
            details={
                field_name: {
                    "observed_repo_ref": repo_ref_value,
                    "expected_repo_ref": boundary_instance.repo_ref,
                }
            },
        )
        _require_lineage(
            task_identity == boundary_instance.task_instance_identity,
            message=(
                f"{field_name} task_instance_identity must match boundary "
                "instance task_instance_identity"
            ),
            details={
                field_name: {
                    "observed_task_instance_identity": task_identity,
                    "expected_task_instance_identity": boundary_instance.task_instance_identity,
                }
            },
        )

    allowlist_paths = _load_allowlist_payload(_safe_join(root, compiled_binding.allowlist_ref))
    forbidden_paths, forbidden_effects, _forbidden_operation_kinds = _load_forbidden_payload(
        _safe_join(root, compiled_binding.forbidden_ref)
    )
    _deterministic_env, commands_by_run = _load_commands_payload(
        _safe_join(root, compiled_binding.commands_ref)
    )

    lineage_check = _make_check(
        check_family="lineage_match",
        judgment="pass",
        detail={
            "compiled_binding_ref": boundary_instance.compiled_binding_ref,
            "boundary_instance_ref": boundary_instance_ref,
            "worker_execution_attestation_ref": worker_execution_attestation_ref,
            "worker_execution_provenance_ref": worker_execution_provenance_ref,
        },
        supporting_observed_action_refs=[
            filesystem_mutation_set_ref,
            command_invocation_log_ref,
            emitted_artifact_set_ref,
            branch_ref_identity_ref,
        ],
    )

    outside_allowlist_paths = sorted(
        mutation.path
        for mutation in filesystem_mutation_set.mutations
        if not any(
            _path_matches_prefix(path=mutation.path, prefix=prefix)
            for prefix in allowlist_paths
        )
    )
    forbidden_paths_hit = sorted(
        mutation.path
        for mutation in filesystem_mutation_set.mutations
        if any(
            _path_matches_prefix(path=mutation.path, prefix=prefix)
            for prefix in forbidden_paths
        )
    )
    filesystem_check = _make_check(
        check_family="filesystem_mutation_scope",
        judgment="fail" if outside_allowlist_paths or forbidden_paths_hit else "pass",
        detail={
            "observed_mutations": [
                mutation.model_dump(mode="json") for mutation in filesystem_mutation_set.mutations
            ],
            "outside_allowlist_paths": outside_allowlist_paths,
            "forbidden_paths_hit": forbidden_paths_hit,
        },
        supporting_observed_action_refs=[filesystem_mutation_set_ref],
    )

    unauthorized_commands: list[dict[str, Any]] = []
    forbidden_effect_hits: list[dict[str, Any]] = []
    for invocation in command_invocation_log.invocations:
        expected = commands_by_run.get(invocation.run)
        if expected is None:
            unauthorized_commands.append(invocation.model_dump(mode="json"))
            continue
        if (
            expected["command_id"] != invocation.command_id
            or expected["working_directory_or_repo_root"]
            != invocation.working_directory_or_repo_root
            or expected["env_overrides"] != invocation.env_overrides
        ):
            unauthorized_commands.append(invocation.model_dump(mode="json"))
            continue
        observed_forbidden_effects = sorted(
            effect for effect in invocation.observed_effects if effect in forbidden_effects
        )
        if observed_forbidden_effects:
            forbidden_effect_hits.append(
                {
                    "command_id": invocation.command_id,
                    "run": invocation.run,
                    "observed_forbidden_effects": observed_forbidden_effects,
                }
            )
    command_check = _make_check(
        check_family="command_invocation_scope",
        judgment="fail" if unauthorized_commands or forbidden_effect_hits else "pass",
        detail={
            "observed_invocations": [
                invocation.model_dump(mode="json")
                for invocation in command_invocation_log.invocations
            ],
            "unauthorized_commands": unauthorized_commands,
            "forbidden_effect_hits": forbidden_effect_hits,
        },
        supporting_observed_action_refs=[command_invocation_log_ref],
    )

    expected_artifact_refs = sorted(set(worker_execution_provenance.emitted_artifact_refs))
    observed_artifact_refs = sorted(set(emitted_artifact_set.artifact_refs))
    missing_artifact_refs = sorted(set(expected_artifact_refs) - set(observed_artifact_refs))
    extra_artifact_refs = sorted(set(observed_artifact_refs) - set(expected_artifact_refs))
    emitted_artifact_check = _make_check(
        check_family="emitted_artifact_coherence",
        judgment="fail" if missing_artifact_refs or extra_artifact_refs else "pass",
        detail={
            "observed_artifact_refs": observed_artifact_refs,
            "expected_support_artifact_refs": expected_artifact_refs,
            "missing_artifact_refs": missing_artifact_refs,
            "extra_artifact_refs": extra_artifact_refs,
        },
        supporting_observed_action_refs=[emitted_artifact_set_ref],
    )

    execution_repository_identity_check = _make_check(
        check_family="execution_repository_identity_match",
        judgment=(
            "pass"
            if (
                branch_ref_identity.repo_ref == boundary_instance.repo_ref
                and branch_ref_identity.snapshot_id == boundary_instance.snapshot_id
                and branch_ref_identity.snapshot_sha256 == boundary_instance.snapshot_sha256
            )
            else "fail"
        ),
        detail={
            "observed_repo_ref": branch_ref_identity.repo_ref,
            "expected_repo_ref": boundary_instance.repo_ref,
            "observed_snapshot_id": branch_ref_identity.snapshot_id,
            "expected_snapshot_id": boundary_instance.snapshot_id,
            "observed_snapshot_sha256": branch_ref_identity.snapshot_sha256,
            "expected_snapshot_sha256": boundary_instance.snapshot_sha256,
            "branch_ref": branch_ref_identity.branch_ref,
            "commit_sha": branch_ref_identity.commit_sha,
        },
        supporting_observed_action_refs=[branch_ref_identity_ref],
    )

    prompt_check = _make_check(
        check_family="prompt_conflict",
        judgment=(
            "pass"
            if worker_execution_attestation.prompt_authority_posture
            == "projection_only_conflict_fail_closed"
            else "fail"
        ),
        detail={
            "prompt_authority_posture": worker_execution_attestation.prompt_authority_posture,
            "required_prompt_authority_posture": "projection_only_conflict_fail_closed",
        },
        supporting_observed_action_refs=[],
    )

    conformance_checks = [
        lineage_check,
        filesystem_check,
        command_check,
        emitted_artifact_check,
        execution_repository_identity_check,
        prompt_check,
    ]

    if any(check.judgment == "incomplete_evidence" for check in conformance_checks):
        overall_judgment: OverallJudgment = "incomplete_evidence"
    elif any(check.judgment == "fail" for check in conformance_checks):
        overall_judgment = "non_conformant"
    else:
        overall_judgment = "conformant"

    supporting_diagnostic_ids = sorted(
        diagnostic_id
        for check in conformance_checks
        if (diagnostic_id := _diagnostic_id_for(check.check_family, check.judgment)) is not None
    )

    observed_action_carriers = [
        ObservedActionCarrier(
            observed_action_carrier_kind="filesystem_mutation_set_ref",
            carrier_ref=filesystem_mutation_set_ref,
            carrier_source_of_truth=filesystem_mutation_set.carrier_source_of_truth,
            carrier_observation_scope=filesystem_mutation_set.carrier_observation_scope,
        ),
        ObservedActionCarrier(
            observed_action_carrier_kind="command_invocation_log_ref",
            carrier_ref=command_invocation_log_ref,
            carrier_source_of_truth=command_invocation_log.carrier_source_of_truth,
            carrier_observation_scope=command_invocation_log.carrier_observation_scope,
        ),
        ObservedActionCarrier(
            observed_action_carrier_kind="emitted_artifact_set_ref",
            carrier_ref=emitted_artifact_set_ref,
            carrier_source_of_truth=emitted_artifact_set.carrier_source_of_truth,
            carrier_observation_scope=emitted_artifact_set.carrier_observation_scope,
        ),
        ObservedActionCarrier(
            observed_action_carrier_kind="branch_ref_identity_ref",
            carrier_ref=branch_ref_identity_ref,
            carrier_source_of_truth=branch_ref_identity.carrier_source_of_truth,
            carrier_observation_scope=branch_ref_identity.carrier_observation_scope,
        ),
    ]

    report = WorkerBoundaryConformanceReport(
        worker_boundary_conformance_report_id=_derive_report_id(
            boundary_instance_ref=boundary_instance_ref,
            worker_execution_attestation_ref=worker_execution_attestation_ref,
            worker_execution_provenance_ref=worker_execution_provenance_ref,
            filesystem_mutation_set_ref=filesystem_mutation_set_ref,
            command_invocation_log_ref=command_invocation_log_ref,
            emitted_artifact_set_ref=emitted_artifact_set_ref,
            branch_ref_identity_ref=branch_ref_identity_ref,
        ),
        snapshot_id=boundary_instance.snapshot_id,
        snapshot_sha256=boundary_instance.snapshot_sha256,
        compiled_binding_ref=boundary_instance.compiled_binding_ref,
        boundary_instance_ref=boundary_instance_ref,
        worker_execution_attestation_ref=worker_execution_attestation_ref,
        worker_execution_provenance_ref=worker_execution_provenance_ref,
        repo_ref=boundary_instance.repo_ref,
        task_instance_identity=boundary_instance.task_instance_identity,
        worker_subject_kind=boundary_instance.worker_subject_kind,
        worker_subject_ref=boundary_instance.worker_subject_ref,
        worker_scope_posture="single_worker_only",
        filesystem_mutation_set_ref=filesystem_mutation_set_ref,
        command_invocation_log_ref=command_invocation_log_ref,
        emitted_artifact_set_ref=emitted_artifact_set_ref,
        branch_ref_identity_ref=branch_ref_identity_ref,
        observed_action_carriers=observed_action_carriers,
        conformance_checks=conformance_checks,
        overall_judgment=overall_judgment,
        supporting_diagnostic_ids=supporting_diagnostic_ids,
        semantic_hash="0" * 64,
    )

    out_path = _safe_join(root, out_dir)
    report_path = out_path / "worker_boundary_conformance_report.json"
    _write_json(report_path, report.model_dump(mode="json"))

    return WorkerBoundaryConformanceResult(
        report=report,
        report_path=report_path,
    )
