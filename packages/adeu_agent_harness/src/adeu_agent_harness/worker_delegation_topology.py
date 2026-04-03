from __future__ import annotations

import json
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
from .run_taskpack import _normalize_relative_path
from .worker_boundary_conformance import (
    WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA,
    WorkerBoundaryConformanceReport,
)
from .worker_execution_envelope import (
    TASK_RUN_BOUNDARY_INSTANCE_SCHEMA,
    TaskRunBoundaryInstance,
)

WORKER_DELEGATION_TOPOLOGY_SCHEMA = "worker_delegation_topology@1"
WORKER_DELEGATION_TOPOLOGY_ERROR_SCHEMA = "worker_delegation_topology_error@1"

DelegationEdgeKind = Literal["supervisor_to_worker"]
WorkerRoleKind = Literal["supervisor", "worker"]
HandoffResult = Literal["completed", "rejected", "incomplete_lineage"]
SupportingDiagnosticFamily = Literal[
    "role_ambiguity",
    "lineage_mismatch",
    "compiled_boundary_mismatch",
    "repo_snapshot_mismatch",
    "non_conformant_parent",
    "non_conformant_child",
    "recursive_topology_forbidden",
]
TopologyScopePosture = Literal["one_parent_one_child_one_edge_only"]
AuthorityRelationPosture = Literal["same_compiled_boundary_no_widening"]
WorkerSubjectKind = Literal["repo_internal_single_codex_worker"]

AHK6001_INPUT_INVALID = "AHK6001"
AHK6002_SCHEMA_MISMATCH = "AHK6002"
AHK6003_CARDINALITY_VIOLATION = "AHK6003"
AHK6004_LINEAGE_UNRESOLVED = "AHK6004"
AHK6005_LINEAGE_MISMATCH = "AHK6005"

_DIAGNOSTIC_FAMILY_ORDER: tuple[SupportingDiagnosticFamily, ...] = (
    "role_ambiguity",
    "lineage_mismatch",
    "compiled_boundary_mismatch",
    "repo_snapshot_mismatch",
    "non_conformant_parent",
    "non_conformant_child",
    "recursive_topology_forbidden",
)


def _stable_payload_hash(value: Any) -> str:
    return sha256_canonical_json(value)


class WorkerDelegationTopology(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["worker_delegation_topology@1"] = WORKER_DELEGATION_TOPOLOGY_SCHEMA
    worker_delegation_topology_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    repo_ref: str = Field(min_length=1)
    parent_worker_boundary_conformance_report_ref: str = Field(min_length=1)
    child_worker_boundary_conformance_report_ref: str = Field(min_length=1)
    parent_boundary_instance_ref: str = Field(min_length=1)
    child_boundary_instance_ref: str = Field(min_length=1)
    parent_compiled_binding_ref: str = Field(min_length=1)
    child_compiled_binding_ref: str = Field(min_length=1)
    parent_task_instance_identity: str = Field(min_length=1)
    child_task_instance_identity: str = Field(min_length=1)
    parent_worker_subject_kind: WorkerSubjectKind
    parent_worker_subject_ref: str = Field(min_length=1)
    child_worker_subject_kind: WorkerSubjectKind
    child_worker_subject_ref: str = Field(min_length=1)
    parent_role_kind: WorkerRoleKind
    child_role_kind: WorkerRoleKind
    delegation_edge_id: str = Field(min_length=1)
    delegation_edge_kind: DelegationEdgeKind = "supervisor_to_worker"
    delegated_task_identity: str = Field(min_length=1)
    handoff_result: HandoffResult
    topology_scope_posture: TopologyScopePosture = "one_parent_one_child_one_edge_only"
    authority_relation_posture: AuthorityRelationPosture = (
        "same_compiled_boundary_no_widening"
    )
    supporting_diagnostic_ids: list[str]
    supporting_diagnostic_families: list[SupportingDiagnosticFamily]
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "WorkerDelegationTopology":
        if len(self.supporting_diagnostic_families) != len(
            set(self.supporting_diagnostic_families)
        ):
            raise ValueError("supporting_diagnostic_families must not contain duplicates")
        expected_families = sorted(
            self.supporting_diagnostic_families,
            key=_DIAGNOSTIC_FAMILY_ORDER.index,
        )
        if self.supporting_diagnostic_families != expected_families:
            raise ValueError(
                "supporting_diagnostic_families must already be ordered by the "
                "released V48-E diagnostic family vocabulary"
            )

        expected_diagnostic_ids = [
            _diagnostic_id_for(family) for family in self.supporting_diagnostic_families
        ]
        if len(self.supporting_diagnostic_ids) != len(set(self.supporting_diagnostic_ids)):
            raise ValueError("supporting_diagnostic_ids must not contain duplicates")
        if self.supporting_diagnostic_ids != expected_diagnostic_ids:
            raise ValueError(
                "supporting_diagnostic_ids must exactly match the released V48-E "
                "diagnostic family mapping and ordering"
            )
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


@dataclass(frozen=True)
class WorkerDelegationTopologyResult:
    topology: WorkerDelegationTopology
    topology_path: Path


class WorkerDelegationTopologyError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": WORKER_DELEGATION_TOPOLOGY_ERROR_SCHEMA,
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
) -> WorkerDelegationTopologyError:
    return WorkerDelegationTopologyError(code=code, message=message, details=details)


def _require_exactly_one(values: list[str], *, field_name: str) -> str:
    if len(values) != 1:
        raise _fail(
            code=AHK6003_CARDINALITY_VIOLATION,
            message=f"{field_name} must contain exactly one value",
            details={"field_name": field_name, "observed_count": len(values)},
        )
    value = values[0].strip()
    if not value:
        raise _fail(
            code=AHK6001_INPUT_INVALID,
            message=f"{field_name} must not be empty",
            details={"field_name": field_name},
        )
    return value


def _normalize_role_kind(value: str, *, field_name: str) -> WorkerRoleKind:
    if value not in {"supervisor", "worker"}:
        raise _fail(
            code=AHK6001_INPUT_INVALID,
            message=f"{field_name} must use the released V48-E worker role vocabulary",
            details={"field_name": field_name, "value": value},
        )
    return value  # type: ignore[return-value]


def _normalize_relative_ref(raw_ref: str, *, field_name: str) -> str:
    try:
        path_text = raw_ref.strip()
        if "#" in path_text:
            path_text = path_text.split("#", 1)[0]
        normalized = _normalize_relative_path(path_text)
    except RuntimeError as exc:
        raise _fail(
            code=AHK6001_INPUT_INVALID,
            message=f"{field_name} must be a repo-relative path",
            details={"field_name": field_name, "value": raw_ref, "error": str(exc)},
        ) from exc
    if not normalized:
        raise _fail(
            code=AHK6001_INPUT_INVALID,
            message=f"{field_name} must not be empty",
            details={"field_name": field_name},
        )
    return normalized


def _safe_join(root: Path, raw_ref: str, *, field_name: str) -> Path:
    normalized = _normalize_relative_ref(raw_ref, field_name=field_name)
    path = (root / normalized).resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise _fail(
            code=AHK6001_INPUT_INVALID,
            message=f"{field_name} must stay within the repository root",
            details={"field_name": field_name, "value": raw_ref},
        ) from exc
    return path


def _load_json_object(path: Path, *, field_name: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=AHK6004_LINEAGE_UNRESOLVED,
            message=f"{field_name} could not be resolved",
            details={"field_name": field_name, "path": str(path)},
        ) from exc
    except OSError as exc:
        raise _fail(
            code=AHK6004_LINEAGE_UNRESOLVED,
            message=f"{field_name} could not be read",
            details={"field_name": field_name, "path": str(path), "error": str(exc)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK6002_SCHEMA_MISMATCH,
            message=f"{field_name} must contain valid JSON",
            details={"field_name": field_name, "path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK6002_SCHEMA_MISMATCH,
            message=f"{field_name} must decode to a JSON object",
            details={"field_name": field_name, "path": str(path)},
        )
    return payload


def _load_payload_model(
    *,
    root: Path,
    ref: str,
    field_name: str,
    expected_schema: str,
    model: type[BaseModel],
) -> BaseModel:
    path = _safe_join(root, ref, field_name=field_name)
    payload = _load_json_object(path, field_name=field_name)
    observed_schema = payload.get("schema")
    if observed_schema != expected_schema:
        raise _fail(
            code=AHK6002_SCHEMA_MISMATCH,
            message=f"{field_name} schema mismatch",
            details={
                "field_name": field_name,
                "path": ref,
                "expected_schema": expected_schema,
                "observed_schema": observed_schema,
            },
        )
    try:
        return model.model_validate(payload)
    except ValidationError as exc:
        raise _fail(
            code=AHK6002_SCHEMA_MISMATCH,
            message=f"{field_name} payload failed validation",
            details={"field_name": field_name, "path": ref, "error": str(exc)},
        ) from exc


@dataclass(frozen=True)
class _ResolvedChain:
    report: WorkerBoundaryConformanceReport
    boundary_instance: TaskRunBoundaryInstance | None
    compiled_binding: CompiledPolicyTaskpackBinding | None
    lineage_complete: bool


def _resolve_support_chain(
    *,
    root: Path,
    report: WorkerBoundaryConformanceReport,
    report_role: str,
) -> _ResolvedChain:
    lineage_complete = True
    boundary_instance: TaskRunBoundaryInstance | None = None
    compiled_binding: CompiledPolicyTaskpackBinding | None = None

    try:
        boundary_instance = _load_payload_model(
            root=root,
            ref=report.boundary_instance_ref,
            field_name=f"{report_role}_boundary_instance_ref",
            expected_schema=TASK_RUN_BOUNDARY_INSTANCE_SCHEMA,
            model=TaskRunBoundaryInstance,
        )
    except WorkerDelegationTopologyError:
        lineage_complete = False

    try:
        compiled_binding = _load_payload_model(
            root=root,
            ref=report.compiled_binding_ref,
            field_name=f"{report_role}_compiled_binding_ref",
            expected_schema=COMPILED_POLICY_TASKPACK_BINDING_SCHEMA,
            model=CompiledPolicyTaskpackBinding,
        )
    except WorkerDelegationTopologyError:
        lineage_complete = False

    if boundary_instance is not None:
        if boundary_instance.compiled_binding_ref != report.compiled_binding_ref:
            lineage_complete = False
        if boundary_instance.snapshot_id != report.snapshot_id:
            lineage_complete = False
        if boundary_instance.snapshot_sha256 != report.snapshot_sha256:
            lineage_complete = False
        if boundary_instance.repo_ref != report.repo_ref:
            lineage_complete = False
        if boundary_instance.task_instance_identity != report.task_instance_identity:
            lineage_complete = False
        if boundary_instance.worker_subject_kind != report.worker_subject_kind:
            lineage_complete = False
        if boundary_instance.worker_subject_ref != report.worker_subject_ref:
            lineage_complete = False

    if compiled_binding is not None:
        if compiled_binding.snapshot_id != report.snapshot_id:
            lineage_complete = False
        if compiled_binding.snapshot_sha256 != report.snapshot_sha256:
            lineage_complete = False
        if compiled_binding.worker_subject_kind != report.worker_subject_kind:
            lineage_complete = False
        if compiled_binding.worker_subject_ref != report.worker_subject_ref:
            lineage_complete = False

    if boundary_instance is not None and compiled_binding is not None:
        if boundary_instance.compiled_binding_ref != report.compiled_binding_ref:
            lineage_complete = False
        if boundary_instance.compiled_boundary_identity_hash != (
            compiled_binding.compiled_boundary_identity_hash
        ):
            lineage_complete = False

    return _ResolvedChain(
        report=report,
        boundary_instance=boundary_instance,
        compiled_binding=compiled_binding,
        lineage_complete=lineage_complete,
    )


def _diagnostic_id_for(family: SupportingDiagnosticFamily) -> str:
    return f"worker_delegation_topology:{family}"


def _derive_topology_id(payload: dict[str, Any]) -> str:
    digest = _stable_payload_hash(
        {
            "snapshot_id": payload["snapshot_id"],
            "snapshot_sha256": payload["snapshot_sha256"],
            "repo_ref": payload["repo_ref"],
            "parent_report_semantic_hash": payload["parent_report_semantic_hash"],
            "child_report_semantic_hash": payload["child_report_semantic_hash"],
            "parent_boundary_instance_semantic_hash": payload[
                "parent_boundary_instance_semantic_hash"
            ],
            "child_boundary_instance_semantic_hash": payload[
                "child_boundary_instance_semantic_hash"
            ],
            "parent_compiled_binding_semantic_hash": payload[
                "parent_compiled_binding_semantic_hash"
            ],
            "child_compiled_binding_semantic_hash": payload[
                "child_compiled_binding_semantic_hash"
            ],
            "parent_lineage_complete": payload["parent_lineage_complete"],
            "child_lineage_complete": payload["child_lineage_complete"],
            "parent_role_kind": payload["parent_role_kind"],
            "child_role_kind": payload["child_role_kind"],
            "delegation_edge_id": payload["delegation_edge_id"],
            "delegated_task_identity": payload["delegated_task_identity"],
            "handoff_result": payload["handoff_result"],
            "supporting_diagnostic_families": payload["supporting_diagnostic_families"],
            "supporting_diagnostic_ids": payload["supporting_diagnostic_ids"],
        }
    )
    return f"worker_delegation_topology:{digest}"


def _serialize_payload(payload: dict[str, Any]) -> str:
    return canonical_json(payload) + "\n"


def build_v48e_worker_delegation_topology(
    *,
    parent_worker_boundary_conformance_report_refs: list[str],
    child_worker_boundary_conformance_report_refs: list[str],
    parent_role_kinds: list[str],
    child_role_kinds: list[str],
    delegation_edge_ids: list[str],
    delegated_task_identities: list[str],
    out_dir: str,
    repo_root_path: str | Path | None = None,
) -> WorkerDelegationTopologyResult:
    root = (
        repo_root(anchor=Path(__file__))
        if repo_root_path is None
        else Path(repo_root_path).resolve()
    )
    out_rel = _normalize_relative_ref(out_dir, field_name="out_dir")
    out_dir_path = _safe_join(root, out_rel, field_name="out_dir")
    out_dir_path.mkdir(parents=True, exist_ok=True)

    parent_report_ref = _require_exactly_one(
        parent_worker_boundary_conformance_report_refs,
        field_name="parent_worker_boundary_conformance_report_refs",
    )
    child_report_ref = _require_exactly_one(
        child_worker_boundary_conformance_report_refs,
        field_name="child_worker_boundary_conformance_report_refs",
    )
    parent_role_kind = _normalize_role_kind(
        _require_exactly_one(parent_role_kinds, field_name="parent_role_kinds"),
        field_name="parent_role_kinds",
    )
    child_role_kind = _normalize_role_kind(
        _require_exactly_one(child_role_kinds, field_name="child_role_kinds"),
        field_name="child_role_kinds",
    )
    delegation_edge_id = _require_exactly_one(
        delegation_edge_ids,
        field_name="delegation_edge_ids",
    )
    delegated_task_identity = _require_exactly_one(
        delegated_task_identities,
        field_name="delegated_task_identities",
    )

    parent_report = _load_payload_model(
        root=root,
        ref=parent_report_ref,
        field_name="parent_worker_boundary_conformance_report_ref",
        expected_schema=WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA,
        model=WorkerBoundaryConformanceReport,
    )
    child_report = _load_payload_model(
        root=root,
        ref=child_report_ref,
        field_name="child_worker_boundary_conformance_report_ref",
        expected_schema=WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA,
        model=WorkerBoundaryConformanceReport,
    )

    parent_chain = _resolve_support_chain(root=root, report=parent_report, report_role="parent")
    child_chain = _resolve_support_chain(root=root, report=child_report, report_role="child")

    supporting_diagnostic_families: set[SupportingDiagnosticFamily] = set()
    incomplete_lineage = False
    rejected = False

    if not parent_chain.lineage_complete or not child_chain.lineage_complete:
        supporting_diagnostic_families.add("lineage_mismatch")
        incomplete_lineage = True

    if parent_report.overall_judgment == "incomplete_evidence":
        supporting_diagnostic_families.add("lineage_mismatch")
        incomplete_lineage = True
    elif parent_report.overall_judgment == "non_conformant":
        supporting_diagnostic_families.add("non_conformant_parent")
        rejected = True

    if child_report.overall_judgment == "incomplete_evidence":
        supporting_diagnostic_families.add("lineage_mismatch")
        incomplete_lineage = True
    elif child_report.overall_judgment == "non_conformant":
        supporting_diagnostic_families.add("non_conformant_child")
        rejected = True

    if parent_role_kind != "supervisor" or child_role_kind != "worker":
        supporting_diagnostic_families.add("role_ambiguity")
        rejected = True

    if (
        parent_report.worker_subject_ref == child_report.worker_subject_ref
        or parent_report.worker_boundary_conformance_report_id
        == child_report.worker_boundary_conformance_report_id
        or parent_report_ref == child_report_ref
        or parent_report.task_instance_identity == child_report.task_instance_identity
    ):
        supporting_diagnostic_families.add("recursive_topology_forbidden")
        rejected = True

    if (
        parent_report.repo_ref != child_report.repo_ref
        or parent_report.snapshot_id != child_report.snapshot_id
        or parent_report.snapshot_sha256 != child_report.snapshot_sha256
    ):
        supporting_diagnostic_families.add("repo_snapshot_mismatch")
        rejected = True

    parent_boundary_hash = (
        parent_chain.compiled_binding.compiled_boundary_identity_hash
        if parent_chain.compiled_binding is not None
        else None
    )
    child_boundary_hash = (
        child_chain.compiled_binding.compiled_boundary_identity_hash
        if child_chain.compiled_binding is not None
        else None
    )
    if parent_boundary_hash is None or child_boundary_hash is None:
        supporting_diagnostic_families.add("lineage_mismatch")
        incomplete_lineage = True
    elif parent_boundary_hash != child_boundary_hash:
        supporting_diagnostic_families.add("compiled_boundary_mismatch")
        rejected = True

    if incomplete_lineage:
        handoff_result: HandoffResult = "incomplete_lineage"
    elif rejected:
        handoff_result = "rejected"
    else:
        handoff_result = "completed"

    ordered_families = sorted(
        supporting_diagnostic_families,
        key=_DIAGNOSTIC_FAMILY_ORDER.index,
    )
    supporting_diagnostic_ids = [
        _diagnostic_id_for(family) for family in ordered_families
    ]
    topology_payload = {
        "snapshot_id": parent_report.snapshot_id,
        "snapshot_sha256": parent_report.snapshot_sha256,
        "repo_ref": parent_report.repo_ref,
        "parent_worker_boundary_conformance_report_ref": parent_report_ref,
        "child_worker_boundary_conformance_report_ref": child_report_ref,
        "parent_boundary_instance_ref": parent_report.boundary_instance_ref,
        "child_boundary_instance_ref": child_report.boundary_instance_ref,
        "parent_compiled_binding_ref": parent_report.compiled_binding_ref,
        "child_compiled_binding_ref": child_report.compiled_binding_ref,
        "parent_task_instance_identity": parent_report.task_instance_identity,
        "child_task_instance_identity": child_report.task_instance_identity,
        "parent_worker_subject_kind": parent_report.worker_subject_kind,
        "parent_worker_subject_ref": parent_report.worker_subject_ref,
        "child_worker_subject_kind": child_report.worker_subject_kind,
        "child_worker_subject_ref": child_report.worker_subject_ref,
        "parent_role_kind": parent_role_kind,
        "child_role_kind": child_role_kind,
        "delegation_edge_id": delegation_edge_id,
        "delegated_task_identity": delegated_task_identity,
        "handoff_result": handoff_result,
        "supporting_diagnostic_ids": supporting_diagnostic_ids,
        "supporting_diagnostic_families": ordered_families,
        "semantic_hash": "0" * 64,
    }
    topology_id_payload = {
        **topology_payload,
        "parent_report_semantic_hash": parent_report.semantic_hash,
        "child_report_semantic_hash": child_report.semantic_hash,
        "parent_boundary_instance_semantic_hash": (
            parent_chain.boundary_instance.semantic_hash
            if parent_chain.boundary_instance is not None
            else None
        ),
        "child_boundary_instance_semantic_hash": (
            child_chain.boundary_instance.semantic_hash
            if child_chain.boundary_instance is not None
            else None
        ),
        "parent_compiled_binding_semantic_hash": (
            parent_chain.compiled_binding.semantic_hash
            if parent_chain.compiled_binding is not None
            else None
        ),
        "child_compiled_binding_semantic_hash": (
            child_chain.compiled_binding.semantic_hash
            if child_chain.compiled_binding is not None
            else None
        ),
        "parent_lineage_complete": parent_chain.lineage_complete,
        "child_lineage_complete": child_chain.lineage_complete,
    }
    topology = WorkerDelegationTopology.model_validate(
        {
            "schema": WORKER_DELEGATION_TOPOLOGY_SCHEMA,
            "worker_delegation_topology_id": _derive_topology_id(topology_id_payload),
            **topology_payload,
        }
    )

    topology_path = out_dir_path / "worker_delegation_topology.json"
    topology_path.write_text(
        _serialize_payload(topology.model_dump(mode="json")),
        encoding="utf-8",
    )
    return WorkerDelegationTopologyResult(
        topology=topology,
        topology_path=topology_path,
    )
