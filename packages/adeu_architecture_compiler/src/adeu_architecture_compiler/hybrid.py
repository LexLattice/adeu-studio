from __future__ import annotations

import re
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_architecture_ir import ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA, AdeuArchitectureSemanticIR
from adeu_architecture_ir.root_family import ArchitectureResolutionRoute
from pydantic import BaseModel, ConfigDict, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json, sha256_text

from .conformance import (
    AdeuArchitectureConformanceReport,
    ArchitectureConsumedRootRef,
    _assert_non_empty_text,
    _assert_sorted_unique,
    _dump_json_payload,
    _load_repo_json,
    _normalize_repo_relative_path,
    _sha256_repo_file,
    _validation_context,
    canonicalize_adeu_architecture_conformance_report_payload,
)

ADEU_ARCHITECTURE_ORACLE_REQUEST_SCHEMA = "adeu_architecture_oracle_request@1"
ADEU_ARCHITECTURE_ORACLE_RESOLUTION_SCHEMA = "adeu_architecture_oracle_resolution@1"
ADEU_ARCHITECTURE_CHECKPOINT_TRACE_SCHEMA = "adeu_architecture_checkpoint_trace@1"
ADEU_ARCHITECTURE_IR_DELTA_SCHEMA = "adeu_architecture_ir_delta@1"
V40C_V79_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS79.md#v79-continuation-contract-machine-checkable"
)

ArchitectureCheckpointClass = Literal[
    "deterministic_pass",
    "deterministic_fail",
    "oracle_needed",
    "human_needed",
]
ArchitectureFinalAdjudication = Literal[
    "resolved_pass",
    "resolved_fail",
    "escalated_human",
]
ArchitectureResolutionState = Literal[
    "advisory_support",
    "advisory_reject",
    "inconclusive",
    "contradictory",
]
ArchitectureOracleResolutionOrigin = Literal["fresh_model_output", "cache_replay"]
ArchitectureReasoningEffort = Literal["low", "medium", "high", "xhigh"]
ArchitectureCheckpointSourceKind = Literal["ambiguity", "human_escalation"]
ArchitectureDeltaOperationKind = Literal["replace_text", "append_list_item", "bind_placeholder"]

_HEX_64_RE = re.compile(r"^[0-9a-f]{64}$")
_ALLOWED_GENERIC_HYBRID_FAILURES = {"ASIR-P-001", "ASIR-P-002", "ASIR-E-002"}
_ALLOWED_ORACLE_FAILURES = {"ASIR-P-001", "ASIR-P-002"}
_HUMAN_ESCALATION_DISPOSITIONS = {"escalated_human", "human_review"}
_HYBRID_POLICY_SOURCE_PATHS = (
    "AGENTS.md",
    "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS79.md",
)
_PROHIBITED_DELTA_FIELD_PATH_FRAGMENTS = (
    "authority_boundary_policy",
    "authority_source_ref",
    "boundary_class",
    "capability_id",
    "escalate_to",
)


def _expected_final_adjudication_for_checkpoint_class(
    checkpoint_class: ArchitectureCheckpointClass,
) -> ArchitectureFinalAdjudication | None:
    mapping: dict[ArchitectureCheckpointClass, ArchitectureFinalAdjudication | None] = {
        "deterministic_pass": "resolved_pass",
        "deterministic_fail": "resolved_fail",
        "oracle_needed": None,
        "human_needed": "escalated_human",
    }
    return mapping[checkpoint_class]


def _expected_final_adjudication_for_resolution_state(
    resolution_state: ArchitectureResolutionState,
) -> ArchitectureFinalAdjudication:
    mapping: dict[ArchitectureResolutionState, ArchitectureFinalAdjudication] = {
        "advisory_support": "resolved_pass",
        "advisory_reject": "resolved_fail",
        "inconclusive": "escalated_human",
        "contradictory": "escalated_human",
    }
    return mapping[resolution_state]


def _policy_source_hash_entries(*, repository_root: Path | None = None) -> list[dict[str, str]]:
    return [
        {
            "path": path_text,
            "sha256": _sha256_repo_file(path_text, repository_root=repository_root),
        }
        for path_text in _HYBRID_POLICY_SOURCE_PATHS
    ]


def _policy_source_paths() -> list[str]:
    return list(_HYBRID_POLICY_SOURCE_PATHS)


def _replay_identity_hash(payload: dict[str, Any]) -> str:
    return sha256_canonical_json(payload)


def _drop_none(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: _drop_none(item) for key, item in value.items() if item is not None}
    if isinstance(value, list):
        return [_drop_none(item) for item in value]
    return value


def _checkpoint_id(
    *,
    architecture_id: str,
    semantic_hash: str,
    source_kind: ArchitectureCheckpointSourceKind,
    source_ref: str,
    checkpoint_class: ArchitectureCheckpointClass,
    resolution_route: ArchitectureResolutionRoute,
) -> str:
    digest = sha256_canonical_json(
        {
            "architecture_id": architecture_id,
            "checkpoint_class": checkpoint_class,
            "resolution_route": resolution_route,
            "semantic_hash": semantic_hash,
            "source_kind": source_kind,
            "source_ref": source_ref,
        }
    )[:16]
    return f"v40c_v79_checkpoint_{digest}"


def _oracle_request_id(*, checkpoint_id: str, replay_identity: dict[str, Any]) -> str:
    digest = sha256_canonical_json(
        {
            "checkpoint_id": checkpoint_id,
            "replay_identity_hash": _replay_identity_hash(replay_identity),
        }
    )[:16]
    return f"v40c_v79_oracle_request_{digest}"


def _oracle_resolution_id(
    *,
    request_id: str,
    resolution_state: ArchitectureResolutionState,
    resolution_origin: ArchitectureOracleResolutionOrigin,
    raw_output_hash: str,
    model_id: str,
    model_version: str,
    reasoning_effort: ArchitectureReasoningEffort,
) -> str:
    digest = sha256_canonical_json(
        {
            "model_id": model_id,
            "model_version": model_version,
            "raw_output_hash": raw_output_hash,
            "reasoning_effort": reasoning_effort,
            "request_id": request_id,
            "resolution_origin": resolution_origin,
            "resolution_state": resolution_state,
        }
    )[:16]
    return f"v40c_v79_oracle_resolution_{digest}"


def _delta_id(
    *,
    source_resolution_id: str,
    scope_ref: str,
    target_refs: list[str],
    authorized_placeholder_refs: list[str],
    operation_set: list[dict[str, Any]],
) -> str:
    digest = sha256_canonical_json(
        {
            "authorized_placeholder_refs": authorized_placeholder_refs,
            "operation_set": operation_set,
            "scope_ref": scope_ref,
            "source_resolution_id": source_resolution_id,
            "target_refs": target_refs,
        }
    )[:16]
    return f"v40c_v79_ir_delta_{digest}"


def _trace_id(
    *,
    architecture_id: str,
    semantic_hash: str,
    conformance_report_ref: str,
    checkpoint_entries: list[dict[str, Any]],
) -> str:
    digest = sha256_canonical_json(
        {
            "architecture_id": architecture_id,
            "checkpoint_entries": [_drop_none(entry) for entry in checkpoint_entries],
            "conformance_report_ref": conformance_report_ref,
            "semantic_hash": semantic_hash,
        }
    )[:16]
    return f"v40c_v79_trace_{digest}"


def _conformance_root_ref(
    report: AdeuArchitectureConformanceReport,
    *,
    artifact_schema: str,
) -> ArchitectureConsumedRootRef:
    matches = [ref for ref in report.consumed_root_refs if ref.artifact_schema == artifact_schema]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one consumed_root_ref for {artifact_schema}")
    return matches[0]


def _semantic_root_ref_set(semantic_ir: AdeuArchitectureSemanticIR) -> set[str]:
    ontology_refs = (
        {item.actor_id for item in semantic_ir.ontology.actors}
        | {item.surface_id for item in semantic_ir.ontology.surfaces}
        | {item.object_id for item in semantic_ir.ontology.data_objects}
        | {item.boundary_id for item in semantic_ir.ontology.boundaries}
        | {item.capability_id for item in semantic_ir.ontology.capabilities}
        | {item.workflow_id for item in semantic_ir.ontology.workflows}
        | {item.step_id for item in semantic_ir.ontology.flow_steps}
        | {item.state_id for item in semantic_ir.ontology.states}
        | {item.transition_id for item in semantic_ir.ontology.transitions}
        | {item.decision_id for item in semantic_ir.ontology.decisions}
        | {item.failure_mode_id for item in semantic_ir.ontology.failure_modes}
    )
    source_ref_ids = {item.source_ref_id for item in semantic_ir.source_set.sources}
    epistemic_refs = (
        {item.fact_id for item in semantic_ir.epistemics.facts}
        | {item.assumption_id for item in semantic_ir.epistemics.assumptions}
        | {item.ambiguity_id for item in semantic_ir.epistemics.ambiguities}
        | {item.evidence_id for item in semantic_ir.epistemics.evidence_requirements}
        | {item.hook_id for item in semantic_ir.epistemics.observability_hooks}
        | {item.annotation_id for item in semantic_ir.epistemics.annotations}
    )
    deontic_refs = (
        {item.obligation_id for item in semantic_ir.deontics.obligations}
        | {item.prohibition_id for item in semantic_ir.deontics.prohibitions}
        | {item.permission_id for item in semantic_ir.deontics.permissions}
        | {item.gate_id for item in semantic_ir.deontics.gates}
        | {item.invariant_id for item in semantic_ir.deontics.invariants}
        | {item.rule_id for item in semantic_ir.deontics.escalation_rules}
    )
    utility_refs = (
        {item.goal_id for item in semantic_ir.utility.goals}
        | {item.metric_id for item in semantic_ir.utility.metrics}
        | {item.priority_id for item in semantic_ir.utility.priority_rules}
        | {item.tradeoff_id for item in semantic_ir.utility.tradeoffs}
    )
    return ontology_refs | source_ref_ids | epistemic_refs | deontic_refs | utility_refs


class ArchitecturePolicySourceHash(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    path: str
    sha256: str

    @model_validator(mode="after")
    def _validate_entry(self, info: ValidationInfo) -> ArchitecturePolicySourceHash:
        object.__setattr__(
            self,
            "path",
            _normalize_repo_relative_path(self.path, field_name="policy_source_hashes.path"),
        )
        object.__setattr__(
            self,
            "sha256",
            _assert_non_empty_text(self.sha256, field_name="policy_source_hashes.sha256"),
        )
        if not _HEX_64_RE.match(self.sha256):
            raise ValueError("policy_source_hashes.sha256 must be a 64-character lowercase sha256")
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            actual_hash = _sha256_repo_file(self.path, repository_root=repository_root)
            if self.sha256 != actual_hash:
                raise ValueError("policy_source_hashes.sha256 must match repo file contents")
        return self


class ArchitectureOracleReplayIdentity(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    intent_packet_hash: str
    semantic_hash: str
    conformance_report_ref: str
    policy_source_hashes: list[ArchitecturePolicySourceHash]
    model_id: str
    model_version: str
    reasoning_effort: ArchitectureReasoningEffort
    prompt_template_version: str
    compiler_version: str
    context_refs: list[str]

    @model_validator(mode="after")
    def _validate_identity(self) -> ArchitectureOracleReplayIdentity:
        object.__setattr__(
            self,
            "intent_packet_hash",
            _assert_non_empty_text(
                self.intent_packet_hash,
                field_name="replay_identity.intent_packet_hash",
            ),
        )
        object.__setattr__(
            self,
            "semantic_hash",
            _assert_non_empty_text(self.semantic_hash, field_name="replay_identity.semantic_hash"),
        )
        if not _HEX_64_RE.match(self.intent_packet_hash):
            raise ValueError(
                "replay_identity.intent_packet_hash must be a 64-character lowercase sha256"
            )
        if not _HEX_64_RE.match(self.semantic_hash):
            raise ValueError(
                "replay_identity.semantic_hash must be a 64-character lowercase sha256"
            )
        object.__setattr__(
            self,
            "conformance_report_ref",
            _normalize_repo_relative_path(
                self.conformance_report_ref,
                field_name="replay_identity.conformance_report_ref",
            ),
        )
        object.__setattr__(
            self,
            "model_id",
            _assert_non_empty_text(self.model_id, field_name="replay_identity.model_id"),
        )
        object.__setattr__(
            self,
            "model_version",
            _assert_non_empty_text(
                self.model_version,
                field_name="replay_identity.model_version",
            ),
        )
        object.__setattr__(
            self,
            "prompt_template_version",
            _assert_non_empty_text(
                self.prompt_template_version,
                field_name="replay_identity.prompt_template_version",
            ),
        )
        object.__setattr__(
            self,
            "compiler_version",
            _assert_non_empty_text(
                self.compiler_version,
                field_name="replay_identity.compiler_version",
            ),
        )
        object.__setattr__(
            self,
            "context_refs",
            _assert_sorted_unique(self.context_refs, field_name="replay_identity.context_refs"),
        )
        policy_paths = [item.path for item in self.policy_source_hashes]
        if policy_paths != _policy_source_paths():
            raise ValueError(
                "replay_identity.policy_source_hashes must match the fixed V40-C policy source set"
            )
        return self


class AdeuArchitectureOracleRequest(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_ORACLE_REQUEST_SCHEMA]
    request_id: str
    architecture_id: str
    semantic_hash: str
    conformance_report_ref: str
    checkpoint_id: str
    ambiguity_ref: str
    checkpoint_class: Literal["oracle_needed"]
    replay_identity: ArchitectureOracleReplayIdentity
    policy_source_hashes: list[ArchitecturePolicySourceHash]
    model_id: str
    model_version: str
    reasoning_effort: ArchitectureReasoningEffort
    prompt_template_version: str
    compiler_version: str
    context_refs: list[str]

    @model_validator(mode="after")
    def _validate_request(self, info: ValidationInfo) -> AdeuArchitectureOracleRequest:
        object.__setattr__(
            self, "request_id", _assert_non_empty_text(self.request_id, field_name="request_id")
        )
        object.__setattr__(
            self,
            "architecture_id",
            _assert_non_empty_text(self.architecture_id, field_name="architecture_id"),
        )
        object.__setattr__(
            self,
            "semantic_hash",
            _assert_non_empty_text(self.semantic_hash, field_name="semantic_hash"),
        )
        if not _HEX_64_RE.match(self.semantic_hash):
            raise ValueError("semantic_hash must be a 64-character lowercase sha256")
        object.__setattr__(
            self,
            "conformance_report_ref",
            _normalize_repo_relative_path(
                self.conformance_report_ref,
                field_name="conformance_report_ref",
            ),
        )
        object.__setattr__(
            self,
            "checkpoint_id",
            _assert_non_empty_text(self.checkpoint_id, field_name="checkpoint_id"),
        )
        object.__setattr__(
            self,
            "ambiguity_ref",
            _assert_non_empty_text(self.ambiguity_ref, field_name="ambiguity_ref"),
        )
        object.__setattr__(
            self, "model_id", _assert_non_empty_text(self.model_id, field_name="model_id")
        )
        object.__setattr__(
            self,
            "model_version",
            _assert_non_empty_text(self.model_version, field_name="model_version"),
        )
        object.__setattr__(
            self,
            "prompt_template_version",
            _assert_non_empty_text(
                self.prompt_template_version,
                field_name="prompt_template_version",
            ),
        )
        object.__setattr__(
            self,
            "compiler_version",
            _assert_non_empty_text(self.compiler_version, field_name="compiler_version"),
        )
        object.__setattr__(
            self,
            "context_refs",
            _assert_sorted_unique(self.context_refs, field_name="context_refs"),
        )
        if self.policy_source_hashes != self.replay_identity.policy_source_hashes:
            raise ValueError("policy_source_hashes must match replay_identity.policy_source_hashes")
        if self.model_id != self.replay_identity.model_id:
            raise ValueError("model_id must match replay_identity.model_id")
        if self.model_version != self.replay_identity.model_version:
            raise ValueError("model_version must match replay_identity.model_version")
        if self.reasoning_effort != self.replay_identity.reasoning_effort:
            raise ValueError("reasoning_effort must match replay_identity.reasoning_effort")
        if self.prompt_template_version != self.replay_identity.prompt_template_version:
            raise ValueError(
                "prompt_template_version must match replay_identity.prompt_template_version"
            )
        if self.compiler_version != self.replay_identity.compiler_version:
            raise ValueError("compiler_version must match replay_identity.compiler_version")
        if self.context_refs != self.replay_identity.context_refs:
            raise ValueError("context_refs must match replay_identity.context_refs")
        if self.semantic_hash != self.replay_identity.semantic_hash:
            raise ValueError("semantic_hash must match replay_identity.semantic_hash")
        if self.conformance_report_ref != self.replay_identity.conformance_report_ref:
            raise ValueError(
                "conformance_report_ref must match replay_identity.conformance_report_ref"
            )
        expected_request_id = _oracle_request_id(
            checkpoint_id=self.checkpoint_id,
            replay_identity=_dump_json_payload(self.replay_identity),
        )
        if self.request_id != expected_request_id:
            raise ValueError("request_id must match checkpoint_id and replay_identity")
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            report_payload = _load_repo_json(
                self.conformance_report_ref,
                repository_root=repository_root,
            )
            report = AdeuArchitectureConformanceReport.model_validate(
                report_payload,
                context=_validation_context(repository_root),
            )
            if report.architecture_id != self.architecture_id:
                raise ValueError("architecture_id must match the referenced conformance report")
            if report.semantic_hash != self.semantic_hash:
                raise ValueError("semantic_hash must match the referenced conformance report")
            intent_ref = _conformance_root_ref(
                report,
                artifact_schema=ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
            )
            if self.replay_identity.intent_packet_hash != intent_ref.sha256:
                raise ValueError(
                    "replay_identity.intent_packet_hash must match the consumed intent packet hash"
                )
        return self


class AdeuArchitectureOracleResolution(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_ORACLE_RESOLUTION_SCHEMA]
    resolution_id: str
    request_id: str
    request_ref: str | None = None
    checkpoint_id: str
    architecture_id: str
    semantic_hash: str
    model_id: str
    model_version: str
    reasoning_effort: ArchitectureReasoningEffort
    raw_output_hash: str
    resolution_state: ArchitectureResolutionState
    proposed_delta_ref: str | None = None
    resolution_origin: ArchitectureOracleResolutionOrigin = "fresh_model_output"

    @model_validator(mode="after")
    def _validate_resolution(self, info: ValidationInfo) -> AdeuArchitectureOracleResolution:
        object.__setattr__(
            self,
            "resolution_id",
            _assert_non_empty_text(self.resolution_id, field_name="resolution_id"),
        )
        object.__setattr__(
            self, "request_id", _assert_non_empty_text(self.request_id, field_name="request_id")
        )
        if self.request_ref is not None:
            object.__setattr__(
                self,
                "request_ref",
                _normalize_repo_relative_path(self.request_ref, field_name="request_ref"),
            )
        object.__setattr__(
            self,
            "checkpoint_id",
            _assert_non_empty_text(self.checkpoint_id, field_name="checkpoint_id"),
        )
        object.__setattr__(
            self,
            "architecture_id",
            _assert_non_empty_text(self.architecture_id, field_name="architecture_id"),
        )
        object.__setattr__(
            self,
            "semantic_hash",
            _assert_non_empty_text(self.semantic_hash, field_name="semantic_hash"),
        )
        if not _HEX_64_RE.match(self.semantic_hash):
            raise ValueError("semantic_hash must be a 64-character lowercase sha256")
        object.__setattr__(
            self, "model_id", _assert_non_empty_text(self.model_id, field_name="model_id")
        )
        object.__setattr__(
            self,
            "model_version",
            _assert_non_empty_text(self.model_version, field_name="model_version"),
        )
        object.__setattr__(
            self,
            "raw_output_hash",
            _assert_non_empty_text(self.raw_output_hash, field_name="raw_output_hash"),
        )
        if not _HEX_64_RE.match(self.raw_output_hash):
            raise ValueError("raw_output_hash must be a 64-character lowercase sha256")
        if self.proposed_delta_ref is not None:
            object.__setattr__(
                self,
                "proposed_delta_ref",
                _assert_non_empty_text(self.proposed_delta_ref, field_name="proposed_delta_ref"),
            )
        if self.proposed_delta_ref is not None and self.resolution_state not in {
            "advisory_support",
            "advisory_reject",
        }:
            raise ValueError(
                "proposed_delta_ref is allowed only for advisory_support or advisory_reject"
            )
        expected_resolution_id = _oracle_resolution_id(
            request_id=self.request_id,
            resolution_state=self.resolution_state,
            resolution_origin=self.resolution_origin,
            raw_output_hash=self.raw_output_hash,
            model_id=self.model_id,
            model_version=self.model_version,
            reasoning_effort=self.reasoning_effort,
        )
        if self.resolution_id != expected_resolution_id:
            raise ValueError(
                "resolution_id must match request_id, resolution_state, provenance, "
                "and raw_output_hash"
            )
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None and self.request_ref is not None:
            request_payload = _load_repo_json(self.request_ref, repository_root=repository_root)
            request = AdeuArchitectureOracleRequest.model_validate(
                request_payload,
                context=_validation_context(repository_root),
            )
            if request.request_id != self.request_id:
                raise ValueError("request_id must match the referenced oracle request")
            if request.checkpoint_id != self.checkpoint_id:
                raise ValueError("checkpoint_id must match the referenced oracle request")
            if request.architecture_id != self.architecture_id:
                raise ValueError("architecture_id must match the referenced oracle request")
            if request.semantic_hash != self.semantic_hash:
                raise ValueError("semantic_hash must match the referenced oracle request")
            if request.model_id != self.model_id:
                raise ValueError("model_id must match the referenced oracle request")
            if request.model_version != self.model_version:
                raise ValueError("model_version must match the referenced oracle request")
            if request.reasoning_effort != self.reasoning_effort:
                raise ValueError("reasoning_effort must match the referenced oracle request")
        return self


class ArchitectureIRDeltaOperation(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    operation_id: str
    operation_kind: ArchitectureDeltaOperationKind
    target_ref: str
    field_path: str
    value: str
    placeholder_ref: str | None = None

    @model_validator(mode="after")
    def _validate_operation(self) -> ArchitectureIRDeltaOperation:
        object.__setattr__(
            self,
            "operation_id",
            _assert_non_empty_text(self.operation_id, field_name="operation_id"),
        )
        object.__setattr__(
            self,
            "target_ref",
            _assert_non_empty_text(self.target_ref, field_name="target_ref"),
        )
        object.__setattr__(
            self, "field_path", _assert_non_empty_text(self.field_path, field_name="field_path")
        )
        object.__setattr__(self, "value", _assert_non_empty_text(self.value, field_name="value"))
        lowered_field_path = self.field_path.lower()
        if any(
            fragment in lowered_field_path for fragment in _PROHIBITED_DELTA_FIELD_PATH_FRAGMENTS
        ):
            raise ValueError("operation_set must not rewrite authority or boundary provenance")
        if self.placeholder_ref is not None:
            object.__setattr__(
                self,
                "placeholder_ref",
                _assert_non_empty_text(self.placeholder_ref, field_name="placeholder_ref"),
            )
        if self.operation_kind == "bind_placeholder" and self.placeholder_ref is None:
            raise ValueError("bind_placeholder operations require placeholder_ref")
        return self


class AdeuArchitectureIRDelta(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_IR_DELTA_SCHEMA]
    delta_id: str
    architecture_id: str
    semantic_hash: str
    checkpoint_id: str
    source_resolution_id: str
    scope_ref: str
    target_refs: list[str]
    authorized_placeholder_refs: list[str]
    operation_set: list[ArchitectureIRDeltaOperation]

    @model_validator(mode="after")
    def _validate_delta(self) -> AdeuArchitectureIRDelta:
        object.__setattr__(
            self, "delta_id", _assert_non_empty_text(self.delta_id, field_name="delta_id")
        )
        object.__setattr__(
            self,
            "architecture_id",
            _assert_non_empty_text(self.architecture_id, field_name="architecture_id"),
        )
        object.__setattr__(
            self,
            "semantic_hash",
            _assert_non_empty_text(self.semantic_hash, field_name="semantic_hash"),
        )
        if not _HEX_64_RE.match(self.semantic_hash):
            raise ValueError("semantic_hash must be a 64-character lowercase sha256")
        object.__setattr__(
            self,
            "checkpoint_id",
            _assert_non_empty_text(self.checkpoint_id, field_name="checkpoint_id"),
        )
        object.__setattr__(
            self,
            "source_resolution_id",
            _assert_non_empty_text(
                self.source_resolution_id,
                field_name="source_resolution_id",
            ),
        )
        object.__setattr__(
            self, "scope_ref", _assert_non_empty_text(self.scope_ref, field_name="scope_ref")
        )
        object.__setattr__(
            self, "target_refs", _assert_sorted_unique(self.target_refs, field_name="target_refs")
        )
        object.__setattr__(
            self,
            "authorized_placeholder_refs",
            _assert_sorted_unique(
                self.authorized_placeholder_refs,
                field_name="authorized_placeholder_refs",
            ),
        )
        if not self.operation_set:
            raise ValueError("operation_set must not be empty")
        operation_ids = [item.operation_id for item in self.operation_set]
        if sorted(operation_ids) != operation_ids or len(operation_ids) != len(set(operation_ids)):
            raise ValueError("operation_set must be sorted by operation_id with no duplicates")
        allowed_refs = set(self.target_refs) | set(self.authorized_placeholder_refs)
        for operation in self.operation_set:
            if operation.target_ref not in allowed_refs:
                raise ValueError(
                    "operation.target_ref must remain within target or placeholder refs"
                )
            if (
                operation.placeholder_ref is not None
                and operation.placeholder_ref not in self.authorized_placeholder_refs
            ):
                raise ValueError(
                    "operation.placeholder_ref must remain within authorized_placeholder_refs"
                )
        expected_delta_id = _delta_id(
            source_resolution_id=self.source_resolution_id,
            scope_ref=self.scope_ref,
            target_refs=self.target_refs,
            authorized_placeholder_refs=self.authorized_placeholder_refs,
            operation_set=[_dump_json_payload(item) for item in self.operation_set],
        )
        if self.delta_id != expected_delta_id:
            raise ValueError(
                "delta_id must match source_resolution_id, scope_ref, target_refs, "
                "placeholders, and operation_set"
            )
        return self


class ArchitectureHybridAdjudicator(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    name: Literal["adeu_architecture_compiler.v40c.adjudicator"] = (
        "adeu_architecture_compiler.v40c.adjudicator"
    )
    version: str = "1"
    one_round_only: Literal[True] = True
    contract_source: str = V40C_V79_CONTRACT_SOURCE

    @model_validator(mode="after")
    def _validate_adjudicator(self) -> ArchitectureHybridAdjudicator:
        object.__setattr__(
            self, "version", _assert_non_empty_text(self.version, field_name="adjudicator.version")
        )
        object.__setattr__(
            self,
            "contract_source",
            _assert_non_empty_text(
                self.contract_source,
                field_name="adjudicator.contract_source",
            ),
        )
        return self


class ArchitectureCheckpointTraceEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    checkpoint_id: str
    ambiguity_ref: str
    human_escalation_ref: str | None = None
    checkpoint_class: ArchitectureCheckpointClass
    resolution_route: ArchitectureResolutionRoute
    oracle_request_ref: str | None = None
    oracle_resolution_ref: str | None = None
    final_adjudication: ArchitectureFinalAdjudication
    replay_identity_hash: str

    @model_validator(mode="after")
    def _validate_entry(self) -> ArchitectureCheckpointTraceEntry:
        object.__setattr__(
            self,
            "checkpoint_id",
            _assert_non_empty_text(self.checkpoint_id, field_name="checkpoint_id"),
        )
        object.__setattr__(
            self,
            "ambiguity_ref",
            _assert_non_empty_text(self.ambiguity_ref, field_name="ambiguity_ref"),
        )
        if self.human_escalation_ref is not None:
            object.__setattr__(
                self,
                "human_escalation_ref",
                _assert_non_empty_text(
                    self.human_escalation_ref,
                    field_name="human_escalation_ref",
                ),
            )
        if self.oracle_request_ref is not None:
            object.__setattr__(
                self,
                "oracle_request_ref",
                _normalize_repo_relative_path(
                    self.oracle_request_ref,
                    field_name="oracle_request_ref",
                ),
            )
        if self.oracle_resolution_ref is not None:
            object.__setattr__(
                self,
                "oracle_resolution_ref",
                _normalize_repo_relative_path(
                    self.oracle_resolution_ref,
                    field_name="oracle_resolution_ref",
                ),
            )
        object.__setattr__(
            self,
            "replay_identity_hash",
            _assert_non_empty_text(
                self.replay_identity_hash,
                field_name="replay_identity_hash",
            ),
        )
        if not _HEX_64_RE.match(self.replay_identity_hash):
            raise ValueError("replay_identity_hash must be a 64-character lowercase sha256")
        expected_final = _expected_final_adjudication_for_checkpoint_class(self.checkpoint_class)
        if expected_final is not None and self.final_adjudication != expected_final:
            raise ValueError(
                "final_adjudication must match the frozen deterministic or human transition law"
            )
        if self.checkpoint_class in {"deterministic_pass", "deterministic_fail"}:
            if self.resolution_route != "deterministic_only":
                raise ValueError(
                    "deterministic checkpoint classes require resolution_route deterministic_only"
                )
            if self.oracle_request_ref is not None or self.oracle_resolution_ref is not None:
                raise ValueError("deterministic checkpoint classes must not carry oracle refs")
        elif self.checkpoint_class == "human_needed":
            if self.resolution_route != "human_only":
                raise ValueError("human_needed checkpoints require resolution_route human_only")
            if self.oracle_request_ref is not None or self.oracle_resolution_ref is not None:
                raise ValueError("human_needed checkpoints must not carry oracle refs")
        else:
            if self.resolution_route != "oracle_assisted":
                raise ValueError(
                    "oracle_needed checkpoints require resolution_route oracle_assisted"
                )
            if self.oracle_request_ref is None:
                raise ValueError("oracle_needed checkpoints require oracle_request_ref")
        if self.oracle_resolution_ref is not None and self.oracle_request_ref is None:
            raise ValueError("oracle_resolution_ref requires oracle_request_ref")
        return self


class AdeuArchitectureCheckpointTrace(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_CHECKPOINT_TRACE_SCHEMA]
    trace_id: str
    architecture_id: str
    semantic_hash: str
    conformance_report_ref: str
    compiler_version: str
    hybrid_policy_hashes: list[ArchitecturePolicySourceHash]
    adjudicator: ArchitectureHybridAdjudicator
    checkpoint_entries: list[ArchitectureCheckpointTraceEntry]

    @model_validator(mode="after")
    def _validate_trace(self, info: ValidationInfo) -> AdeuArchitectureCheckpointTrace:
        object.__setattr__(
            self, "trace_id", _assert_non_empty_text(self.trace_id, field_name="trace_id")
        )
        object.__setattr__(
            self,
            "architecture_id",
            _assert_non_empty_text(self.architecture_id, field_name="architecture_id"),
        )
        object.__setattr__(
            self,
            "semantic_hash",
            _assert_non_empty_text(self.semantic_hash, field_name="semantic_hash"),
        )
        if not _HEX_64_RE.match(self.semantic_hash):
            raise ValueError("semantic_hash must be a 64-character lowercase sha256")
        object.__setattr__(
            self,
            "conformance_report_ref",
            _normalize_repo_relative_path(
                self.conformance_report_ref,
                field_name="conformance_report_ref",
            ),
        )
        object.__setattr__(
            self,
            "compiler_version",
            _assert_non_empty_text(self.compiler_version, field_name="compiler_version"),
        )
        if [entry.path for entry in self.hybrid_policy_hashes] != _policy_source_paths():
            raise ValueError("hybrid_policy_hashes must match the fixed V40-C policy source set")
        if not self.checkpoint_entries:
            raise ValueError("checkpoint_entries must not be empty")
        checkpoint_ids = [entry.checkpoint_id for entry in self.checkpoint_entries]
        if checkpoint_ids != sorted(checkpoint_ids) or len(checkpoint_ids) != len(
            set(checkpoint_ids)
        ):
            raise ValueError(
                "checkpoint_entries must be sorted by checkpoint_id with no duplicates"
            )
        expected_trace_id = _trace_id(
            architecture_id=self.architecture_id,
            semantic_hash=self.semantic_hash,
            conformance_report_ref=self.conformance_report_ref,
            checkpoint_entries=[_dump_json_payload(entry) for entry in self.checkpoint_entries],
        )
        if self.trace_id != expected_trace_id:
            raise ValueError(
                "trace_id must match architecture_id, semantic_hash, "
                "conformance_report_ref, and checkpoint_entries"
            )
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            report_payload = _load_repo_json(
                self.conformance_report_ref,
                repository_root=repository_root,
            )
            report = AdeuArchitectureConformanceReport.model_validate(
                report_payload,
                context=_validation_context(repository_root),
            )
            if report.architecture_id != self.architecture_id:
                raise ValueError("architecture_id must match the referenced conformance report")
            if report.semantic_hash != self.semantic_hash:
                raise ValueError("semantic_hash must match the referenced conformance report")
        return self


def _validate_semantic_and_conformance(
    *,
    semantic_ir_payload: dict[str, Any],
    conformance_report_payload: dict[str, Any],
    repository_root: Path | None = None,
) -> tuple[AdeuArchitectureSemanticIR, AdeuArchitectureConformanceReport]:
    context = _validation_context(repository_root)
    semantic_ir = AdeuArchitectureSemanticIR.model_validate(semantic_ir_payload, context=context)
    conformance_report = AdeuArchitectureConformanceReport.model_validate(
        conformance_report_payload,
        context=context,
    )
    if semantic_ir.architecture_id != conformance_report.architecture_id:
        raise ValueError("semantic_ir and conformance_report must share architecture_id")
    if semantic_ir.semantic_hash != conformance_report.semantic_hash:
        raise ValueError("semantic_ir and conformance_report must share semantic_hash")
    unexpected_failures = sorted(
        check_id
        for check_id in conformance_report.failed_check_ids
        if check_id not in _ALLOWED_GENERIC_HYBRID_FAILURES
    )
    if unexpected_failures:
        raise ValueError(
            "V40-C may not consume conformance reports with structural deterministic failures: "
            + ", ".join(unexpected_failures)
        )
    return semantic_ir, conformance_report


def _classify_checkpoint(
    *,
    semantic_ir: AdeuArchitectureSemanticIR,
    conformance_report: AdeuArchitectureConformanceReport,
    checkpoint_source_kind: ArchitectureCheckpointSourceKind,
    checkpoint_subject_ref: str,
) -> dict[str, Any]:
    ambiguity_index = {item.ambiguity_id: item for item in semantic_ir.epistemics.ambiguities}
    escalation_index = {item.rule_id: item for item in semantic_ir.deontics.escalation_rules}
    if checkpoint_source_kind == "human_escalation":
        try:
            escalation = escalation_index[checkpoint_subject_ref]
        except KeyError as exc:
            raise ValueError(
                "checkpoint_subject_ref must reference a released escalation rule"
            ) from exc
        if checkpoint_subject_ref not in conformance_report.human_escalation_refs:
            raise ValueError(
                "human escalation checkpoints require released conformance "
                "human_escalation_refs lineage"
            )
        ambiguity_triggers = sorted(
            trigger_ref for trigger_ref in escalation.trigger_refs if trigger_ref in ambiguity_index
        )
        ambiguity_ref = ambiguity_triggers[0] if ambiguity_triggers else escalation.trigger_refs[0]
        return {
            "source_ref": escalation.rule_id,
            "ambiguity_ref": ambiguity_ref,
            "human_escalation_ref": escalation.rule_id,
            "resolution_route": "human_only",
            "checkpoint_class": "human_needed",
        }

    try:
        ambiguity = ambiguity_index[checkpoint_subject_ref]
    except KeyError as exc:
        raise ValueError("checkpoint_subject_ref must reference a released ambiguity") from exc
    if ambiguity.resolution_route == "oracle_assisted":
        if checkpoint_subject_ref not in conformance_report.blocking_ambiguity_refs:
            raise ValueError(
                "oracle checkpoints require released conformance blocking_ambiguity_refs lineage"
            )
        if any(
            check_id not in _ALLOWED_ORACLE_FAILURES
            for check_id in conformance_report.failed_check_ids
        ):
            raise ValueError(
                "oracle checkpoints may not reinterpret failed required deterministic checks"
            )
        checkpoint_class: ArchitectureCheckpointClass = "oracle_needed"
    elif ambiguity.resolution_route == "human_only":
        checkpoint_class = "human_needed"
    else:
        checkpoint_class = (
            "deterministic_fail"
            if (
                checkpoint_subject_ref in conformance_report.blocking_ambiguity_refs
                or (
                    "ASIR-E-002" in conformance_report.failed_check_ids
                    and ambiguity.impact_class in {"high", "critical"}
                )
            )
            else "deterministic_pass"
        )
    human_escalation_ref = next(
        (
            rule.rule_id
            for rule in semantic_ir.deontics.escalation_rules
            if checkpoint_subject_ref in rule.trigger_refs
            and rule.default_disposition in _HUMAN_ESCALATION_DISPOSITIONS
        ),
        None,
    )
    return {
        "source_ref": ambiguity.ambiguity_id,
        "ambiguity_ref": ambiguity.ambiguity_id,
        "human_escalation_ref": human_escalation_ref,
        "resolution_route": ambiguity.resolution_route,
        "checkpoint_class": checkpoint_class,
    }


def _deterministic_replay_identity_hash(
    *,
    architecture_id: str,
    semantic_hash: str,
    conformance_report_ref: str,
    checkpoint_id: str,
    ambiguity_ref: str,
    human_escalation_ref: str | None,
    checkpoint_class: ArchitectureCheckpointClass,
    resolution_route: ArchitectureResolutionRoute,
    compiler_version: str,
    hybrid_policy_hashes: list[ArchitecturePolicySourceHash],
) -> str:
    payload = {
        "architecture_id": architecture_id,
        "semantic_hash": semantic_hash,
        "conformance_report_ref": conformance_report_ref,
        "checkpoint_id": checkpoint_id,
        "ambiguity_ref": ambiguity_ref,
        "human_escalation_ref": human_escalation_ref,
        "checkpoint_class": checkpoint_class,
        "resolution_route": resolution_route,
        "compiler_version": compiler_version,
        "hybrid_policy_hashes": [_dump_json_payload(item) for item in hybrid_policy_hashes],
    }
    return _replay_identity_hash(payload)


def canonicalize_adeu_architecture_oracle_request_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = AdeuArchitectureOracleRequest.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return _dump_json_payload(model)


def canonicalize_adeu_architecture_oracle_resolution_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = AdeuArchitectureOracleResolution.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return _dump_json_payload(model)


def canonicalize_adeu_architecture_ir_delta_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = AdeuArchitectureIRDelta.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return _dump_json_payload(model)


def canonicalize_adeu_architecture_checkpoint_trace_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = AdeuArchitectureCheckpointTrace.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return _dump_json_payload(model)


def derive_v40c_oracle_request(
    *,
    semantic_ir_payload: dict[str, Any],
    conformance_report_payload: dict[str, Any],
    conformance_report_path: str,
    ambiguity_ref: str,
    model_id: str,
    model_version: str,
    reasoning_effort: ArchitectureReasoningEffort,
    prompt_template_version: str,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    semantic_ir, conformance_report = _validate_semantic_and_conformance(
        semantic_ir_payload=semantic_ir_payload,
        conformance_report_payload=conformance_report_payload,
        repository_root=repository_root,
    )
    normalized_report_path = _normalize_repo_relative_path(
        conformance_report_path,
        field_name="conformance_report_path",
    )
    if repository_root is not None:
        repo_payload = _load_repo_json(normalized_report_path, repository_root=repository_root)
        if canonicalize_adeu_architecture_conformance_report_payload(
            repo_payload,
            repository_root=repository_root,
        ) != _dump_json_payload(conformance_report):
            raise ValueError(
                "conformance_report_path must point to the canonical consumed conformance report"
            )
    classification = _classify_checkpoint(
        semantic_ir=semantic_ir,
        conformance_report=conformance_report,
        checkpoint_source_kind="ambiguity",
        checkpoint_subject_ref=ambiguity_ref,
    )
    if classification["checkpoint_class"] != "oracle_needed":
        raise ValueError("derive_v40c_oracle_request requires an oracle-assisted ambiguity")
    checkpoint_id = _checkpoint_id(
        architecture_id=semantic_ir.architecture_id,
        semantic_hash=semantic_ir.semantic_hash,
        source_kind="ambiguity",
        source_ref=classification["source_ref"],
        checkpoint_class=classification["checkpoint_class"],
        resolution_route=classification["resolution_route"],
    )
    intent_ref = _conformance_root_ref(
        conformance_report,
        artifact_schema=ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
    )
    policy_hashes = _policy_source_hash_entries(repository_root=repository_root)
    ambiguity = next(
        item for item in semantic_ir.epistemics.ambiguities if item.ambiguity_id == ambiguity_ref
    )
    replay_identity = {
        "intent_packet_hash": intent_ref.sha256,
        "semantic_hash": semantic_ir.semantic_hash,
        "conformance_report_ref": normalized_report_path,
        "policy_source_hashes": policy_hashes,
        "model_id": model_id,
        "model_version": model_version,
        "reasoning_effort": reasoning_effort,
        "prompt_template_version": prompt_template_version,
        "compiler_version": "1",
        "context_refs": sorted(ambiguity.touches_refs),
    }
    request = {
        "schema": ADEU_ARCHITECTURE_ORACLE_REQUEST_SCHEMA,
        "request_id": _oracle_request_id(
            checkpoint_id=checkpoint_id,
            replay_identity=replay_identity,
        ),
        "architecture_id": semantic_ir.architecture_id,
        "semantic_hash": semantic_ir.semantic_hash,
        "conformance_report_ref": normalized_report_path,
        "checkpoint_id": checkpoint_id,
        "ambiguity_ref": ambiguity_ref,
        "checkpoint_class": "oracle_needed",
        "replay_identity": replay_identity,
        "policy_source_hashes": policy_hashes,
        "model_id": model_id,
        "model_version": model_version,
        "reasoning_effort": reasoning_effort,
        "prompt_template_version": prompt_template_version,
        "compiler_version": "1",
        "context_refs": sorted(ambiguity.touches_refs),
    }
    return canonicalize_adeu_architecture_oracle_request_payload(
        request,
        repository_root=repository_root,
    )


def derive_v40c_oracle_resolution(
    *,
    oracle_request_payload: dict[str, Any],
    oracle_request_path: str | None = None,
    resolution_state: ArchitectureResolutionState,
    raw_output_text: str,
    proposed_delta_ref: str | None = None,
    resolution_origin: ArchitectureOracleResolutionOrigin = "fresh_model_output",
    repository_root: Path | None = None,
) -> dict[str, Any]:
    request = AdeuArchitectureOracleRequest.model_validate(
        oracle_request_payload,
        context=_validation_context(repository_root),
    )
    raw_output_hash = sha256_text(
        _assert_non_empty_text(raw_output_text, field_name="raw_output_text")
    )
    payload = {
        "schema": ADEU_ARCHITECTURE_ORACLE_RESOLUTION_SCHEMA,
        "resolution_id": _oracle_resolution_id(
            request_id=request.request_id,
            resolution_state=resolution_state,
            resolution_origin=resolution_origin,
            raw_output_hash=raw_output_hash,
            model_id=request.model_id,
            model_version=request.model_version,
            reasoning_effort=request.reasoning_effort,
        ),
        "request_id": request.request_id,
        "request_ref": (
            _normalize_repo_relative_path(
                oracle_request_path,
                field_name="oracle_request_path",
            )
            if oracle_request_path is not None
            else None
        ),
        "checkpoint_id": request.checkpoint_id,
        "architecture_id": request.architecture_id,
        "semantic_hash": request.semantic_hash,
        "model_id": request.model_id,
        "model_version": request.model_version,
        "reasoning_effort": request.reasoning_effort,
        "raw_output_hash": raw_output_hash,
        "resolution_state": resolution_state,
        "proposed_delta_ref": proposed_delta_ref,
        "resolution_origin": resolution_origin,
    }
    return canonicalize_adeu_architecture_oracle_resolution_payload(
        payload,
        repository_root=repository_root,
    )


def derive_v40c_ir_delta(
    *,
    semantic_ir_payload: dict[str, Any],
    oracle_resolution_payload: dict[str, Any],
    checkpoint_id: str,
    scope_ref: str,
    target_refs: list[str],
    authorized_placeholder_refs: list[str] | None = None,
    operation_set: list[dict[str, Any]],
    repository_root: Path | None = None,
) -> dict[str, Any]:
    semantic_ir = AdeuArchitectureSemanticIR.model_validate(
        semantic_ir_payload,
        context=_validation_context(repository_root),
    )
    resolution = AdeuArchitectureOracleResolution.model_validate(
        oracle_resolution_payload,
        context=_validation_context(repository_root),
    )
    if resolution.architecture_id != semantic_ir.architecture_id:
        raise ValueError("resolution and semantic_ir must share architecture_id")
    if resolution.semantic_hash != semantic_ir.semantic_hash:
        raise ValueError("resolution and semantic_ir must share semantic_hash")
    if checkpoint_id != resolution.checkpoint_id:
        raise ValueError("checkpoint_id must match resolution.checkpoint_id")
    if resolution.resolution_state not in {"advisory_support", "advisory_reject"}:
        raise ValueError(
            "IR delta may be derived only from advisory_support or advisory_reject resolutions"
        )
    allowed_refs = _semantic_root_ref_set(semantic_ir)
    normalized_target_refs = _assert_sorted_unique(target_refs, field_name="target_refs")
    for target_ref in normalized_target_refs:
        if target_ref not in allowed_refs:
            raise ValueError("target_refs must resolve within the semantic root")
    normalized_placeholders = _assert_sorted_unique(
        authorized_placeholder_refs or [],
        field_name="authorized_placeholder_refs",
    )
    operations = [ArchitectureIRDeltaOperation.model_validate(item) for item in operation_set]
    payload = {
        "schema": ADEU_ARCHITECTURE_IR_DELTA_SCHEMA,
        "delta_id": _delta_id(
            source_resolution_id=resolution.resolution_id,
            scope_ref=scope_ref,
            target_refs=normalized_target_refs,
            authorized_placeholder_refs=normalized_placeholders,
            operation_set=[_dump_json_payload(item) for item in operations],
        ),
        "architecture_id": semantic_ir.architecture_id,
        "semantic_hash": semantic_ir.semantic_hash,
        "checkpoint_id": checkpoint_id,
        "source_resolution_id": resolution.resolution_id,
        "scope_ref": scope_ref,
        "target_refs": normalized_target_refs,
        "authorized_placeholder_refs": normalized_placeholders,
        "operation_set": [_dump_json_payload(item) for item in operations],
    }
    return canonicalize_adeu_architecture_ir_delta_payload(
        payload,
        repository_root=repository_root,
    )


def derive_v40c_checkpoint_trace(
    *,
    semantic_ir_payload: dict[str, Any],
    conformance_report_payload: dict[str, Any],
    conformance_report_path: str,
    checkpoint_source_kind: ArchitectureCheckpointSourceKind,
    checkpoint_subject_ref: str,
    oracle_request_payload: dict[str, Any] | None = None,
    oracle_request_path: str | None = None,
    oracle_resolution_payload: dict[str, Any] | None = None,
    oracle_resolution_path: str | None = None,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    semantic_ir, conformance_report = _validate_semantic_and_conformance(
        semantic_ir_payload=semantic_ir_payload,
        conformance_report_payload=conformance_report_payload,
        repository_root=repository_root,
    )
    normalized_report_path = _normalize_repo_relative_path(
        conformance_report_path,
        field_name="conformance_report_path",
    )
    if repository_root is not None:
        repo_payload = _load_repo_json(normalized_report_path, repository_root=repository_root)
        if canonicalize_adeu_architecture_conformance_report_payload(
            repo_payload,
            repository_root=repository_root,
        ) != _dump_json_payload(conformance_report):
            raise ValueError(
                "conformance_report_path must point to the canonical consumed conformance report"
            )
    classification = _classify_checkpoint(
        semantic_ir=semantic_ir,
        conformance_report=conformance_report,
        checkpoint_source_kind=checkpoint_source_kind,
        checkpoint_subject_ref=checkpoint_subject_ref,
    )
    checkpoint_id = _checkpoint_id(
        architecture_id=semantic_ir.architecture_id,
        semantic_hash=semantic_ir.semantic_hash,
        source_kind=checkpoint_source_kind,
        source_ref=classification["source_ref"],
        checkpoint_class=classification["checkpoint_class"],
        resolution_route=classification["resolution_route"],
    )
    policy_hashes = [
        ArchitecturePolicySourceHash.model_validate(
            item,
            context=_validation_context(repository_root),
        )
        for item in _policy_source_hash_entries(repository_root=repository_root)
    ]
    request_ref: str | None = None
    resolution_ref: str | None = None
    final_adjudication = _expected_final_adjudication_for_checkpoint_class(
        classification["checkpoint_class"]
    )
    replay_identity_hash = _deterministic_replay_identity_hash(
        architecture_id=semantic_ir.architecture_id,
        semantic_hash=semantic_ir.semantic_hash,
        conformance_report_ref=normalized_report_path,
        checkpoint_id=checkpoint_id,
        ambiguity_ref=classification["ambiguity_ref"],
        human_escalation_ref=classification["human_escalation_ref"],
        checkpoint_class=classification["checkpoint_class"],
        resolution_route=classification["resolution_route"],
        compiler_version="1",
        hybrid_policy_hashes=policy_hashes,
    )
    if classification["checkpoint_class"] == "oracle_needed":
        if oracle_request_payload is None or oracle_request_path is None:
            raise ValueError(
                "oracle_needed checkpoint traces require oracle_request_payload "
                "and oracle_request_path"
            )
        request_ref = _normalize_repo_relative_path(
            oracle_request_path,
            field_name="oracle_request_path",
        )
        request = AdeuArchitectureOracleRequest.model_validate(
            oracle_request_payload,
            context=_validation_context(repository_root),
        )
        if request.architecture_id != semantic_ir.architecture_id:
            raise ValueError("oracle request must match semantic_ir architecture_id")
        if request.semantic_hash != semantic_ir.semantic_hash:
            raise ValueError("oracle request must match semantic_ir semantic_hash")
        if request.conformance_report_ref != normalized_report_path:
            raise ValueError("oracle request must bind to the consumed conformance report")
        if request.checkpoint_id != checkpoint_id:
            raise ValueError("oracle request checkpoint_id must match classified checkpoint")
        if request.ambiguity_ref != classification["ambiguity_ref"]:
            raise ValueError("oracle request ambiguity_ref must match classified ambiguity")
        replay_identity_hash = _replay_identity_hash(_dump_json_payload(request.replay_identity))
        if oracle_resolution_payload is not None:
            if oracle_resolution_path is None:
                raise ValueError(
                    "oracle_resolution_path is required when resolution payload is provided"
                )
            resolution_ref = _normalize_repo_relative_path(
                oracle_resolution_path,
                field_name="oracle_resolution_path",
            )
            resolution = AdeuArchitectureOracleResolution.model_validate(
                oracle_resolution_payload,
                context=_validation_context(repository_root),
            )
            if resolution.request_id != request.request_id:
                final_adjudication = "escalated_human"
            elif resolution.checkpoint_id != checkpoint_id:
                final_adjudication = "escalated_human"
            elif resolution.architecture_id != semantic_ir.architecture_id:
                final_adjudication = "escalated_human"
            elif resolution.semantic_hash != semantic_ir.semantic_hash:
                final_adjudication = "escalated_human"
            elif resolution.model_id != request.model_id:
                final_adjudication = "escalated_human"
            elif resolution.model_version != request.model_version:
                final_adjudication = "escalated_human"
            elif resolution.reasoning_effort != request.reasoning_effort:
                final_adjudication = "escalated_human"
            else:
                final_adjudication = _expected_final_adjudication_for_resolution_state(
                    resolution.resolution_state
                )
        else:
            final_adjudication = "escalated_human"
    assert final_adjudication is not None
    entry = {
        "checkpoint_id": checkpoint_id,
        "ambiguity_ref": classification["ambiguity_ref"],
        "human_escalation_ref": classification["human_escalation_ref"],
        "checkpoint_class": classification["checkpoint_class"],
        "resolution_route": classification["resolution_route"],
        "oracle_request_ref": request_ref,
        "oracle_resolution_ref": resolution_ref,
        "final_adjudication": final_adjudication,
        "replay_identity_hash": replay_identity_hash,
    }
    trace = {
        "schema": ADEU_ARCHITECTURE_CHECKPOINT_TRACE_SCHEMA,
        "trace_id": _trace_id(
            architecture_id=semantic_ir.architecture_id,
            semantic_hash=semantic_ir.semantic_hash,
            conformance_report_ref=normalized_report_path,
            checkpoint_entries=[entry],
        ),
        "architecture_id": semantic_ir.architecture_id,
        "semantic_hash": semantic_ir.semantic_hash,
        "conformance_report_ref": normalized_report_path,
        "compiler_version": "1",
        "hybrid_policy_hashes": [_dump_json_payload(item) for item in policy_hashes],
        "adjudicator": _dump_json_payload(ArchitectureHybridAdjudicator()),
        "checkpoint_entries": [entry],
    }
    return canonicalize_adeu_architecture_checkpoint_trace_payload(
        trace,
        repository_root=repository_root,
    )


__all__ = [
    "ADEU_ARCHITECTURE_CHECKPOINT_TRACE_SCHEMA",
    "ADEU_ARCHITECTURE_IR_DELTA_SCHEMA",
    "ADEU_ARCHITECTURE_ORACLE_REQUEST_SCHEMA",
    "ADEU_ARCHITECTURE_ORACLE_RESOLUTION_SCHEMA",
    "V40C_V79_CONTRACT_SOURCE",
    "AdeuArchitectureCheckpointTrace",
    "AdeuArchitectureIRDelta",
    "AdeuArchitectureOracleRequest",
    "AdeuArchitectureOracleResolution",
    "ArchitectureCheckpointClass",
    "ArchitectureCheckpointTraceEntry",
    "ArchitectureFinalAdjudication",
    "ArchitectureHybridAdjudicator",
    "ArchitectureIRDeltaOperation",
    "ArchitectureOracleReplayIdentity",
    "ArchitecturePolicySourceHash",
    "ArchitectureReasoningEffort",
    "ArchitectureResolutionState",
    "canonicalize_adeu_architecture_checkpoint_trace_payload",
    "canonicalize_adeu_architecture_ir_delta_payload",
    "canonicalize_adeu_architecture_oracle_request_payload",
    "canonicalize_adeu_architecture_oracle_resolution_payload",
    "derive_v40c_checkpoint_trace",
    "derive_v40c_ir_delta",
    "derive_v40c_oracle_request",
    "derive_v40c_oracle_resolution",
]
