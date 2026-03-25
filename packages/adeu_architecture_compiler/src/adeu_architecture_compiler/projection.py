from __future__ import annotations

from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_architecture_ir import AdeuArchitectureSemanticIR
from adeu_core_ir import (
    AdeuCoreIR,
    CoreDNode,
    CoreEdge,
    CoreENode,
    CoreONode,
    CoreUNode,
    canonicalize_core_ir_payload,
)
from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .conformance import (
    AdeuArchitectureConformanceReport,
    ArchitectureConsumedRootRef,
    ArchitectureProjectionReadiness,
    _assert_non_empty_text,
    _assert_sorted_unique,
    _dump_json_payload,
    _load_repo_json,
    _normalize_repo_relative_path,
    _validation_context,
)
from .hybrid import (
    AdeuArchitectureCheckpointTrace,
)

ADEU_ARCHITECTURE_PROJECTION_BUNDLE_SCHEMA = "adeu_architecture_projection_bundle@1"
ADEU_ARCHITECTURE_PROJECTION_MANIFEST_SCHEMA = "adeu_architecture_projection_manifest@1"
ADEU_CORE_IR_TARGET_FAMILY = "adeu_core_ir@0.1"
V40D_V80_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS80.md#v80-continuation-contract-machine-checkable"
)
V40D_COMPILER_ENTRYPOINT = "adeu_architecture_compiler.v40d.lower_to_adeu_core_ir"

_ALLOWED_EDGE_TYPES = {"depends_on", "gates", "justifies", "prioritizes", "serves_goal"}
_BLOCKING_FINAL_ADJUDICATIONS = {"resolved_fail", "escalated_human"}


def _projection_config_hash() -> str:
    return sha256_canonical_json(
        {
            "contract_source": V40D_V80_CONTRACT_SOURCE,
            "entrypoint": V40D_COMPILER_ENTRYPOINT,
            "lowering_profile": "v40d_core_ir_projection.v1",
            "slice": "vNext+80",
            "target_family": ADEU_CORE_IR_TARGET_FAMILY,
            "target_path": "V40-D",
            "ready_vocabulary": ["ready", "blocked"],
            "starter_edge_types": sorted(_ALLOWED_EDGE_TYPES),
        }
    )


def _projection_id(
    *,
    architecture_id: str,
    target_family: str,
    source_refs: list[str],
) -> str:
    digest = sha256_canonical_json(
        {
            "architecture_id": architecture_id,
            "target_family": target_family,
            "source_refs": source_refs,
        }
    )[:16]
    return f"v40d_v80_projection_{digest}"


def _bundle_id(
    *,
    architecture_id: str,
    semantic_hash: str,
    conformance_report_ref: str,
    checkpoint_trace_ref: str,
    target_family: str,
    compiler: dict[str, Any],
    compiler_version: str,
    projection_units: list[dict[str, Any]],
) -> str:
    digest = sha256_canonical_json(
        {
            "architecture_id": architecture_id,
            "semantic_hash": semantic_hash,
            "conformance_report_ref": conformance_report_ref,
            "checkpoint_trace_ref": checkpoint_trace_ref,
            "target_family": target_family,
            "compiler": compiler,
            "compiler_version": compiler_version,
            "projection_units": projection_units,
        }
    )[:16]
    return f"v40d_v80_bundle_{digest}"


def _manifest_id(
    *,
    architecture_id: str,
    semantic_hash: str,
    conformance_report_ref: str,
    checkpoint_trace_ref: str,
    source_root_refs: list[dict[str, Any]],
    target_family: str,
    compiler_entrypoint: str,
    compiler_version: str,
    projection_units: list[dict[str, Any]],
    touched_artifact_refs: list[str],
    blocked_by_ambiguity_refs: list[str],
) -> str:
    digest = sha256_canonical_json(
        {
            "architecture_id": architecture_id,
            "semantic_hash": semantic_hash,
            "conformance_report_ref": conformance_report_ref,
            "checkpoint_trace_ref": checkpoint_trace_ref,
            "source_root_refs": source_root_refs,
            "target_family": target_family,
            "compiler_entrypoint": compiler_entrypoint,
            "compiler_version": compiler_version,
            "projection_units": projection_units,
            "touched_artifact_refs": touched_artifact_refs,
            "blocked_by_ambiguity_refs": blocked_by_ambiguity_refs,
        }
    )[:16]
    return f"v40d_v80_manifest_{digest}"


def _active_blocking_ambiguity_refs(
    checkpoint_trace: AdeuArchitectureCheckpointTrace,
) -> list[str]:
    return sorted(
        {
            entry.ambiguity_ref
            for entry in checkpoint_trace.checkpoint_entries
            if entry.final_adjudication in _BLOCKING_FINAL_ADJUDICATIONS
        }
    )


def _validate_projection_output_artifact_lineage(
    *,
    unit: "ArchitectureProjectionUnit",
    architecture_id: str,
    semantic_hash: str,
    conformance_report_ref: str,
    checkpoint_trace_ref: str,
    compiler_version: str,
    repository_root: Path,
) -> None:
    for artifact_ref in unit.output_artifact_refs:
        payload = _load_repo_json(artifact_ref, repository_root=repository_root)
        core_ir = AdeuCoreIR.model_validate(payload)
        if core_ir.schema != ADEU_CORE_IR_TARGET_FAMILY:
            raise ValueError("output_artifact_refs must target adeu_core_ir@0.1 only")
        if core_ir.source_text_hash != semantic_hash:
            raise ValueError(
                "output_artifact_refs must preserve semantic_hash as core_ir.source_text_hash"
            )
        metadata = core_ir.metadata
        if not isinstance(metadata, dict):
            raise ValueError("output_artifact_refs must carry V40-D lineage metadata")
        expected_metadata = {
            "architecture_id": architecture_id,
            "semantic_hash": semantic_hash,
            "conformance_report_ref": conformance_report_ref,
            "checkpoint_trace_ref": checkpoint_trace_ref,
            "projection_id": unit.projection_id,
            "compiler_entrypoint": unit.compiler_entrypoint,
            "compiler_version": compiler_version,
            "source_refs": unit.source_refs,
        }
        for key, expected_value in expected_metadata.items():
            if metadata.get(key) != expected_value:
                raise ValueError(
                    f"output_artifact_refs must preserve {key} in emitted core_ir metadata"
                )


def _validate_projection_units_against_consumed_lineage(
    *,
    projection_units: list["ArchitectureProjectionUnit"],
    conformance: AdeuArchitectureConformanceReport,
    checkpoint_trace: AdeuArchitectureCheckpointTrace,
    architecture_id: str,
    semantic_hash: str,
    conformance_report_ref: str,
    checkpoint_trace_ref: str,
    compiler_version: str,
    repository_root: Path,
) -> None:
    if conformance.architecture_id != architecture_id:
        raise ValueError("architecture_id must match the referenced conformance report")
    if conformance.semantic_hash != semantic_hash:
        raise ValueError("semantic_hash must match the referenced conformance report")
    if checkpoint_trace.architecture_id != architecture_id:
        raise ValueError("architecture_id must match the referenced checkpoint trace")
    if checkpoint_trace.semantic_hash != semantic_hash:
        raise ValueError("semantic_hash must match the referenced checkpoint trace")
    if checkpoint_trace.conformance_report_ref != conformance_report_ref:
        raise ValueError("checkpoint_trace_ref must bind back to conformance_report_ref")

    active_blockers = _active_blocking_ambiguity_refs(checkpoint_trace)
    if conformance.projection_readiness != "ready" and not active_blockers:
        raise ValueError(
            "V40-D may not lower blocked conformance without active "
            "checkpoint blocker lineage"
        )
    for unit in projection_units:
        expected_unit_blockers = sorted(
            blocker for blocker in active_blockers if blocker in unit.source_refs
        )
        if unit.blocked_by_ambiguity_refs != expected_unit_blockers:
            raise ValueError(
                "projection_unit blocked_by_ambiguity_refs must match "
                "active unit-local blockers from checkpoint-trace lineage"
            )
        if unit.readiness == "ready" and conformance.projection_readiness != "ready":
            raise ValueError(
                "projection_unit readiness may not be ready while source "
                "conformance remains blocked"
            )
        if unit.readiness == "ready" and expected_unit_blockers:
            raise ValueError(
                "projection_unit readiness may not be ready while active blockers remain"
            )
        _validate_projection_output_artifact_lineage(
            unit=unit,
            architecture_id=architecture_id,
            semantic_hash=semantic_hash,
            conformance_report_ref=conformance_report_ref,
            checkpoint_trace_ref=checkpoint_trace_ref,
            compiler_version=compiler_version,
            repository_root=repository_root,
        )


def _validate_v40d_inputs(
    *,
    semantic_ir_payload: dict[str, Any],
    conformance_report_payload: dict[str, Any],
    conformance_report_path: str,
    checkpoint_trace_payload: dict[str, Any],
    checkpoint_trace_path: str,
    repository_root: Path | None = None,
) -> tuple[
    AdeuArchitectureSemanticIR,
    AdeuArchitectureConformanceReport,
    AdeuArchitectureCheckpointTrace,
    str,
    str,
]:
    context = _validation_context(repository_root)
    semantic_ir = AdeuArchitectureSemanticIR.model_validate(semantic_ir_payload, context=context)
    conformance_report = AdeuArchitectureConformanceReport.model_validate(
        conformance_report_payload,
        context=context,
    )
    checkpoint_trace = AdeuArchitectureCheckpointTrace.model_validate(
        checkpoint_trace_payload,
        context=context,
    )
    normalized_report_path = _normalize_repo_relative_path(
        conformance_report_path,
        field_name="conformance_report_path",
    )
    normalized_trace_path = _normalize_repo_relative_path(
        checkpoint_trace_path,
        field_name="checkpoint_trace_path",
    )
    if semantic_ir.architecture_id != conformance_report.architecture_id:
        raise ValueError("semantic_ir and conformance_report must share architecture_id")
    if semantic_ir.semantic_hash != conformance_report.semantic_hash:
        raise ValueError("semantic_ir and conformance_report must share semantic_hash")
    if semantic_ir.architecture_id != checkpoint_trace.architecture_id:
        raise ValueError("semantic_ir and checkpoint_trace must share architecture_id")
    if semantic_ir.semantic_hash != checkpoint_trace.semantic_hash:
        raise ValueError("semantic_ir and checkpoint_trace must share semantic_hash")
    if checkpoint_trace.conformance_report_ref != normalized_report_path:
        raise ValueError("checkpoint_trace must bind to the consumed conformance_report_path")
    if repository_root is not None:
        report_payload = _load_repo_json(normalized_report_path, repository_root=repository_root)
        if report_payload != _dump_json_payload(conformance_report):
            raise ValueError("conformance_report_path must point to the canonical consumed report")
        trace_payload = _load_repo_json(normalized_trace_path, repository_root=repository_root)
        if trace_payload != _dump_json_payload(checkpoint_trace):
            raise ValueError("checkpoint_trace_path must point to the canonical consumed trace")
    return (
        semantic_ir,
        conformance_report,
        checkpoint_trace,
        normalized_report_path,
        normalized_trace_path,
    )


def _semantic_projection_source_refs(semantic_ir: AdeuArchitectureSemanticIR) -> list[str]:
    refs: list[str] = []
    refs.extend(item.actor_id for item in semantic_ir.ontology.actors)
    refs.extend(item.surface_id for item in semantic_ir.ontology.surfaces)
    refs.extend(item.object_id for item in semantic_ir.ontology.data_objects)
    refs.extend(item.boundary_id for item in semantic_ir.ontology.boundaries)
    refs.extend(item.capability_id for item in semantic_ir.ontology.capabilities)
    refs.extend(item.workflow_id for item in semantic_ir.ontology.workflows)
    refs.extend(item.step_id for item in semantic_ir.ontology.flow_steps)
    refs.extend(item.state_id for item in semantic_ir.ontology.states)
    refs.extend(item.transition_id for item in semantic_ir.ontology.transitions)
    refs.extend(item.decision_id for item in semantic_ir.ontology.decisions)
    refs.extend(item.failure_mode_id for item in semantic_ir.ontology.failure_modes)
    refs.extend(item.fact_id for item in semantic_ir.epistemics.facts)
    refs.extend(item.assumption_id for item in semantic_ir.epistemics.assumptions)
    refs.extend(item.ambiguity_id for item in semantic_ir.epistemics.ambiguities)
    refs.extend(item.evidence_id for item in semantic_ir.epistemics.evidence_requirements)
    refs.extend(item.obligation_id for item in semantic_ir.deontics.obligations)
    refs.extend(item.prohibition_id for item in semantic_ir.deontics.prohibitions)
    refs.extend(item.permission_id for item in semantic_ir.deontics.permissions)
    refs.extend(item.gate_id for item in semantic_ir.deontics.gates)
    refs.extend(item.invariant_id for item in semantic_ir.deontics.invariants)
    refs.extend(item.rule_id for item in semantic_ir.deontics.escalation_rules)
    refs.extend(item.goal_id for item in semantic_ir.utility.goals)
    refs.extend(item.metric_id for item in semantic_ir.utility.metrics)
    refs.extend(item.priority_id for item in semantic_ir.utility.priority_rules)
    refs.extend(item.tradeoff_id for item in semantic_ir.utility.tradeoffs)
    return _assert_sorted_unique(refs, field_name="projection_source_refs", allow_empty=False)


def _build_ready_core_ir_payload(
    *,
    semantic_ir: AdeuArchitectureSemanticIR,
    conformance_report_ref: str,
    checkpoint_trace_ref: str,
    projection_id: str,
    compiler_version: str,
    source_refs: list[str],
) -> dict[str, Any]:
    nodes: list[CoreONode | CoreENode | CoreDNode | CoreUNode] = []
    edges: list[CoreEdge] = []

    o_kind_by_ref: dict[str, Literal["Entity", "Concept", "RelationType"]] = {}
    e_kind_by_ref: dict[str, Literal["Claim", "Assumption", "Question", "Evidence"]] = {}
    d_kind_by_ref: dict[str, Literal["PhysicalConstraint", "Norm", "Policy", "Exception"]] = {}
    u_kind_by_ref: dict[str, Literal["Goal", "Metric", "Preference"]] = {}

    for actor in semantic_ir.ontology.actors:
        nodes.append(CoreONode(id=actor.actor_id, kind="Entity", label=actor.label))
        o_kind_by_ref[actor.actor_id] = "Entity"
    for surface in semantic_ir.ontology.surfaces:
        nodes.append(CoreONode(id=surface.surface_id, kind="Entity", label=surface.surface_id))
        o_kind_by_ref[surface.surface_id] = "Entity"
    for data_object in semantic_ir.ontology.data_objects:
        nodes.append(CoreONode(id=data_object.object_id, kind="Entity", label=data_object.label))
        o_kind_by_ref[data_object.object_id] = "Entity"
    for boundary in semantic_ir.ontology.boundaries:
        nodes.append(
            CoreONode(id=boundary.boundary_id, kind="RelationType", label=boundary.boundary_class)
        )
        o_kind_by_ref[boundary.boundary_id] = "RelationType"
    for capability in semantic_ir.ontology.capabilities:
        nodes.append(
            CoreONode(id=capability.capability_id, kind="RelationType", label=capability.action)
        )
        o_kind_by_ref[capability.capability_id] = "RelationType"
    for workflow in semantic_ir.ontology.workflows:
        nodes.append(
            CoreONode(id=workflow.workflow_id, kind="RelationType", label=workflow.workflow_id)
        )
        o_kind_by_ref[workflow.workflow_id] = "RelationType"
    for step in semantic_ir.ontology.flow_steps:
        nodes.append(CoreONode(id=step.step_id, kind="RelationType", label=step.kind))
        o_kind_by_ref[step.step_id] = "RelationType"
    for state in semantic_ir.ontology.states:
        nodes.append(CoreONode(id=state.state_id, kind="Concept", label=state.state_kind))
        o_kind_by_ref[state.state_id] = "Concept"
    for transition in semantic_ir.ontology.transitions:
        nodes.append(
            CoreONode(
                id=transition.transition_id, kind="RelationType", label=transition.transition_id
            )
        )
        o_kind_by_ref[transition.transition_id] = "RelationType"
    for decision in semantic_ir.ontology.decisions:
        nodes.append(
            CoreONode(id=decision.decision_id, kind="RelationType", label=decision.decision_id)
        )
        o_kind_by_ref[decision.decision_id] = "RelationType"
    for failure_mode in semantic_ir.ontology.failure_modes:
        nodes.append(
            CoreONode(
                id=failure_mode.failure_mode_id,
                kind="RelationType",
                label=failure_mode.default_disposition,
            )
        )
        o_kind_by_ref[failure_mode.failure_mode_id] = "RelationType"

    for fact in semantic_ir.epistemics.facts:
        nodes.append(CoreENode(id=fact.fact_id, kind="Claim", text=fact.statement))
        e_kind_by_ref[fact.fact_id] = "Claim"
    for assumption in semantic_ir.epistemics.assumptions:
        nodes.append(
            CoreENode(id=assumption.assumption_id, kind="Assumption", text=assumption.statement)
        )
        e_kind_by_ref[assumption.assumption_id] = "Assumption"
    for ambiguity in semantic_ir.epistemics.ambiguities:
        nodes.append(CoreENode(id=ambiguity.ambiguity_id, kind="Question", text=ambiguity.question))
        e_kind_by_ref[ambiguity.ambiguity_id] = "Question"
    for evidence in semantic_ir.epistemics.evidence_requirements:
        nodes.append(
            CoreENode(id=evidence.evidence_id, kind="Evidence", text=evidence.source_policy)
        )
        e_kind_by_ref[evidence.evidence_id] = "Evidence"

    for obligation in semantic_ir.deontics.obligations:
        nodes.append(
            CoreDNode(
                id=obligation.obligation_id,
                kind="Norm",
                label=obligation.statement,
                modality="obligatory",
                condition=obligation.condition,
                target=",".join(obligation.target_refs),
            )
        )
        d_kind_by_ref[obligation.obligation_id] = "Norm"
    for prohibition in semantic_ir.deontics.prohibitions:
        nodes.append(
            CoreDNode(
                id=prohibition.prohibition_id,
                kind="Norm",
                label=prohibition.statement,
                modality="forbidden",
                condition=prohibition.condition,
                target=",".join(prohibition.target_refs),
            )
        )
        d_kind_by_ref[prohibition.prohibition_id] = "Norm"
    for permission in semantic_ir.deontics.permissions:
        nodes.append(
            CoreDNode(
                id=permission.permission_id,
                kind="Norm",
                label=permission.statement,
                modality="permitted",
                condition=permission.condition,
                target=",".join(permission.target_refs),
            )
        )
        d_kind_by_ref[permission.permission_id] = "Norm"
    for gate in semantic_ir.deontics.gates:
        nodes.append(
            CoreDNode(
                id=gate.gate_id,
                kind="Policy",
                label=gate.gate_id,
                condition="fail_closed" if gate.fail_closed else "non_fail_closed",
                target=gate.subject_ref,
            )
        )
        d_kind_by_ref[gate.gate_id] = "Policy"
    for invariant in semantic_ir.deontics.invariants:
        nodes.append(
            CoreDNode(
                id=invariant.invariant_id,
                kind="PhysicalConstraint",
                label=invariant.statement,
                constraint_kind="invariant",
            )
        )
        d_kind_by_ref[invariant.invariant_id] = "PhysicalConstraint"
    for rule in semantic_ir.deontics.escalation_rules:
        nodes.append(
            CoreDNode(
                id=rule.rule_id,
                kind="Exception",
                label=rule.rule_id,
                condition=rule.default_disposition,
                target=rule.escalate_to,
            )
        )
        d_kind_by_ref[rule.rule_id] = "Exception"

    for goal in semantic_ir.utility.goals:
        nodes.append(CoreUNode(id=goal.goal_id, kind="Goal", label=goal.statement))
        u_kind_by_ref[goal.goal_id] = "Goal"
    for metric in semantic_ir.utility.metrics:
        nodes.append(CoreUNode(id=metric.metric_id, kind="Metric", label=metric.label))
        u_kind_by_ref[metric.metric_id] = "Metric"
    for priority in semantic_ir.utility.priority_rules:
        nodes.append(
            CoreUNode(id=priority.priority_id, kind="Preference", label=priority.condition)
        )
        u_kind_by_ref[priority.priority_id] = "Preference"
    for tradeoff in semantic_ir.utility.tradeoffs:
        nodes.append(
            CoreUNode(id=tradeoff.tradeoff_id, kind="Preference", label=tradeoff.adjudication_rule)
        )
        u_kind_by_ref[tradeoff.tradeoff_id] = "Preference"

    for gate in semantic_ir.deontics.gates:
        for required_ref in gate.required_refs:
            if e_kind_by_ref.get(required_ref) in {"Claim", "Evidence"}:
                edges.append(
                    CoreEdge.model_validate(
                        {"type": "justifies", "from": required_ref, "to": gate.gate_id}
                    )
                )
    for ambiguity in semantic_ir.epistemics.ambiguities:
        for touched_ref in ambiguity.touches_refs:
            if d_kind_by_ref.get(touched_ref) == "Policy":
                edges.append(
                    CoreEdge.model_validate(
                        {"type": "gates", "from": touched_ref, "to": ambiguity.ambiguity_id}
                    )
                )
    for goal in semantic_ir.utility.goals:
        for served_by_ref in goal.served_by_refs:
            if d_kind_by_ref.get(served_by_ref) in {
                "PhysicalConstraint",
                "Norm",
                "Policy",
            } or e_kind_by_ref.get(served_by_ref) == "Claim":
                edges.append(
                    CoreEdge.model_validate(
                        {"type": "serves_goal", "from": served_by_ref, "to": goal.goal_id}
                    )
                )
    for priority in semantic_ir.utility.priority_rules:
        for target_ref in (priority.higher_ref, priority.lower_ref):
            if target_ref in u_kind_by_ref or target_ref in d_kind_by_ref:
                edges.append(
                    CoreEdge.model_validate(
                        {"type": "prioritizes", "from": priority.priority_id, "to": target_ref}
                    )
                )
    for tradeoff in semantic_ir.utility.tradeoffs:
        for target_ref in tradeoff.between_refs:
            if target_ref in u_kind_by_ref or target_ref in d_kind_by_ref:
                edges.append(
                    CoreEdge.model_validate(
                        {"type": "prioritizes", "from": tradeoff.tradeoff_id, "to": target_ref}
                    )
                )

    payload = {
        "schema": ADEU_CORE_IR_TARGET_FAMILY,
        "source_text_hash": semantic_ir.semantic_hash,
        "metadata": {
            "architecture_id": semantic_ir.architecture_id,
            "semantic_hash": semantic_ir.semantic_hash,
            "conformance_report_ref": conformance_report_ref,
            "checkpoint_trace_ref": checkpoint_trace_ref,
            "projection_id": projection_id,
            "compiler_entrypoint": V40D_COMPILER_ENTRYPOINT,
            "compiler_version": compiler_version,
            "source_refs": source_refs,
        },
        "nodes": [node.model_dump(mode="json", by_alias=True, exclude_none=True) for node in nodes],
        "edges": [edge.model_dump(mode="json", by_alias=True, exclude_none=True) for edge in edges],
    }
    return canonicalize_core_ir_payload(payload)


class ArchitectureProjectionCompilerProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    name: Literal["adeu_architecture_compiler.v40d"] = "adeu_architecture_compiler.v40d"
    version: str = "1"
    lowering_profile: Literal["v40d_core_ir_projection.v1"] = "v40d_core_ir_projection.v1"
    config_hash: str = Field(default_factory=_projection_config_hash)
    contract_source: str = V40D_V80_CONTRACT_SOURCE

    @model_validator(mode="after")
    def _validate_compiler(self) -> ArchitectureProjectionCompilerProvenance:
        object.__setattr__(
            self,
            "version",
            _assert_non_empty_text(self.version, field_name="compiler.version"),
        )
        object.__setattr__(
            self,
            "contract_source",
            _assert_non_empty_text(self.contract_source, field_name="compiler.contract_source"),
        )
        if self.config_hash != _projection_config_hash():
            raise ValueError(
                "compiler.config_hash must match the fixed v40d_core_ir_projection.v1 profile"
            )
        return self


class ArchitectureProjectionUnit(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    projection_id: str
    target_family: Literal[ADEU_CORE_IR_TARGET_FAMILY]
    source_refs: list[str]
    readiness: ArchitectureProjectionReadiness
    blocked_by_ambiguity_refs: list[str]
    output_artifact_refs: list[str]
    compiler_entrypoint: Literal[V40D_COMPILER_ENTRYPOINT] = V40D_COMPILER_ENTRYPOINT

    @model_validator(mode="after")
    def _validate_unit(self, info: ValidationInfo) -> ArchitectureProjectionUnit:
        object.__setattr__(
            self,
            "projection_id",
            _assert_non_empty_text(self.projection_id, field_name="projection_id"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _assert_sorted_unique(self.source_refs, field_name="source_refs", allow_empty=False),
        )
        object.__setattr__(
            self,
            "blocked_by_ambiguity_refs",
            _assert_sorted_unique(
                self.blocked_by_ambiguity_refs,
                field_name="blocked_by_ambiguity_refs",
            ),
        )
        normalized_outputs = [
            _normalize_repo_relative_path(value, field_name="output_artifact_refs")
            for value in self.output_artifact_refs
        ]
        object.__setattr__(
            self,
            "output_artifact_refs",
            _assert_sorted_unique(normalized_outputs, field_name="output_artifact_refs"),
        )
        if self.readiness == "ready":
            if self.blocked_by_ambiguity_refs:
                raise ValueError("ready projection units must not carry blocked_by_ambiguity_refs")
            if not self.output_artifact_refs:
                raise ValueError(
                    "ready projection units must emit at least one output artifact ref"
                )
        else:
            if self.output_artifact_refs:
                raise ValueError("blocked projection units must carry empty output_artifact_refs")
            if not self.blocked_by_ambiguity_refs:
                raise ValueError(
                    "blocked projection units require explicit blocked_by_ambiguity_refs lineage"
                )
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            for artifact_ref in self.output_artifact_refs:
                payload = _load_repo_json(artifact_ref, repository_root=repository_root)
                core_ir = AdeuCoreIR.model_validate(payload)
                if core_ir.schema != ADEU_CORE_IR_TARGET_FAMILY:
                    raise ValueError("output_artifact_refs must target adeu_core_ir@0.1 only")
        return self


class AdeuArchitectureProjectionBundle(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_PROJECTION_BUNDLE_SCHEMA]
    bundle_id: str
    architecture_id: str
    semantic_hash: str
    conformance_report_ref: str
    checkpoint_trace_ref: str
    target_family: Literal[ADEU_CORE_IR_TARGET_FAMILY]
    compiler: ArchitectureProjectionCompilerProvenance
    compiler_version: str
    projection_units: list[ArchitectureProjectionUnit]

    @model_validator(mode="after")
    def _validate_bundle(self, info: ValidationInfo) -> AdeuArchitectureProjectionBundle:
        object.__setattr__(
            self, "bundle_id", _assert_non_empty_text(self.bundle_id, field_name="bundle_id")
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
            "checkpoint_trace_ref",
            _normalize_repo_relative_path(
                self.checkpoint_trace_ref,
                field_name="checkpoint_trace_ref",
            ),
        )
        object.__setattr__(
            self,
            "compiler_version",
            _assert_non_empty_text(self.compiler_version, field_name="compiler_version"),
        )
        if self.compiler.version != self.compiler_version:
            raise ValueError("compiler_version must match compiler.version")
        if not self.projection_units:
            raise ValueError("projection_units must not be empty")
        sorted_units = sorted(self.projection_units, key=lambda item: item.projection_id)
        if self.projection_units != sorted_units:
            raise ValueError("projection_units must be sorted by projection_id")
        if len({item.projection_id for item in self.projection_units}) != len(
            self.projection_units
        ):
            raise ValueError("projection_units must not contain duplicate projection_id values")
        expected_bundle_id = _bundle_id(
            architecture_id=self.architecture_id,
            semantic_hash=self.semantic_hash,
            conformance_report_ref=self.conformance_report_ref,
            checkpoint_trace_ref=self.checkpoint_trace_ref,
            target_family=self.target_family,
            compiler=_dump_json_payload(self.compiler),
            compiler_version=self.compiler_version,
            projection_units=[_dump_json_payload(item) for item in self.projection_units],
        )
        if self.bundle_id != expected_bundle_id:
            raise ValueError(
                "bundle_id must match architecture_id, semantic_hash, consumed lineage, "
                "compiler provenance, and projection_units"
            )
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            conformance_payload = _load_repo_json(
                self.conformance_report_ref,
                repository_root=repository_root,
            )
            conformance = AdeuArchitectureConformanceReport.model_validate(
                conformance_payload,
                context=_validation_context(repository_root),
            )
            checkpoint_payload = _load_repo_json(
                self.checkpoint_trace_ref,
                repository_root=repository_root,
            )
            checkpoint_trace = AdeuArchitectureCheckpointTrace.model_validate(
                checkpoint_payload,
                context=_validation_context(repository_root),
            )
            _validate_projection_units_against_consumed_lineage(
                projection_units=self.projection_units,
                conformance=conformance,
                checkpoint_trace=checkpoint_trace,
                architecture_id=self.architecture_id,
                semantic_hash=self.semantic_hash,
                conformance_report_ref=self.conformance_report_ref,
                checkpoint_trace_ref=self.checkpoint_trace_ref,
                compiler_version=self.compiler_version,
                repository_root=repository_root,
            )
        return self


class AdeuArchitectureProjectionManifest(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_PROJECTION_MANIFEST_SCHEMA]
    manifest_id: str
    architecture_id: str
    semantic_hash: str
    conformance_report_ref: str
    checkpoint_trace_ref: str
    source_root_refs: list[ArchitectureConsumedRootRef]
    target_family: Literal[ADEU_CORE_IR_TARGET_FAMILY]
    compiler_entrypoint: Literal[V40D_COMPILER_ENTRYPOINT] = V40D_COMPILER_ENTRYPOINT
    compiler_version: str
    projection_units: list[ArchitectureProjectionUnit]
    touched_artifact_refs: list[str]
    blocked_by_ambiguity_refs: list[str]

    @model_validator(mode="after")
    def _validate_manifest(self, info: ValidationInfo) -> AdeuArchitectureProjectionManifest:
        object.__setattr__(
            self,
            "manifest_id",
            _assert_non_empty_text(self.manifest_id, field_name="manifest_id"),
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
            "checkpoint_trace_ref",
            _normalize_repo_relative_path(
                self.checkpoint_trace_ref,
                field_name="checkpoint_trace_ref",
            ),
        )
        object.__setattr__(
            self,
            "compiler_version",
            _assert_non_empty_text(self.compiler_version, field_name="compiler_version"),
        )
        if not self.projection_units:
            raise ValueError("projection_units must not be empty")
        sorted_units = sorted(self.projection_units, key=lambda item: item.projection_id)
        if self.projection_units != sorted_units:
            raise ValueError("projection_units must be sorted by projection_id")
        normalized_touched = [
            _normalize_repo_relative_path(value, field_name="touched_artifact_refs")
            for value in self.touched_artifact_refs
        ]
        object.__setattr__(
            self,
            "touched_artifact_refs",
            _assert_sorted_unique(normalized_touched, field_name="touched_artifact_refs"),
        )
        object.__setattr__(
            self,
            "blocked_by_ambiguity_refs",
            _assert_sorted_unique(
                self.blocked_by_ambiguity_refs,
                field_name="blocked_by_ambiguity_refs",
            ),
        )
        if any(
            unit.compiler_entrypoint != self.compiler_entrypoint for unit in self.projection_units
        ):
            raise ValueError("projection_units must share the manifest compiler_entrypoint")
        expected_touched = sorted(
            {
                artifact_ref
                for unit in self.projection_units
                for artifact_ref in unit.output_artifact_refs
            }
        )
        if self.touched_artifact_refs != expected_touched:
            raise ValueError(
                "touched_artifact_refs must match the union of projection_unit output_artifact_refs"
            )
        expected_blockers = sorted(
            {
                ambiguity_ref
                for unit in self.projection_units
                for ambiguity_ref in unit.blocked_by_ambiguity_refs
            }
        )
        if self.blocked_by_ambiguity_refs != expected_blockers:
            raise ValueError(
                "blocked_by_ambiguity_refs must match the union of projection-unit blocker lineage"
            )
        expected_manifest_id = _manifest_id(
            architecture_id=self.architecture_id,
            semantic_hash=self.semantic_hash,
            conformance_report_ref=self.conformance_report_ref,
            checkpoint_trace_ref=self.checkpoint_trace_ref,
            source_root_refs=[_dump_json_payload(item) for item in self.source_root_refs],
            target_family=self.target_family,
            compiler_entrypoint=self.compiler_entrypoint,
            compiler_version=self.compiler_version,
            projection_units=[_dump_json_payload(item) for item in self.projection_units],
            touched_artifact_refs=self.touched_artifact_refs,
            blocked_by_ambiguity_refs=self.blocked_by_ambiguity_refs,
        )
        if self.manifest_id != expected_manifest_id:
            raise ValueError(
                "manifest_id must match consumed lineage, compiler provenance, projection_units, "
                "touched_artifact_refs, and blocked_by_ambiguity_refs"
            )
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            conformance_payload = _load_repo_json(
                self.conformance_report_ref,
                repository_root=repository_root,
            )
            conformance = AdeuArchitectureConformanceReport.model_validate(
                conformance_payload,
                context=_validation_context(repository_root),
            )
            checkpoint_payload = _load_repo_json(
                self.checkpoint_trace_ref,
                repository_root=repository_root,
            )
            checkpoint_trace = AdeuArchitectureCheckpointTrace.model_validate(
                checkpoint_payload,
                context=_validation_context(repository_root),
            )
            if self.source_root_refs != conformance.consumed_root_refs:
                raise ValueError(
                    "source_root_refs must match the consumed_root_refs in conformance"
                )
            _validate_projection_units_against_consumed_lineage(
                projection_units=self.projection_units,
                conformance=conformance,
                checkpoint_trace=checkpoint_trace,
                architecture_id=self.architecture_id,
                semantic_hash=self.semantic_hash,
                conformance_report_ref=self.conformance_report_ref,
                checkpoint_trace_ref=self.checkpoint_trace_ref,
                compiler_version=self.compiler_version,
                repository_root=repository_root,
            )
        return self


def canonicalize_adeu_architecture_projection_bundle_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = AdeuArchitectureProjectionBundle.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return _dump_json_payload(model)


def canonicalize_adeu_architecture_projection_manifest_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = AdeuArchitectureProjectionManifest.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return _dump_json_payload(model)


def derive_v40d_adeu_core_ir(
    *,
    semantic_ir_payload: dict[str, Any],
    conformance_report_payload: dict[str, Any],
    conformance_report_path: str,
    checkpoint_trace_payload: dict[str, Any],
    checkpoint_trace_path: str,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    (
        semantic_ir,
        conformance_report,
        checkpoint_trace,
        normalized_report_path,
        normalized_trace_path,
    ) = _validate_v40d_inputs(
        semantic_ir_payload=semantic_ir_payload,
        conformance_report_payload=conformance_report_payload,
        conformance_report_path=conformance_report_path,
        checkpoint_trace_payload=checkpoint_trace_payload,
        checkpoint_trace_path=checkpoint_trace_path,
        repository_root=repository_root,
    )
    active_blockers = _active_blocking_ambiguity_refs(checkpoint_trace)
    if conformance_report.projection_readiness != "ready":
        raise ValueError("V40-D core IR lowering requires source conformance readiness = ready")
    if active_blockers:
        raise ValueError("V40-D core IR lowering may not proceed while active blockers remain")
    source_refs = _semantic_projection_source_refs(semantic_ir)
    projection_id = _projection_id(
        architecture_id=semantic_ir.architecture_id,
        target_family=ADEU_CORE_IR_TARGET_FAMILY,
        source_refs=source_refs,
    )
    payload = _build_ready_core_ir_payload(
        semantic_ir=semantic_ir,
        conformance_report_ref=normalized_report_path,
        checkpoint_trace_ref=normalized_trace_path,
        projection_id=projection_id,
        compiler_version="1",
        source_refs=source_refs,
    )
    return AdeuCoreIR.model_validate(payload).model_dump(
        mode="json", by_alias=True, exclude_none=True
    )


def _derive_v40d_projection_units(
    *,
    semantic_ir: AdeuArchitectureSemanticIR,
    conformance_report: AdeuArchitectureConformanceReport,
    checkpoint_trace: AdeuArchitectureCheckpointTrace,
    core_ir_output_path: str | None,
    repository_root: Path | None = None,
) -> list[ArchitectureProjectionUnit]:
    source_refs = _semantic_projection_source_refs(semantic_ir)
    projection_id = _projection_id(
        architecture_id=semantic_ir.architecture_id,
        target_family=ADEU_CORE_IR_TARGET_FAMILY,
        source_refs=source_refs,
    )
    active_blockers = _active_blocking_ambiguity_refs(checkpoint_trace)
    unit_blockers = sorted(blocker for blocker in active_blockers if blocker in source_refs)
    readiness: ArchitectureProjectionReadiness
    output_artifact_refs: list[str]
    if conformance_report.projection_readiness == "ready" and not unit_blockers:
        readiness = "ready"
        if core_ir_output_path is None:
            raise ValueError("ready V40-D projection units require core_ir_output_path")
        output_artifact_refs = [
            _normalize_repo_relative_path(core_ir_output_path, field_name="core_ir_output_path")
        ]
    else:
        if conformance_report.projection_readiness != "ready" and not unit_blockers:
            raise ValueError(
                "blocked V40-D lowering requires active checkpoint-trace blocker lineage"
            )
        readiness = "blocked"
        if core_ir_output_path is not None:
            raise ValueError("blocked V40-D projection units may not emit core_ir_output_path")
        output_artifact_refs = []
    unit = ArchitectureProjectionUnit.model_validate(
        {
            "projection_id": projection_id,
            "target_family": ADEU_CORE_IR_TARGET_FAMILY,
            "source_refs": source_refs,
            "readiness": readiness,
            "blocked_by_ambiguity_refs": unit_blockers,
            "output_artifact_refs": output_artifact_refs,
            "compiler_entrypoint": V40D_COMPILER_ENTRYPOINT,
        },
        context=_validation_context(repository_root),
    )
    return [unit]


def derive_v40d_projection_bundle(
    *,
    semantic_ir_payload: dict[str, Any],
    conformance_report_payload: dict[str, Any],
    conformance_report_path: str,
    checkpoint_trace_payload: dict[str, Any],
    checkpoint_trace_path: str,
    core_ir_output_path: str | None = None,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    (
        semantic_ir,
        conformance_report,
        checkpoint_trace,
        normalized_report_path,
        normalized_trace_path,
    ) = _validate_v40d_inputs(
        semantic_ir_payload=semantic_ir_payload,
        conformance_report_payload=conformance_report_payload,
        conformance_report_path=conformance_report_path,
        checkpoint_trace_payload=checkpoint_trace_payload,
        checkpoint_trace_path=checkpoint_trace_path,
        repository_root=repository_root,
    )
    projection_units = _derive_v40d_projection_units(
        semantic_ir=semantic_ir,
        conformance_report=conformance_report,
        checkpoint_trace=checkpoint_trace,
        core_ir_output_path=core_ir_output_path,
        repository_root=repository_root,
    )
    compiler = ArchitectureProjectionCompilerProvenance()
    payload = {
        "schema": ADEU_ARCHITECTURE_PROJECTION_BUNDLE_SCHEMA,
        "bundle_id": _bundle_id(
            architecture_id=semantic_ir.architecture_id,
            semantic_hash=semantic_ir.semantic_hash,
            conformance_report_ref=normalized_report_path,
            checkpoint_trace_ref=normalized_trace_path,
            target_family=ADEU_CORE_IR_TARGET_FAMILY,
            compiler=_dump_json_payload(compiler),
            compiler_version=compiler.version,
            projection_units=[_dump_json_payload(item) for item in projection_units],
        ),
        "architecture_id": semantic_ir.architecture_id,
        "semantic_hash": semantic_ir.semantic_hash,
        "conformance_report_ref": normalized_report_path,
        "checkpoint_trace_ref": normalized_trace_path,
        "target_family": ADEU_CORE_IR_TARGET_FAMILY,
        "compiler": _dump_json_payload(compiler),
        "compiler_version": compiler.version,
        "projection_units": [_dump_json_payload(item) for item in projection_units],
    }
    return canonicalize_adeu_architecture_projection_bundle_payload(
        payload,
        repository_root=repository_root,
    )


def derive_v40d_projection_manifest(
    *,
    semantic_ir_payload: dict[str, Any],
    conformance_report_payload: dict[str, Any],
    conformance_report_path: str,
    checkpoint_trace_payload: dict[str, Any],
    checkpoint_trace_path: str,
    core_ir_output_path: str | None = None,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    (
        semantic_ir,
        conformance_report,
        checkpoint_trace,
        normalized_report_path,
        normalized_trace_path,
    ) = _validate_v40d_inputs(
        semantic_ir_payload=semantic_ir_payload,
        conformance_report_payload=conformance_report_payload,
        conformance_report_path=conformance_report_path,
        checkpoint_trace_payload=checkpoint_trace_payload,
        checkpoint_trace_path=checkpoint_trace_path,
        repository_root=repository_root,
    )
    projection_units = _derive_v40d_projection_units(
        semantic_ir=semantic_ir,
        conformance_report=conformance_report,
        checkpoint_trace=checkpoint_trace,
        core_ir_output_path=core_ir_output_path,
        repository_root=repository_root,
    )
    touched_artifact_refs = sorted(
        {artifact_ref for unit in projection_units for artifact_ref in unit.output_artifact_refs}
    )
    blocked_by_ambiguity_refs = sorted(
        {
            ambiguity_ref
            for unit in projection_units
            for ambiguity_ref in unit.blocked_by_ambiguity_refs
        }
    )
    payload = {
        "schema": ADEU_ARCHITECTURE_PROJECTION_MANIFEST_SCHEMA,
        "manifest_id": _manifest_id(
            architecture_id=semantic_ir.architecture_id,
            semantic_hash=semantic_ir.semantic_hash,
            conformance_report_ref=normalized_report_path,
            checkpoint_trace_ref=normalized_trace_path,
            source_root_refs=[
                _dump_json_payload(item) for item in conformance_report.consumed_root_refs
            ],
            target_family=ADEU_CORE_IR_TARGET_FAMILY,
            compiler_entrypoint=V40D_COMPILER_ENTRYPOINT,
            compiler_version="1",
            projection_units=[_dump_json_payload(item) for item in projection_units],
            touched_artifact_refs=touched_artifact_refs,
            blocked_by_ambiguity_refs=blocked_by_ambiguity_refs,
        ),
        "architecture_id": semantic_ir.architecture_id,
        "semantic_hash": semantic_ir.semantic_hash,
        "conformance_report_ref": normalized_report_path,
        "checkpoint_trace_ref": normalized_trace_path,
        "source_root_refs": [
            _dump_json_payload(item) for item in conformance_report.consumed_root_refs
        ],
        "target_family": ADEU_CORE_IR_TARGET_FAMILY,
        "compiler_entrypoint": V40D_COMPILER_ENTRYPOINT,
        "compiler_version": "1",
        "projection_units": [_dump_json_payload(item) for item in projection_units],
        "touched_artifact_refs": touched_artifact_refs,
        "blocked_by_ambiguity_refs": blocked_by_ambiguity_refs,
    }
    return canonicalize_adeu_architecture_projection_manifest_payload(
        payload,
        repository_root=repository_root,
    )


__all__ = [
    "ADEU_ARCHITECTURE_PROJECTION_BUNDLE_SCHEMA",
    "ADEU_ARCHITECTURE_PROJECTION_MANIFEST_SCHEMA",
    "ADEU_CORE_IR_TARGET_FAMILY",
    "V40D_COMPILER_ENTRYPOINT",
    "V40D_V80_CONTRACT_SOURCE",
    "AdeuArchitectureProjectionBundle",
    "AdeuArchitectureProjectionManifest",
    "ArchitectureProjectionCompilerProvenance",
    "ArchitectureProjectionUnit",
    "canonicalize_adeu_architecture_projection_bundle_payload",
    "canonicalize_adeu_architecture_projection_manifest_payload",
    "derive_v40d_adeu_core_ir",
    "derive_v40d_projection_bundle",
    "derive_v40d_projection_manifest",
]
