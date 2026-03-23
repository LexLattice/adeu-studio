from __future__ import annotations

import re
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json, sha256_text

ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA = "adeu_architecture_intent_packet@1"
ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA = "adeu_architecture_ontology_frame@1"
ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA = "adeu_architecture_boundary_graph@1"
ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA = "adeu_architecture_world_hypothesis@1"
ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA = "adeu_architecture_semantic_ir@1"

V40A_V77_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS77.md#v40a_architecture_semantic_root_schema_contract@1"
)

ArchitectureImpactClass = Literal["low", "medium", "high", "critical"]
ArchitectureResolutionRoute = Literal["deterministic_only", "oracle_assisted", "human_only"]
ArchitectureConfidenceKind = Literal["explicit", "strongly_implied", "weakly_implied"]
ArchitectureEvaluableAs = Literal["deterministic", "contextual", "semantic"]

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")


def _validation_context(
    repository_root: Path | None = None,
    **extra: Any,
) -> dict[str, Any]:
    context = {"repository_root": repository_root}
    context.update(extra)
    return context


def _resolve_repository_root(explicit_root: Path | None = None) -> Path:
    if explicit_root is not None:
        return explicit_root.resolve(strict=True)
    return repo_root(anchor=Path(__file__))


def _normalize_repo_relative_path(raw_path: str, *, field_name: str) -> str:
    value = raw_path.strip().replace("\\", "/")
    if not value:
        raise ValueError(f"{field_name} must not be empty")
    if value.startswith("/") or value.startswith("\\") or _WINDOWS_ABSOLUTE_PATH_RE.match(value):
        raise ValueError(f"{field_name} must be repo-relative")
    parts: list[str] = []
    for part in value.split("/"):
        if part in ("", "."):
            continue
        if part == "..":
            if not parts:
                raise ValueError(f"{field_name} must not escape repository root")
            parts.pop()
            continue
        parts.append(part)
    if not parts:
        raise ValueError(f"{field_name} resolves to repository root")
    return "/".join(parts)


def _sha256_repo_file(path: str, *, repository_root: Path | None = None) -> str:
    root = _resolve_repository_root(repository_root)
    file_path = root / path
    if not file_path.is_file():
        raise ValueError(f"referenced repo-relative path does not exist: {path}")
    return sha256_text(file_path.read_text(encoding="utf-8"))


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return normalized


def _assert_sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return sorted(normalized)


def _assert_unique_preserving_order(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return normalized


def _dump_json_payload(model: BaseModel) -> dict[str, Any]:
    return model.model_dump(mode="json", exclude_none=True)


def _semantic_hash_basis(payload: dict[str, Any]) -> dict[str, Any]:
    basis = deepcopy(payload)
    basis.pop("semantic_hash", None)
    return basis


def compute_adeu_architecture_semantic_ir_hash(payload: dict[str, Any]) -> str:
    return sha256_canonical_json(_semantic_hash_basis(payload))


def _require_unique_ids(items: list[Any], *, attr_name: str, field_name: str) -> None:
    seen: set[str] = set()
    for item in items:
        value = getattr(item, attr_name)
        if value in seen:
            raise ValueError(f"{field_name} must not contain duplicate id {value!r}")
        seen.add(value)


class AuthorityBoundaryPolicy(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    no_direct_brief_to_codegen: Literal[True]
    projections_may_express_but_may_not_mint_authority: Literal[True]
    deterministic_adjudicator_authoritative: Literal[True]
    oracle_output_advisory_only: Literal[True]
    fail_closed_on_high_impact_ambiguity: Literal[True]


class ArchitectureSourceSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    source_ref_id: str
    path: str
    sha256: str

    @model_validator(mode="after")
    def _validate_source(self, info: ValidationInfo) -> ArchitectureSourceSnapshot:
        object.__setattr__(
            self,
            "source_ref_id",
            _assert_non_empty_text(self.source_ref_id, field_name="source_ref_id"),
        )
        normalized_path = _normalize_repo_relative_path(self.path, field_name="path")
        object.__setattr__(self, "path", normalized_path)
        object.__setattr__(self, "sha256", _assert_non_empty_text(self.sha256, field_name="sha256"))
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            actual = _sha256_repo_file(normalized_path, repository_root=repository_root)
            if actual != self.sha256:
                raise ValueError(f"sha256 does not match repo file contents for {normalized_path}")
        return self


class ArchitectureSourceSet(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    sources: list[ArchitectureSourceSnapshot]

    @model_validator(mode="after")
    def _validate_sources(self) -> ArchitectureSourceSet:
        if not self.sources:
            raise ValueError("sources must not be empty")
        _require_unique_ids(self.sources, attr_name="source_ref_id", field_name="sources")
        paths = [item.path for item in self.sources]
        normalized_paths = sorted(paths)
        if len(normalized_paths) != len(set(normalized_paths)):
            raise ValueError("sources must not contain duplicate paths")
        if normalized_paths != paths:
            sources_by_path = {item.path: item for item in self.sources}
            object.__setattr__(
                self,
                "sources",
                [sources_by_path[path] for path in normalized_paths],
            )
        return self


class CoverageSummary(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    covered_topics: list[str]
    unresolved_questions: list[str]

    @model_validator(mode="after")
    def _validate_coverage(self) -> CoverageSummary:
        object.__setattr__(
            self,
            "covered_topics",
            _assert_sorted_unique(self.covered_topics, field_name="covered_topics"),
        )
        object.__setattr__(
            self,
            "unresolved_questions",
            _assert_sorted_unique(self.unresolved_questions, field_name="unresolved_questions"),
        )
        return self


class ArchitectureRootCompilerProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    name: str
    version: str
    scope: Literal["root_family_only"]
    canonicalization_profile: Literal["adeu_architecture_ir.root_family.v1"]
    schema_bundle_version: str

    @model_validator(mode="after")
    def _validate_text(self) -> ArchitectureRootCompilerProvenance:
        object.__setattr__(
            self, "name", _assert_non_empty_text(self.name, field_name="compiler.name")
        )
        object.__setattr__(
            self, "version", _assert_non_empty_text(self.version, field_name="compiler.version")
        )
        object.__setattr__(
            self,
            "schema_bundle_version",
            _assert_non_empty_text(
                self.schema_bundle_version, field_name="compiler.schema_bundle_version"
            ),
        )
        return self


class ArchitectureVariantLineage(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    accepted_candidate_id: str
    candidate_ids: list[str]

    @model_validator(mode="after")
    def _validate_lineage(self) -> ArchitectureVariantLineage:
        object.__setattr__(
            self,
            "accepted_candidate_id",
            _assert_non_empty_text(
                self.accepted_candidate_id,
                field_name="accepted_candidate_id",
            ),
        )
        object.__setattr__(
            self,
            "candidate_ids",
            _assert_sorted_unique(self.candidate_ids, field_name="candidate_ids"),
        )
        if self.accepted_candidate_id not in self.candidate_ids:
            raise ValueError("accepted_candidate_id must be present in candidate_ids")
        return self


class ArchitectureIntentPacket(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA]
    intent_packet_id: str
    source_set: ArchitectureSourceSet
    requested_outcomes: list[str]
    non_goals: list[str]
    declared_constraints: list[str]
    authority_boundary_policy: AuthorityBoundaryPolicy

    @model_validator(mode="after")
    def _validate_packet(self) -> ArchitectureIntentPacket:
        object.__setattr__(
            self,
            "intent_packet_id",
            _assert_non_empty_text(self.intent_packet_id, field_name="intent_packet_id"),
        )
        object.__setattr__(
            self,
            "requested_outcomes",
            _assert_sorted_unique(self.requested_outcomes, field_name="requested_outcomes"),
        )
        object.__setattr__(
            self, "non_goals", _assert_sorted_unique(self.non_goals, field_name="non_goals")
        )
        object.__setattr__(
            self,
            "declared_constraints",
            _assert_sorted_unique(self.declared_constraints, field_name="declared_constraints"),
        )
        return self


class OntologyActor(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    actor_id: str
    kind: str
    label: str
    trust_domain: str
    authority_level: str

    @model_validator(mode="after")
    def _validate_actor(self) -> OntologyActor:
        for field_name in ("actor_id", "kind", "label", "trust_domain", "authority_level"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class OntologySurface(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    surface_id: str
    kind: str
    owner_ref: str
    authority_posture: str
    exposed_actions: list[str]

    @model_validator(mode="after")
    def _validate_surface(self) -> OntologySurface:
        for field_name in ("surface_id", "kind", "owner_ref", "authority_posture"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "exposed_actions",
            _assert_sorted_unique(self.exposed_actions, field_name="exposed_actions"),
        )
        return self


class OntologyDataObject(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    object_id: str
    label: str
    sensitivity_class: str
    source_of_truth_ref: str

    @model_validator(mode="after")
    def _validate_data_object(self) -> OntologyDataObject:
        for field_name in ("object_id", "label", "sensitivity_class", "source_of_truth_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class OntologyBoundary(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    boundary_id: str
    from_ref: str
    to_ref: str
    boundary_class: str
    auth_required: bool
    audit_required: bool

    @model_validator(mode="after")
    def _validate_boundary(self) -> OntologyBoundary:
        for field_name in ("boundary_id", "from_ref", "to_ref", "boundary_class"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class OntologyCapability(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    capability_id: str
    subject_ref: str
    action: str
    resource_ref: str
    granted_by_ref: str

    @model_validator(mode="after")
    def _validate_capability(self) -> OntologyCapability:
        for field_name in (
            "capability_id",
            "subject_ref",
            "action",
            "resource_ref",
            "granted_by_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class OntologyFlowStep(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    step_id: str
    kind: str
    actor_ref: str
    surface_ref: str
    inputs: list[str]
    outputs: list[str]
    preconditions: list[str]
    postconditions: list[str]

    @model_validator(mode="after")
    def _validate_step(self) -> OntologyFlowStep:
        for field_name in ("step_id", "kind", "actor_ref", "surface_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("inputs", "outputs", "preconditions", "postconditions"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class OntologyWorkflow(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    workflow_id: str
    entry_ref: str
    step_refs: list[str]
    terminal_state_refs: list[str]

    @model_validator(mode="after")
    def _validate_workflow(self) -> OntologyWorkflow:
        for field_name in ("workflow_id", "entry_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "step_refs",
            _assert_unique_preserving_order(self.step_refs, field_name="step_refs"),
        )
        object.__setattr__(
            self,
            "terminal_state_refs",
            _assert_sorted_unique(self.terminal_state_refs, field_name="terminal_state_refs"),
        )
        if not self.terminal_state_refs:
            raise ValueError("terminal_state_refs must not be empty")
        return self


class OntologyState(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    state_id: str
    workflow_id: str
    state_kind: str
    terminal: bool

    @model_validator(mode="after")
    def _validate_state(self) -> OntologyState:
        for field_name in ("state_id", "workflow_id", "state_kind"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class OntologyTransition(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    transition_id: str
    from_state_ref: str
    to_state_ref: str
    trigger_ref: str
    guard_refs: list[str]

    @model_validator(mode="after")
    def _validate_transition(self) -> OntologyTransition:
        for field_name in ("transition_id", "from_state_ref", "to_state_ref", "trigger_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self, "guard_refs", _assert_sorted_unique(self.guard_refs, field_name="guard_refs")
        )
        return self


class OntologyDecision(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    decision_id: str
    decider_ref: str
    authority_source_ref: str
    evidence_required_refs: list[str]
    ambiguity_default: str

    @model_validator(mode="after")
    def _validate_decision(self) -> OntologyDecision:
        for field_name in (
            "decision_id",
            "decider_ref",
            "authority_source_ref",
            "ambiguity_default",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "evidence_required_refs",
            _assert_sorted_unique(self.evidence_required_refs, field_name="evidence_required_refs"),
        )
        return self


class OntologyFailureMode(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    failure_mode_id: str
    affected_refs: list[str]
    default_disposition: str
    observable_surface_ref: str

    @model_validator(mode="after")
    def _validate_failure_mode(self) -> OntologyFailureMode:
        for field_name in ("failure_mode_id", "default_disposition", "observable_surface_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "affected_refs",
            _assert_sorted_unique(self.affected_refs, field_name="affected_refs"),
        )
        return self


def _ontology_node_ids(
    *,
    actors: list[OntologyActor],
    surfaces: list[OntologySurface],
    data_objects: list[OntologyDataObject],
    boundaries: list[OntologyBoundary],
    capabilities: list[OntologyCapability],
    workflows: list[OntologyWorkflow],
    flow_steps: list[OntologyFlowStep],
    states: list[OntologyState],
    transitions: list[OntologyTransition],
    decisions: list[OntologyDecision],
    failure_modes: list[OntologyFailureMode],
) -> dict[str, set[str]]:
    return {
        "actor_ids": {item.actor_id for item in actors},
        "surface_ids": {item.surface_id for item in surfaces},
        "object_ids": {item.object_id for item in data_objects},
        "boundary_ids": {item.boundary_id for item in boundaries},
        "capability_ids": {item.capability_id for item in capabilities},
        "workflow_ids": {item.workflow_id for item in workflows},
        "step_ids": {item.step_id for item in flow_steps},
        "state_ids": {item.state_id for item in states},
        "transition_ids": {item.transition_id for item in transitions},
        "decision_ids": {item.decision_id for item in decisions},
        "failure_mode_ids": {item.failure_mode_id for item in failure_modes},
    }


def _all_ontology_refs(groups: dict[str, set[str]]) -> set[str]:
    refs: set[str] = set()
    for values in groups.values():
        refs.update(values)
    return refs


def _validate_ontology_shape(
    *,
    actors: list[OntologyActor],
    surfaces: list[OntologySurface],
    data_objects: list[OntologyDataObject],
    boundaries: list[OntologyBoundary],
    capabilities: list[OntologyCapability],
    workflows: list[OntologyWorkflow],
    flow_steps: list[OntologyFlowStep],
    states: list[OntologyState],
    transitions: list[OntologyTransition],
    decisions: list[OntologyDecision],
    failure_modes: list[OntologyFailureMode],
) -> dict[str, set[str]]:
    _require_unique_ids(actors, attr_name="actor_id", field_name="actors")
    _require_unique_ids(surfaces, attr_name="surface_id", field_name="surfaces")
    _require_unique_ids(data_objects, attr_name="object_id", field_name="data_objects")
    _require_unique_ids(boundaries, attr_name="boundary_id", field_name="boundaries")
    _require_unique_ids(capabilities, attr_name="capability_id", field_name="capabilities")
    _require_unique_ids(workflows, attr_name="workflow_id", field_name="workflows")
    _require_unique_ids(flow_steps, attr_name="step_id", field_name="flow_steps")
    _require_unique_ids(states, attr_name="state_id", field_name="states")
    _require_unique_ids(transitions, attr_name="transition_id", field_name="transitions")
    _require_unique_ids(decisions, attr_name="decision_id", field_name="decisions")
    _require_unique_ids(failure_modes, attr_name="failure_mode_id", field_name="failure_modes")

    groups = _ontology_node_ids(
        actors=actors,
        surfaces=surfaces,
        data_objects=data_objects,
        boundaries=boundaries,
        capabilities=capabilities,
        workflows=workflows,
        flow_steps=flow_steps,
        states=states,
        transitions=transitions,
        decisions=decisions,
        failure_modes=failure_modes,
    )
    all_refs = _all_ontology_refs(groups)
    category_counts = sum(len(values) for values in groups.values())
    if len(all_refs) != category_counts:
        raise ValueError("ontology ids must be globally unique across categories")

    actor_ids = groups["actor_ids"]
    surface_ids = groups["surface_ids"]
    object_ids = groups["object_ids"]
    workflow_ids = groups["workflow_ids"]
    step_ids = groups["step_ids"]
    state_ids = groups["state_ids"]
    decision_ids = groups["decision_ids"]

    for surface in surfaces:
        if surface.owner_ref not in actor_ids:
            raise ValueError(f"surface owner_ref must resolve to actor id: {surface.owner_ref}")
    for data_object in data_objects:
        if data_object.source_of_truth_ref not in actor_ids | surface_ids:
            raise ValueError(
                f"data_object source_of_truth_ref must resolve to actor or surface id: "
                f"{data_object.source_of_truth_ref}"
            )
    for boundary in boundaries:
        if boundary.from_ref not in all_refs or boundary.to_ref not in all_refs:
            raise ValueError("boundary from_ref/to_ref must resolve to ontology ids")
    for capability in capabilities:
        if capability.subject_ref not in all_refs:
            raise ValueError(f"capability subject_ref must resolve: {capability.subject_ref}")
        if capability.resource_ref not in all_refs:
            raise ValueError(f"capability resource_ref must resolve: {capability.resource_ref}")
        if capability.granted_by_ref not in all_refs:
            raise ValueError(f"capability granted_by_ref must resolve: {capability.granted_by_ref}")
    for step in flow_steps:
        if step.actor_ref not in actor_ids:
            raise ValueError(f"flow_step actor_ref must resolve to actor id: {step.actor_ref}")
        if step.surface_ref not in surface_ids:
            raise ValueError(
                f"flow_step surface_ref must resolve to surface id: {step.surface_ref}"
            )
        for input_ref in step.inputs:
            if input_ref not in object_ids:
                raise ValueError(f"flow_step inputs must resolve to data_object ids: {input_ref}")
        for output_ref in step.outputs:
            if output_ref not in object_ids:
                raise ValueError(f"flow_step outputs must resolve to data_object ids: {output_ref}")
    for workflow in workflows:
        if workflow.entry_ref not in step_ids:
            raise ValueError(f"workflow entry_ref must resolve to step id: {workflow.entry_ref}")
        if not set(workflow.step_refs).issubset(step_ids):
            raise ValueError("workflow step_refs must resolve to step ids")
        if not set(workflow.terminal_state_refs).issubset(state_ids):
            raise ValueError("workflow terminal_state_refs must resolve to state ids")
    for state in states:
        if state.workflow_id not in workflow_ids:
            raise ValueError(f"state workflow_id must resolve to workflow id: {state.workflow_id}")
    for transition in transitions:
        if transition.from_state_ref not in state_ids or transition.to_state_ref not in state_ids:
            raise ValueError("transition state refs must resolve to state ids")
        if transition.trigger_ref not in step_ids | decision_ids:
            raise ValueError("transition trigger_ref must resolve to step or decision id")
    for decision in decisions:
        if decision.decider_ref not in actor_ids:
            raise ValueError(
                f"decision decider_ref must resolve to actor id: {decision.decider_ref}"
            )
        if decision.authority_source_ref not in actor_ids | surface_ids:
            raise ValueError("decision authority_source_ref must resolve to actor or surface id")
    for failure_mode in failure_modes:
        if failure_mode.observable_surface_ref not in surface_ids:
            raise ValueError("failure_mode observable_surface_ref must resolve to surface id")
        if not set(failure_mode.affected_refs).issubset(all_refs):
            raise ValueError("failure_mode affected_refs must resolve to ontology ids")
    return groups


class ArchitectureOntologyFrame(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA]
    ontology_frame_id: str
    intent_packet_id: str
    authority_boundary_policy: AuthorityBoundaryPolicy
    actors: list[OntologyActor]
    surfaces: list[OntologySurface]
    data_objects: list[OntologyDataObject]
    boundaries: list[OntologyBoundary]
    capabilities: list[OntologyCapability]
    workflows: list[OntologyWorkflow]
    states: list[OntologyState]
    transitions: list[OntologyTransition]
    decisions: list[OntologyDecision]
    failure_modes: list[OntologyFailureMode]
    flow_steps: list[OntologyFlowStep] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_frame(self) -> ArchitectureOntologyFrame:
        for field_name in ("ontology_frame_id", "intent_packet_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        _validate_ontology_shape(
            actors=self.actors,
            surfaces=self.surfaces,
            data_objects=self.data_objects,
            boundaries=self.boundaries,
            capabilities=self.capabilities,
            workflows=self.workflows,
            flow_steps=self.flow_steps,
            states=self.states,
            transitions=self.transitions,
            decisions=self.decisions,
            failure_modes=self.failure_modes,
        )
        return self


class BoundaryGraphEdge(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    edge_id: str
    from_ref: str
    to_ref: str
    boundary_ref: str
    crossing_class: str

    @model_validator(mode="after")
    def _validate_edge(self) -> BoundaryGraphEdge:
        for field_name in ("edge_id", "from_ref", "to_ref", "boundary_ref", "crossing_class"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class ArchitectureBoundaryGraph(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA]
    boundary_graph_id: str
    intent_packet_id: str
    authority_boundary_policy: AuthorityBoundaryPolicy
    node_refs: list[str]
    edge_set: list[BoundaryGraphEdge]
    authority_crossings: list[str]
    sensitivity_crossings: list[str]

    @model_validator(mode="after")
    def _validate_graph(self, info: ValidationInfo) -> ArchitectureBoundaryGraph:
        for field_name in ("boundary_graph_id", "intent_packet_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self, "node_refs", _assert_sorted_unique(self.node_refs, field_name="node_refs")
        )
        object.__setattr__(
            self,
            "authority_crossings",
            _assert_sorted_unique(self.authority_crossings, field_name="authority_crossings"),
        )
        object.__setattr__(
            self,
            "sensitivity_crossings",
            _assert_sorted_unique(self.sensitivity_crossings, field_name="sensitivity_crossings"),
        )
        _require_unique_ids(self.edge_set, attr_name="edge_id", field_name="edge_set")
        edge_ids = {edge.edge_id for edge in self.edge_set}
        if not set(self.authority_crossings).issubset(edge_ids):
            raise ValueError("authority_crossings must resolve to edge ids")
        if not set(self.sensitivity_crossings).issubset(edge_ids):
            raise ValueError("sensitivity_crossings must resolve to edge ids")

        ontology_frame = info.context.get("ontology_frame") if info.context else None
        if ontology_frame is not None and not isinstance(ontology_frame, ArchitectureOntologyFrame):
            ontology_frame = ArchitectureOntologyFrame.model_validate(
                ontology_frame,
                context=info.context,
            )
        if ontology_frame is not None:
            groups = _validate_ontology_shape(
                actors=ontology_frame.actors,
                surfaces=ontology_frame.surfaces,
                data_objects=ontology_frame.data_objects,
                boundaries=ontology_frame.boundaries,
                capabilities=ontology_frame.capabilities,
                workflows=ontology_frame.workflows,
                flow_steps=ontology_frame.flow_steps,
                states=ontology_frame.states,
                transitions=ontology_frame.transitions,
                decisions=ontology_frame.decisions,
                failure_modes=ontology_frame.failure_modes,
            )
            all_refs = _all_ontology_refs(groups)
            if not set(self.node_refs).issubset(all_refs):
                raise ValueError("boundary_graph.node_refs must resolve to ontology-frame node ids")
            boundary_ids = groups["boundary_ids"]
            for edge in self.edge_set:
                if edge.from_ref not in set(self.node_refs) or edge.to_ref not in set(
                    self.node_refs
                ):
                    raise ValueError("boundary graph edges must bind to declared node_refs")
                if edge.boundary_ref not in boundary_ids:
                    raise ValueError(
                        "boundary graph edge boundary_ref must resolve to ontology boundary"
                    )
        return self


class ArchitectureWorldHypothesis(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA]
    candidate_id: str
    intent_packet_id: str
    authority_boundary_policy: AuthorityBoundaryPolicy
    source_set: ArchitectureSourceSet
    coverage_summary: CoverageSummary
    ontology_bindings: list[str]
    epistemic_bindings: list[str]
    deontic_bindings: list[str]
    utility_bindings: list[str]
    authoritative: Literal[False] = False

    @model_validator(mode="after")
    def _validate_candidate(self) -> ArchitectureWorldHypothesis:
        for field_name in ("candidate_id", "intent_packet_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "ontology_bindings",
            "epistemic_bindings",
            "deontic_bindings",
            "utility_bindings",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class EpistemicAnnotation(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    annotation_id: str
    subject_ref: str
    confidence_kind: ArchitectureConfidenceKind
    evaluable_as: ArchitectureEvaluableAs

    @model_validator(mode="after")
    def _validate_annotation(self) -> EpistemicAnnotation:
        object.__setattr__(
            self,
            "annotation_id",
            _assert_non_empty_text(self.annotation_id, field_name="annotation_id"),
        )
        object.__setattr__(
            self, "subject_ref", _assert_non_empty_text(self.subject_ref, field_name="subject_ref")
        )
        return self


class EpistemicFact(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    fact_id: str
    statement: str
    source_refs: list[str]
    confidence_kind: ArchitectureConfidenceKind
    evaluable_as: ArchitectureEvaluableAs

    @model_validator(mode="after")
    def _validate_fact(self) -> EpistemicFact:
        object.__setattr__(
            self, "fact_id", _assert_non_empty_text(self.fact_id, field_name="fact_id")
        )
        object.__setattr__(
            self, "statement", _assert_non_empty_text(self.statement, field_name="statement")
        )
        object.__setattr__(
            self, "source_refs", _assert_sorted_unique(self.source_refs, field_name="source_refs")
        )
        return self


class EpistemicAssumption(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    assumption_id: str
    statement: str
    impact_class: ArchitectureImpactClass
    touches_refs: list[str]
    confidence_kind: ArchitectureConfidenceKind

    @model_validator(mode="after")
    def _validate_assumption(self) -> EpistemicAssumption:
        object.__setattr__(
            self,
            "assumption_id",
            _assert_non_empty_text(self.assumption_id, field_name="assumption_id"),
        )
        object.__setattr__(
            self, "statement", _assert_non_empty_text(self.statement, field_name="statement")
        )
        object.__setattr__(
            self,
            "touches_refs",
            _assert_sorted_unique(self.touches_refs, field_name="touches_refs"),
        )
        return self


class EpistemicAmbiguity(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    ambiguity_id: str
    question: str
    impact_class: ArchitectureImpactClass
    touches_refs: list[str]
    resolution_route: ArchitectureResolutionRoute
    evaluable_as: ArchitectureEvaluableAs

    @model_validator(mode="after")
    def _validate_ambiguity(self) -> EpistemicAmbiguity:
        object.__setattr__(
            self,
            "ambiguity_id",
            _assert_non_empty_text(self.ambiguity_id, field_name="ambiguity_id"),
        )
        object.__setattr__(
            self, "question", _assert_non_empty_text(self.question, field_name="question")
        )
        object.__setattr__(
            self,
            "touches_refs",
            _assert_sorted_unique(self.touches_refs, field_name="touches_refs"),
        )
        return self


class EpistemicEvidenceRequirement(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    evidence_id: str
    required_before_refs: list[str]
    evidence_kind: str
    source_policy: str

    @model_validator(mode="after")
    def _validate_evidence(self) -> EpistemicEvidenceRequirement:
        object.__setattr__(
            self,
            "evidence_id",
            _assert_non_empty_text(self.evidence_id, field_name="evidence_id"),
        )
        object.__setattr__(
            self,
            "required_before_refs",
            _assert_sorted_unique(self.required_before_refs, field_name="required_before_refs"),
        )
        object.__setattr__(
            self,
            "evidence_kind",
            _assert_non_empty_text(self.evidence_kind, field_name="evidence_kind"),
        )
        object.__setattr__(
            self,
            "source_policy",
            _assert_non_empty_text(self.source_policy, field_name="source_policy"),
        )
        return self


class EpistemicObservabilityHook(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    hook_id: str
    subject_ref: str
    observable_kind: str
    required_for_metrics: list[str]

    @model_validator(mode="after")
    def _validate_hook(self) -> EpistemicObservabilityHook:
        object.__setattr__(
            self, "hook_id", _assert_non_empty_text(self.hook_id, field_name="hook_id")
        )
        object.__setattr__(
            self, "subject_ref", _assert_non_empty_text(self.subject_ref, field_name="subject_ref")
        )
        object.__setattr__(
            self,
            "observable_kind",
            _assert_non_empty_text(self.observable_kind, field_name="observable_kind"),
        )
        object.__setattr__(
            self,
            "required_for_metrics",
            _assert_sorted_unique(self.required_for_metrics, field_name="required_for_metrics"),
        )
        return self


class EpistemicHypothesisBinding(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    candidate_id: str
    accepted: bool
    coverage_summary: str
    rejection_reasons: list[str]

    @model_validator(mode="after")
    def _validate_binding(self) -> EpistemicHypothesisBinding:
        object.__setattr__(
            self,
            "candidate_id",
            _assert_non_empty_text(self.candidate_id, field_name="candidate_id"),
        )
        object.__setattr__(
            self,
            "coverage_summary",
            _assert_non_empty_text(self.coverage_summary, field_name="coverage_summary"),
        )
        object.__setattr__(
            self,
            "rejection_reasons",
            _assert_sorted_unique(self.rejection_reasons, field_name="rejection_reasons"),
        )
        return self


class SemanticEpistemicsSection(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    facts: list[EpistemicFact]
    assumptions: list[EpistemicAssumption]
    ambiguities: list[EpistemicAmbiguity]
    evidence_requirements: list[EpistemicEvidenceRequirement]
    observability_hooks: list[EpistemicObservabilityHook]
    hypothesis_bindings: list[EpistemicHypothesisBinding]
    annotations: list[EpistemicAnnotation] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_epistemics(self) -> SemanticEpistemicsSection:
        _require_unique_ids(self.facts, attr_name="fact_id", field_name="facts")
        _require_unique_ids(self.assumptions, attr_name="assumption_id", field_name="assumptions")
        _require_unique_ids(self.ambiguities, attr_name="ambiguity_id", field_name="ambiguities")
        _require_unique_ids(
            self.evidence_requirements, attr_name="evidence_id", field_name="evidence_requirements"
        )
        _require_unique_ids(
            self.observability_hooks, attr_name="hook_id", field_name="observability_hooks"
        )
        _require_unique_ids(
            self.hypothesis_bindings, attr_name="candidate_id", field_name="hypothesis_bindings"
        )
        _require_unique_ids(self.annotations, attr_name="annotation_id", field_name="annotations")
        return self


class DeonticObligation(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    obligation_id: str
    statement: str
    target_refs: list[str]
    condition: str

    @model_validator(mode="after")
    def _validate_obligation(self) -> DeonticObligation:
        object.__setattr__(
            self,
            "obligation_id",
            _assert_non_empty_text(self.obligation_id, field_name="obligation_id"),
        )
        object.__setattr__(
            self, "statement", _assert_non_empty_text(self.statement, field_name="statement")
        )
        object.__setattr__(
            self, "target_refs", _assert_sorted_unique(self.target_refs, field_name="target_refs")
        )
        object.__setattr__(
            self, "condition", _assert_non_empty_text(self.condition, field_name="condition")
        )
        return self


class DeonticProhibition(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    prohibition_id: str
    statement: str
    target_refs: list[str]
    condition: str

    @model_validator(mode="after")
    def _validate_prohibition(self) -> DeonticProhibition:
        object.__setattr__(
            self,
            "prohibition_id",
            _assert_non_empty_text(self.prohibition_id, field_name="prohibition_id"),
        )
        object.__setattr__(
            self, "statement", _assert_non_empty_text(self.statement, field_name="statement")
        )
        object.__setattr__(
            self, "target_refs", _assert_sorted_unique(self.target_refs, field_name="target_refs")
        )
        object.__setattr__(
            self, "condition", _assert_non_empty_text(self.condition, field_name="condition")
        )
        return self


class DeonticPermission(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    permission_id: str
    statement: str
    target_refs: list[str]
    condition: str

    @model_validator(mode="after")
    def _validate_permission(self) -> DeonticPermission:
        object.__setattr__(
            self,
            "permission_id",
            _assert_non_empty_text(self.permission_id, field_name="permission_id"),
        )
        object.__setattr__(
            self, "statement", _assert_non_empty_text(self.statement, field_name="statement")
        )
        object.__setattr__(
            self, "target_refs", _assert_sorted_unique(self.target_refs, field_name="target_refs")
        )
        object.__setattr__(
            self, "condition", _assert_non_empty_text(self.condition, field_name="condition")
        )
        return self


class DeonticGate(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    gate_id: str
    subject_ref: str
    authority_source_ref: str
    required_refs: list[str]
    fail_closed: bool

    @model_validator(mode="after")
    def _validate_gate(self) -> DeonticGate:
        object.__setattr__(
            self, "gate_id", _assert_non_empty_text(self.gate_id, field_name="gate_id")
        )
        object.__setattr__(
            self, "subject_ref", _assert_non_empty_text(self.subject_ref, field_name="subject_ref")
        )
        object.__setattr__(
            self,
            "authority_source_ref",
            _assert_non_empty_text(self.authority_source_ref, field_name="authority_source_ref"),
        )
        object.__setattr__(
            self,
            "required_refs",
            _assert_sorted_unique(self.required_refs, field_name="required_refs"),
        )
        return self


class DeonticInvariant(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    invariant_id: str
    statement: str
    scope_refs: list[str]
    severity: ArchitectureImpactClass

    @model_validator(mode="after")
    def _validate_invariant(self) -> DeonticInvariant:
        object.__setattr__(
            self,
            "invariant_id",
            _assert_non_empty_text(self.invariant_id, field_name="invariant_id"),
        )
        object.__setattr__(
            self, "statement", _assert_non_empty_text(self.statement, field_name="statement")
        )
        object.__setattr__(
            self, "scope_refs", _assert_sorted_unique(self.scope_refs, field_name="scope_refs")
        )
        return self


class DeonticEscalationRule(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    rule_id: str
    trigger_refs: list[str]
    escalate_to: str
    default_disposition: str

    @model_validator(mode="after")
    def _validate_escalation(self) -> DeonticEscalationRule:
        object.__setattr__(
            self, "rule_id", _assert_non_empty_text(self.rule_id, field_name="rule_id")
        )
        object.__setattr__(
            self,
            "trigger_refs",
            _assert_sorted_unique(self.trigger_refs, field_name="trigger_refs"),
        )
        object.__setattr__(
            self, "escalate_to", _assert_non_empty_text(self.escalate_to, field_name="escalate_to")
        )
        object.__setattr__(
            self,
            "default_disposition",
            _assert_non_empty_text(self.default_disposition, field_name="default_disposition"),
        )
        return self


class SemanticDeonticsSection(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    obligations: list[DeonticObligation]
    prohibitions: list[DeonticProhibition]
    permissions: list[DeonticPermission]
    gates: list[DeonticGate]
    invariants: list[DeonticInvariant]
    escalation_rules: list[DeonticEscalationRule]

    @model_validator(mode="after")
    def _validate_deontics(self) -> SemanticDeonticsSection:
        _require_unique_ids(self.obligations, attr_name="obligation_id", field_name="obligations")
        _require_unique_ids(
            self.prohibitions, attr_name="prohibition_id", field_name="prohibitions"
        )
        _require_unique_ids(self.permissions, attr_name="permission_id", field_name="permissions")
        _require_unique_ids(self.gates, attr_name="gate_id", field_name="gates")
        _require_unique_ids(self.invariants, attr_name="invariant_id", field_name="invariants")
        _require_unique_ids(
            self.escalation_rules, attr_name="rule_id", field_name="escalation_rules"
        )
        return self


class UtilityGoal(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    goal_id: str
    statement: str
    served_by_refs: list[str]

    @model_validator(mode="after")
    def _validate_goal(self) -> UtilityGoal:
        object.__setattr__(
            self, "goal_id", _assert_non_empty_text(self.goal_id, field_name="goal_id")
        )
        object.__setattr__(
            self, "statement", _assert_non_empty_text(self.statement, field_name="statement")
        )
        object.__setattr__(
            self,
            "served_by_refs",
            _assert_sorted_unique(self.served_by_refs, field_name="served_by_refs"),
        )
        return self


class UtilityMetric(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    metric_id: str
    label: str
    target_expression: str
    measured_by_refs: list[str]

    @model_validator(mode="after")
    def _validate_metric(self) -> UtilityMetric:
        object.__setattr__(
            self, "metric_id", _assert_non_empty_text(self.metric_id, field_name="metric_id")
        )
        object.__setattr__(self, "label", _assert_non_empty_text(self.label, field_name="label"))
        object.__setattr__(
            self,
            "target_expression",
            _assert_non_empty_text(self.target_expression, field_name="target_expression"),
        )
        object.__setattr__(
            self,
            "measured_by_refs",
            _assert_sorted_unique(self.measured_by_refs, field_name="measured_by_refs"),
        )
        return self


class UtilityPriorityRule(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    priority_id: str
    higher_ref: str
    lower_ref: str
    condition: str

    @model_validator(mode="after")
    def _validate_priority(self) -> UtilityPriorityRule:
        for field_name in ("priority_id", "higher_ref", "lower_ref", "condition"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class UtilityTradeoff(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    tradeoff_id: str
    between_refs: list[str]
    adjudication_rule: str

    @model_validator(mode="after")
    def _validate_tradeoff(self) -> UtilityTradeoff:
        object.__setattr__(
            self,
            "tradeoff_id",
            _assert_non_empty_text(self.tradeoff_id, field_name="tradeoff_id"),
        )
        object.__setattr__(
            self,
            "between_refs",
            _assert_sorted_unique(self.between_refs, field_name="between_refs"),
        )
        object.__setattr__(
            self,
            "adjudication_rule",
            _assert_non_empty_text(self.adjudication_rule, field_name="adjudication_rule"),
        )
        return self


class SemanticUtilitySection(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    goals: list[UtilityGoal]
    metrics: list[UtilityMetric]
    priority_rules: list[UtilityPriorityRule]
    tradeoffs: list[UtilityTradeoff]

    @model_validator(mode="after")
    def _validate_utility(self) -> SemanticUtilitySection:
        _require_unique_ids(self.goals, attr_name="goal_id", field_name="goals")
        _require_unique_ids(self.metrics, attr_name="metric_id", field_name="metrics")
        _require_unique_ids(
            self.priority_rules, attr_name="priority_id", field_name="priority_rules"
        )
        _require_unique_ids(self.tradeoffs, attr_name="tradeoff_id", field_name="tradeoffs")
        if not self.goals:
            raise ValueError("goals must not be empty")
        return self


class SemanticOntologySection(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    actors: list[OntologyActor]
    surfaces: list[OntologySurface]
    data_objects: list[OntologyDataObject]
    boundaries: list[OntologyBoundary]
    capabilities: list[OntologyCapability]
    workflows: list[OntologyWorkflow]
    states: list[OntologyState]
    transitions: list[OntologyTransition]
    decisions: list[OntologyDecision]
    failure_modes: list[OntologyFailureMode]
    flow_steps: list[OntologyFlowStep] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_ontology(self) -> SemanticOntologySection:
        _validate_ontology_shape(
            actors=self.actors,
            surfaces=self.surfaces,
            data_objects=self.data_objects,
            boundaries=self.boundaries,
            capabilities=self.capabilities,
            workflows=self.workflows,
            flow_steps=self.flow_steps,
            states=self.states,
            transitions=self.transitions,
            decisions=self.decisions,
            failure_modes=self.failure_modes,
        )
        return self


class AdeuArchitectureSemanticIR(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA]
    architecture_id: str
    intent_packet_id: str
    semantic_hash: str
    compiler: ArchitectureRootCompilerProvenance
    authority_boundary_policy: AuthorityBoundaryPolicy
    source_set: ArchitectureSourceSet
    variant_lineage: ArchitectureVariantLineage
    ontology: SemanticOntologySection
    epistemics: SemanticEpistemicsSection
    deontics: SemanticDeonticsSection
    utility: SemanticUtilitySection

    @model_validator(mode="after")
    def _validate_semantic_ir(self, info: ValidationInfo) -> AdeuArchitectureSemanticIR:
        object.__setattr__(
            self,
            "architecture_id",
            _assert_non_empty_text(self.architecture_id, field_name="architecture_id"),
        )
        object.__setattr__(
            self,
            "intent_packet_id",
            _assert_non_empty_text(self.intent_packet_id, field_name="intent_packet_id"),
        )
        object.__setattr__(
            self,
            "semantic_hash",
            _assert_non_empty_text(self.semantic_hash, field_name="semantic_hash"),
        )

        ontology_groups = _validate_ontology_shape(
            actors=self.ontology.actors,
            surfaces=self.ontology.surfaces,
            data_objects=self.ontology.data_objects,
            boundaries=self.ontology.boundaries,
            capabilities=self.ontology.capabilities,
            workflows=self.ontology.workflows,
            flow_steps=self.ontology.flow_steps,
            states=self.ontology.states,
            transitions=self.ontology.transitions,
            decisions=self.ontology.decisions,
            failure_modes=self.ontology.failure_modes,
        )
        ontology_refs = _all_ontology_refs(ontology_groups)

        source_ref_ids = {item.source_ref_id for item in self.source_set.sources}
        evidence_ids = {item.evidence_id for item in self.epistemics.evidence_requirements}
        hook_ids = {item.hook_id for item in self.epistemics.observability_hooks}
        fact_ids = {item.fact_id for item in self.epistemics.facts}
        assumption_ids = {item.assumption_id for item in self.epistemics.assumptions}
        ambiguity_ids = {item.ambiguity_id for item in self.epistemics.ambiguities}
        annotation_ids = {item.annotation_id for item in self.epistemics.annotations}
        obligation_ids = {item.obligation_id for item in self.deontics.obligations}
        prohibition_ids = {item.prohibition_id for item in self.deontics.prohibitions}
        permission_ids = {item.permission_id for item in self.deontics.permissions}
        gate_ids = {item.gate_id for item in self.deontics.gates}
        invariant_ids = {item.invariant_id for item in self.deontics.invariants}
        escalation_rule_ids = {item.rule_id for item in self.deontics.escalation_rules}
        goal_ids = {item.goal_id for item in self.utility.goals}
        metric_ids = {item.metric_id for item in self.utility.metrics}
        priority_ids = {item.priority_id for item in self.utility.priority_rules}
        tradeoff_ids = {item.tradeoff_id for item in self.utility.tradeoffs}

        all_refs = (
            ontology_refs
            | source_ref_ids
            | evidence_ids
            | hook_ids
            | fact_ids
            | assumption_ids
            | ambiguity_ids
            | annotation_ids
            | obligation_ids
            | prohibition_ids
            | permission_ids
            | gate_ids
            | invariant_ids
            | escalation_rule_ids
            | goal_ids
            | metric_ids
            | priority_ids
            | tradeoff_ids
        )

        for fact in self.epistemics.facts:
            if not set(fact.source_refs).issubset(source_ref_ids):
                raise ValueError("fact.source_refs must resolve to source_set source_ref_ids")
        for assumption in self.epistemics.assumptions:
            if not set(assumption.touches_refs).issubset(all_refs):
                raise ValueError("assumption.touches_refs must resolve within semantic root")
        for ambiguity in self.epistemics.ambiguities:
            if not set(ambiguity.touches_refs).issubset(all_refs):
                raise ValueError("ambiguity.touches_refs must resolve within semantic root")
        for annotation in self.epistemics.annotations:
            if annotation.subject_ref not in all_refs:
                raise ValueError(
                    "epistemic annotation subject_ref must resolve within semantic root"
                )
        for evidence in self.epistemics.evidence_requirements:
            if not set(evidence.required_before_refs).issubset(all_refs):
                raise ValueError("evidence_requirement.required_before_refs must resolve")
        for hook in self.epistemics.observability_hooks:
            if hook.subject_ref not in ontology_refs:
                raise ValueError("observability_hook.subject_ref must resolve to ontology ref")
            if not set(hook.required_for_metrics).issubset(metric_ids):
                raise ValueError(
                    "observability_hook.required_for_metrics must resolve to metric ids"
                )
        for binding in self.epistemics.hypothesis_bindings:
            if binding.candidate_id not in set(self.variant_lineage.candidate_ids):
                raise ValueError("hypothesis_binding candidate_id must exist in variant_lineage")
        accepted_bindings = [
            binding for binding in self.epistemics.hypothesis_bindings if binding.accepted
        ]
        if len(accepted_bindings) != 1:
            raise ValueError("exactly one hypothesis_binding must be marked accepted")
        if (
            accepted_bindings[0].candidate_id
            != self.variant_lineage.accepted_candidate_id
        ):
            raise ValueError(
                "accepted hypothesis_binding must match variant_lineage.accepted_candidate_id"
            )

        for obligation in self.deontics.obligations:
            if not set(obligation.target_refs).issubset(all_refs):
                raise ValueError("obligation.target_refs must resolve within semantic root")
        for prohibition in self.deontics.prohibitions:
            if not set(prohibition.target_refs).issubset(all_refs):
                raise ValueError("prohibition.target_refs must resolve within semantic root")
        for permission in self.deontics.permissions:
            if not set(permission.target_refs).issubset(all_refs):
                raise ValueError("permission.target_refs must resolve within semantic root")
        for gate in self.deontics.gates:
            if gate.subject_ref not in all_refs:
                raise ValueError("gate.subject_ref must resolve within semantic root")
            if gate.authority_source_ref not in ontology_refs:
                raise ValueError("gate.authority_source_ref must resolve to ontology ref")
            if not set(gate.required_refs).issubset(all_refs):
                raise ValueError("gate.required_refs must resolve within semantic root")
        for invariant in self.deontics.invariants:
            if not set(invariant.scope_refs).issubset(all_refs):
                raise ValueError("invariant.scope_refs must resolve within semantic root")
        for escalation in self.deontics.escalation_rules:
            if not set(escalation.trigger_refs).issubset(all_refs):
                raise ValueError("escalation_rule.trigger_refs must resolve within semantic root")
            if escalation.escalate_to not in ontology_groups["actor_ids"]:
                raise ValueError("escalation_rule.escalate_to must resolve to actor id")

        utility_refs = goal_ids | metric_ids | priority_ids | tradeoff_ids
        for goal in self.utility.goals:
            if not set(goal.served_by_refs).issubset(all_refs):
                raise ValueError("goal.served_by_refs must resolve within semantic root")
        for metric in self.utility.metrics:
            if not set(metric.measured_by_refs).issubset(evidence_ids | hook_ids):
                raise ValueError(
                    "metric.measured_by_refs must resolve to evidence_requirement or "
                    "observability_hook ids"
                )
        for priority in self.utility.priority_rules:
            if priority.higher_ref not in utility_refs or priority.lower_ref not in utility_refs:
                raise ValueError("priority_rule refs must resolve within utility section")
        for tradeoff in self.utility.tradeoffs:
            if not set(tradeoff.between_refs).issubset(utility_refs):
                raise ValueError("tradeoff.between_refs must resolve within utility section")

        skip_semantic_hash_validation = False
        if info.context:
            skip_semantic_hash_validation = bool(
                info.context.get("skip_semantic_hash_validation")
            )
        if not skip_semantic_hash_validation:
            expected_hash = compute_adeu_architecture_semantic_ir_hash(_dump_json_payload(self))
            if self.semantic_hash != expected_hash:
                raise ValueError("semantic_hash must match canonical payload")
        return self


def canonicalize_adeu_architecture_intent_packet_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    return _dump_json_payload(
        ArchitectureIntentPacket.model_validate(
            payload,
            context=_validation_context(repository_root),
        )
    )


def canonicalize_adeu_architecture_ontology_frame_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    return _dump_json_payload(
        ArchitectureOntologyFrame.model_validate(
            payload,
            context=_validation_context(repository_root),
        )
    )


def canonicalize_adeu_architecture_boundary_graph_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
    ontology_frame: ArchitectureOntologyFrame | dict[str, Any] | None = None,
) -> dict[str, Any]:
    context = _validation_context(repository_root)
    if ontology_frame is not None:
        context["ontology_frame"] = ontology_frame
    return _dump_json_payload(
        ArchitectureBoundaryGraph.model_validate(
            payload,
            context=context,
        )
    )


def canonicalize_adeu_architecture_world_hypothesis_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    return _dump_json_payload(
        ArchitectureWorldHypothesis.model_validate(
            payload,
            context=_validation_context(repository_root),
        )
    )


def canonicalize_adeu_architecture_semantic_ir_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    return _dump_json_payload(
        AdeuArchitectureSemanticIR.model_validate(
            payload,
            context=_validation_context(repository_root),
        )
    )


def materialize_adeu_architecture_semantic_ir_payload(
    payload_without_hash: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    payload = deepcopy(payload_without_hash)
    payload["semantic_hash"] = "0" * 64
    validated = AdeuArchitectureSemanticIR.model_validate(
        payload,
        context=_validation_context(
            repository_root,
            skip_semantic_hash_validation=True,
        ),
    )
    normalized_payload = _dump_json_payload(validated)
    normalized_payload["semantic_hash"] = compute_adeu_architecture_semantic_ir_hash(
        normalized_payload
    )
    return canonicalize_adeu_architecture_semantic_ir_payload(
        normalized_payload,
        repository_root=repository_root,
    )
