from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

UXDomainPacketSchemaVersion = Literal["ux_domain_packet@1"]
UXMorphIRSchemaVersion = Literal["ux_morph_ir@1"]
V36AApprovedProfileTableSchemaVersion = Literal["v36a_first_family_approved_profile_table@1"]
V36ASameContextGlossarySchemaVersion = Literal["v36a_same_context_reachability_glossary@1"]

UXReferenceSurfaceFamily = Literal["artifact_inspector_advisory_workbench"]
UXApprovedProfileId = Literal["artifact_inspector_alternate", "artifact_inspector_reference"]
UXDensity = Literal["high", "medium"]
UXNavigationMode = Literal["hub_and_spoke", "split_pane"]
UXInformationPosture = Literal["evidence_first", "task_first"]
UXInteractionTempo = Literal["expert_fast_path", "guided"]
UXSaliencePosture = Literal[
    "action_and_diagnostics_prominent",
    "evidence_and_status_prominent",
]
UXStateExposure = Literal["full_explicit", "progressive"]
UXCommandPosture = Literal["dual_lane", "safe_buffered"]

UXPrimaryUserArchetype = Literal["expert_operator"]
UXDeviceClass = Literal["desktop"]
UXRiskLevel = Literal["high"]
UXTrustSensitivity = Literal["authority_and_evidence_sensitive"]
UXInteractionMode = Literal["analysis_then_commit"]
UXEnvironmentAssumption = Literal[
    "bounded_workbench_context_available",
    "multi_region_workbench_allowed",
]
UXDomainTask = Literal[
    "compare_candidate_variant",
    "inspect_evidence_lane",
    "inspect_source_artifact",
    "review_diagnostics_lane",
    "select_advisory_action",
]
UXLatencyAssumption = Literal[
    "background_artifact_fetch_permitted",
    "network_variability_must_remain_visible",
    "subsecond_local_state_transitions_expected",
]
UXReversibilityPolicy = Literal[
    "advisory_actions_reversible",
    "commit_actions_require_explicit_gate",
    "destructive_actions_remain_separately_gated",
]
UXRequiredEvidenceVisibility = Literal[
    "evidence_must_be_same_context_reachable_before_commit",
    "no_commit_or_destructive_barrier_before_required_evidence",
    "no_route_change_before_required_evidence",
]
UXUtilityObjective = Literal[
    "error_prevention",
    "operator_speed",
    "trust_calibration",
]

UXSurfaceCompilationUnit = Literal[
    "surface_root",
    "bounded_workbench",
    "region",
    "lane",
    "action_cluster",
]
UXEntity = Literal[
    "action",
    "artifact",
    "candidate_variant",
    "commit_gate",
    "diagnostic",
    "evidence_packet",
    "trust_lane",
]
UXView = Literal["collection_view", "detail_view", "diff_view", "evidence_view"]
UXRegion = Literal[
    "action_region",
    "evidence_region",
    "navigation_region",
    "primary_work_region",
    "status_region",
]
UXActionCluster = Literal[
    "advisory_action_cluster",
    "commit_action_cluster",
    "comparison_action_cluster",
]
UXEvidenceSurface = Literal["diagnostics_lane", "evidence_lane", "source_lane"]
UXTrustSurface = Literal["authority_marker_lane", "status_marker_lane", "trust_boundary_lane"]
UXEpistemicState = Literal[
    "loading",
    "draft",
    "candidate",
    "validated",
    "authoritative",
    "conflicted",
    "stale",
    "ambiguous",
]
UXVisibilityRule = Literal[
    "authoritative_state_must_be_distinguishable",
    "provisional_state_must_be_marked",
    "unknown_state_must_not_render_as_success",
]
UXRequiredRule = Literal[
    "evidence_before_commit",
    "observable_state_feedback",
    "separate_advisory_actions_from_commit_actions",
    "unambiguous_primary_action",
]
UXForbiddenRule = Literal[
    "authority_minting_by_surface_arrangement",
    "single_click_irreversible_commit",
    "visual_collapse_of_advisory_and_authoritative_material",
]
UXInvariant = Literal[
    "destructive_action_gating",
    "evidence_before_commit_visibility",
    "observable_state_transitions",
    "trust_boundary_clarity",
    "unambiguous_primary_action",
]
UXMorphableChoice = Literal[
    "disclosure_style",
    "navigation_placement",
    "region_arrangement",
    "within_bound_component_topology",
]

SameContextReachableTerm = Literal[
    "bounded_workbench_focus_shift",
    "bounded_workbench_position_shift",
    "bounded_workbench_state_reveal",
]
ContextBreakTerm = Literal[
    "bounded_workbench_replacement",
    "detached_surface_replacement",
    "route_transition",
]
ForbiddenBarrierTerm = Literal["authority_escalation_step", "cross_workbench_dependency"]
CommitOrDestructiveBarrierTerm = Literal["commit_action", "destructive_action"]

UX_DOMAIN_PACKET_SCHEMA = "ux_domain_packet@1"
UX_MORPH_IR_SCHEMA = "ux_morph_ir@1"
V36A_APPROVED_PROFILE_TABLE_SCHEMA = "v36a_first_family_approved_profile_table@1"
V36A_SAME_CONTEXT_GLOSSARY_SCHEMA = "v36a_same_context_reachability_glossary@1"
V36A_REFERENCE_SURFACE_FAMILY = "artifact_inspector_advisory_workbench"
V36A_CANONICAL_REFERENCE_PROFILE_ID = "artifact_inspector_reference"
V36A_ALTERNATE_LAWFUL_PROFILE_ID = "artifact_inspector_alternate"

FROZEN_SURFACE_COMPILATION_UNITS: tuple[UXSurfaceCompilationUnit, ...] = (
    "surface_root",
    "bounded_workbench",
    "region",
    "lane",
    "action_cluster",
)
FROZEN_ALLOWED_MORPH_AXES: tuple[str, ...] = (
    "density",
    "navigation_mode",
    "information_posture",
    "interaction_tempo",
    "salience_posture",
    "state_exposure",
    "command_posture",
)
FROZEN_EPISTEMIC_STATES: tuple[UXEpistemicState, ...] = (
    "loading",
    "draft",
    "candidate",
    "validated",
    "authoritative",
    "conflicted",
    "stale",
    "ambiguous",
)
FROZEN_SAME_CONTEXT_REACHABLE_TERMS: tuple[SameContextReachableTerm, ...] = (
    "bounded_workbench_focus_shift",
    "bounded_workbench_position_shift",
    "bounded_workbench_state_reveal",
)
FROZEN_CONTEXT_BREAK_TERMS: tuple[ContextBreakTerm, ...] = (
    "bounded_workbench_replacement",
    "detached_surface_replacement",
    "route_transition",
)
FROZEN_FORBIDDEN_BARRIER_TERMS: tuple[ForbiddenBarrierTerm, ...] = (
    "authority_escalation_step",
    "cross_workbench_dependency",
)
FROZEN_COMMIT_OR_DESTRUCTIVE_BARRIER_TERMS: tuple[CommitOrDestructiveBarrierTerm, ...] = (
    "commit_action",
    "destructive_action",
)

_WIDGET_SEMANTIC_TOKENS: tuple[str, ...] = (
    "tab",
    "drawer",
    "modal",
    "accordion",
    "viewport",
    "fold",
)


def _assert_sorted_unique(values: list[str], *, field_name: str) -> None:
    if not values:
        raise ValueError(f"{field_name} must not be empty")
    if any(not value for value in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _assert_sorted_distinct(values: list[str], *, field_name: str) -> None:
    if any(not value for value in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _assert_exact_sequence(
    values: list[str], *, expected: tuple[str, ...], field_name: str
) -> None:
    if values != list(expected):
        raise ValueError(f"{field_name} must equal the frozen sequence {list(expected)!r}")


class UXSupportingArtifactRefs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    approved_profile_table_schema: V36AApprovedProfileTableSchemaVersion = (
        V36A_APPROVED_PROFILE_TABLE_SCHEMA
    )
    same_context_reachability_glossary_schema: V36ASameContextGlossarySchemaVersion = (
        V36A_SAME_CONTEXT_GLOSSARY_SCHEMA
    )


class UXAuthorityBoundaryPolicy(BaseModel):
    model_config = ConfigDict(extra="forbid")

    no_free_form_ui_codegen_without_ir: Literal[True] = True
    no_visual_authority_inflation: Literal[True] = True
    ui_artifacts_may_express_but_may_not_mint_authority: Literal[True] = True


class UXMorphAxisValues(BaseModel):
    model_config = ConfigDict(extra="forbid")

    density: UXDensity
    navigation_mode: UXNavigationMode
    information_posture: UXInformationPosture
    interaction_tempo: UXInteractionTempo
    salience_posture: UXSaliencePosture
    state_exposure: UXStateExposure
    command_posture: UXCommandPosture

    def signature(self) -> tuple[str, str, str, str, str, str, str]:
        return (
            self.density,
            self.navigation_mode,
            self.information_posture,
            self.interaction_tempo,
            self.salience_posture,
            self.state_exposure,
            self.command_posture,
        )


class UXApprovedProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    profile_id: UXApprovedProfileId
    label: str = Field(min_length=1)
    morph_axes: UXMorphAxisValues


class V36AFirstFamilyApprovedProfileTable(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: V36AApprovedProfileTableSchemaVersion = V36A_APPROVED_PROFILE_TABLE_SCHEMA
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    canonical_reference_profile_id: Literal["artifact_inspector_reference"] = (
        V36A_CANONICAL_REFERENCE_PROFILE_ID
    )
    alternate_lawful_profile_id: Literal["artifact_inspector_alternate"] = (
        V36A_ALTERNATE_LAWFUL_PROFILE_ID
    )
    profiles: list[UXApprovedProfile]

    @model_validator(mode="after")
    def _validate_contract(self) -> "V36AFirstFamilyApprovedProfileTable":
        if len(self.profiles) != 2:
            raise ValueError("profiles must contain exactly two entries")
        profile_ids = [profile.profile_id for profile in self.profiles]
        if profile_ids != [
            self.canonical_reference_profile_id,
            self.alternate_lawful_profile_id,
        ]:
            raise ValueError(
                "profiles must enumerate canonical reference profile first and alternate lawful "
                "profile second"
            )
        signatures = [profile.morph_axes.signature() for profile in self.profiles]
        if len(signatures) != len(set(signatures)):
            raise ValueError("profiles must not contain duplicate axis combinations")
        return self


class V36ASameContextReachabilityGlossary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: V36ASameContextGlossarySchemaVersion = V36A_SAME_CONTEXT_GLOSSARY_SCHEMA
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    same_context_reachable: list[SameContextReachableTerm]
    context_break: list[ContextBreakTerm]
    forbidden_barrier: list[ForbiddenBarrierTerm]
    commit_or_destructive_barrier: list[CommitOrDestructiveBarrierTerm]

    @model_validator(mode="after")
    def _validate_contract(self) -> "V36ASameContextReachabilityGlossary":
        _assert_exact_sequence(
            self.same_context_reachable,
            expected=FROZEN_SAME_CONTEXT_REACHABLE_TERMS,
            field_name="same_context_reachable",
        )
        _assert_exact_sequence(
            self.context_break,
            expected=FROZEN_CONTEXT_BREAK_TERMS,
            field_name="context_break",
        )
        _assert_exact_sequence(
            self.forbidden_barrier,
            expected=FROZEN_FORBIDDEN_BARRIER_TERMS,
            field_name="forbidden_barrier",
        )
        _assert_exact_sequence(
            self.commit_or_destructive_barrier,
            expected=FROZEN_COMMIT_OR_DESTRUCTIVE_BARRIER_TERMS,
            field_name="commit_or_destructive_barrier",
        )
        for field_name in (
            "same_context_reachable",
            "context_break",
            "forbidden_barrier",
            "commit_or_destructive_barrier",
        ):
            for token in getattr(self, field_name):
                normalized = token.lower()
                if any(widget_token in normalized for widget_token in _WIDGET_SEMANTIC_TOKENS):
                    raise ValueError(f"{field_name} must remain substrate-level: {token}")
        return self


class UXDomainPacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXDomainPacketSchemaVersion = UX_DOMAIN_PACKET_SCHEMA
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: UXApprovedProfileId
    supporting_artifacts: UXSupportingArtifactRefs = Field(default_factory=UXSupportingArtifactRefs)
    authority_boundary_policy: UXAuthorityBoundaryPolicy = Field(
        default_factory=UXAuthorityBoundaryPolicy
    )
    domain: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    primary_user_archetype: UXPrimaryUserArchetype
    device_class: UXDeviceClass
    environment_assumptions: list[UXEnvironmentAssumption]
    risk_level: UXRiskLevel
    trust_sensitivity: UXTrustSensitivity
    interaction_mode: UXInteractionMode
    tasks: list[UXDomainTask]
    latency_assumptions: list[UXLatencyAssumption]
    reversibility_policies: list[UXReversibilityPolicy]
    required_evidence_visibility: list[UXRequiredEvidenceVisibility]
    utility_ranking: list[UXUtilityObjective]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXDomainPacket":
        _assert_sorted_unique(
            self.environment_assumptions,
            field_name="environment_assumptions",
        )
        _assert_sorted_unique(self.tasks, field_name="tasks")
        _assert_sorted_unique(self.latency_assumptions, field_name="latency_assumptions")
        _assert_sorted_unique(self.reversibility_policies, field_name="reversibility_policies")
        _assert_sorted_unique(
            self.required_evidence_visibility,
            field_name="required_evidence_visibility",
        )
        if len(self.utility_ranking) != len(set(self.utility_ranking)):
            raise ValueError("utility_ranking must not contain duplicates")
        return self


class UXMorphContext(BaseModel):
    model_config = ConfigDict(extra="forbid")

    primary_user_archetype: UXPrimaryUserArchetype
    device_class: UXDeviceClass
    risk_level: UXRiskLevel
    trust_sensitivity: UXTrustSensitivity
    interaction_mode: UXInteractionMode


class UXOntology(BaseModel):
    model_config = ConfigDict(extra="forbid")

    entities: list[UXEntity]
    views: list[UXView]
    regions: list[UXRegion]
    action_clusters: list[UXActionCluster]
    evidence_surfaces: list[UXEvidenceSurface]
    trust_surfaces: list[UXTrustSurface]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXOntology":
        _assert_sorted_unique(self.entities, field_name="ontology.entities")
        _assert_sorted_unique(self.views, field_name="ontology.views")
        _assert_sorted_unique(self.regions, field_name="ontology.regions")
        _assert_sorted_unique(self.action_clusters, field_name="ontology.action_clusters")
        _assert_sorted_unique(self.evidence_surfaces, field_name="ontology.evidence_surfaces")
        _assert_sorted_unique(self.trust_surfaces, field_name="ontology.trust_surfaces")
        return self


class UXEpistemics(BaseModel):
    model_config = ConfigDict(extra="forbid")

    knowledge_states: list[UXEpistemicState]
    visibility_rules: list[UXVisibilityRule]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXEpistemics":
        _assert_exact_sequence(
            self.knowledge_states,
            expected=FROZEN_EPISTEMIC_STATES,
            field_name="epistemics.knowledge_states",
        )
        _assert_sorted_unique(self.visibility_rules, field_name="epistemics.visibility_rules")
        return self


class UXDeontics(BaseModel):
    model_config = ConfigDict(extra="forbid")

    required: list[UXRequiredRule]
    forbidden: list[UXForbiddenRule]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXDeontics":
        _assert_sorted_unique(self.required, field_name="deontics.required")
        _assert_sorted_unique(self.forbidden, field_name="deontics.forbidden")
        return self


class UXUtility(BaseModel):
    model_config = ConfigDict(extra="forbid")

    objectives: list[UXUtilityObjective]
    priority_order: list[UXUtilityObjective]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXUtility":
        _assert_sorted_unique(self.objectives, field_name="utility.objectives")
        if len(self.priority_order) != len(set(self.priority_order)):
            raise ValueError("utility.priority_order must not contain duplicates")
        if sorted(self.priority_order) != sorted(self.objectives):
            raise ValueError("utility.priority_order must be a permutation of utility.objectives")
        return self


class UXMorphIR(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXMorphIRSchemaVersion = UX_MORPH_IR_SCHEMA
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: UXApprovedProfileId
    supporting_artifacts: UXSupportingArtifactRefs = Field(default_factory=UXSupportingArtifactRefs)
    authority_boundary_policy: UXAuthorityBoundaryPolicy = Field(
        default_factory=UXAuthorityBoundaryPolicy
    )
    surface_compilation_units: list[UXSurfaceCompilationUnit]
    context: UXMorphContext
    ontology: UXOntology
    epistemics: UXEpistemics
    deontics: UXDeontics
    utility: UXUtility
    invariants: list[UXInvariant]
    morphable_surface_choices: list[UXMorphableChoice]
    morph_axes: UXMorphAxisValues

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXMorphIR":
        _assert_exact_sequence(
            self.surface_compilation_units,
            expected=FROZEN_SURFACE_COMPILATION_UNITS,
            field_name="surface_compilation_units",
        )
        _assert_sorted_unique(self.invariants, field_name="invariants")
        _assert_sorted_unique(
            self.morphable_surface_choices,
            field_name="morphable_surface_choices",
        )
        return self


def canonicalize_ux_domain_packet_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = UXDomainPacket.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_morph_ir_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = UXMorphIR.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_v36a_approved_profile_table_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = V36AFirstFamilyApprovedProfileTable.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_v36a_same_context_glossary_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = V36ASameContextReachabilityGlossary.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def assert_v36a_reference_instance_binding(
    *,
    domain_packet: UXDomainPacket,
    morph_ir: UXMorphIR,
) -> None:
    for field_name in ("reference_surface_family", "reference_instance_id", "approved_profile_id"):
        if getattr(domain_packet, field_name) != getattr(morph_ir, field_name):
            raise ValueError(f"reference instance binding mismatch for {field_name}")
    if domain_packet.supporting_artifacts != morph_ir.supporting_artifacts:
        raise ValueError("reference instance binding mismatch for supporting_artifacts")
    if domain_packet.authority_boundary_policy != morph_ir.authority_boundary_policy:
        raise ValueError("reference instance binding mismatch for authority_boundary_policy")
    for field_name in UXMorphContext.model_fields:
        if getattr(domain_packet, field_name) != getattr(morph_ir.context, field_name):
            raise ValueError(f"reference instance binding mismatch for {field_name}")
    if domain_packet.utility_ranking != morph_ir.utility.priority_order:
        raise ValueError("reference instance binding mismatch for utility_ranking")


def approved_profile_for_id(
    profile_table: V36AFirstFamilyApprovedProfileTable,
    *,
    approved_profile_id: UXApprovedProfileId,
) -> UXApprovedProfile:
    for profile in profile_table.profiles:
        if profile.profile_id == approved_profile_id:
            return profile
    raise ValueError(f"approved profile id not found: {approved_profile_id}")


def approved_profile_combination_allowed(
    profile_table: V36AFirstFamilyApprovedProfileTable,
    *,
    morph_axes: UXMorphAxisValues,
) -> bool:
    signature = morph_axes.signature()
    return any(profile.morph_axes.signature() == signature for profile in profile_table.profiles)


def assert_v36a_reference_bundle_consistent(
    *,
    domain_packet: UXDomainPacket,
    morph_ir: UXMorphIR,
    approved_profile_table: V36AFirstFamilyApprovedProfileTable,
    same_context_glossary: V36ASameContextReachabilityGlossary,
) -> None:
    assert_v36a_reference_instance_binding(domain_packet=domain_packet, morph_ir=morph_ir)

    if approved_profile_table.reference_surface_family != domain_packet.reference_surface_family:
        raise ValueError("approved profile table reference_surface_family mismatch")
    if same_context_glossary.reference_surface_family != domain_packet.reference_surface_family:
        raise ValueError("same-context glossary reference_surface_family mismatch")

    approved_profile = approved_profile_for_id(
        approved_profile_table,
        approved_profile_id=morph_ir.approved_profile_id,
    )
    if approved_profile.morph_axes.signature() != morph_ir.morph_axes.signature():
        raise ValueError("approved profile binding mismatch for morph axes")
    if not approved_profile_combination_allowed(
        approved_profile_table,
        morph_axes=morph_ir.morph_axes,
    ):
        raise ValueError("morph axes are not part of the approved profile table")


UXSurfaceProjectionSchemaVersion = Literal["ux_surface_projection@1"]
UXInteractionContractSchemaVersion = Literal["ux_interaction_contract@1"]
UXProjectionLaneRole = Literal[
    "action_lane",
    "diagnostics_lane",
    "evidence_lane",
    "navigation_lane",
    "source_lane",
    "status_lane",
    "trust_boundary_lane",
    "work_context_lane",
]
UXResponsiveBehavior = Literal[
    "desktop_split_pane_preserved",
    "narrow_width_context_preserved_without_route_change",
]
UXActionAuthorityPosture = Literal["advisory", "authoritative", "commit_or_approval_gate"]
UXProjectionStateSurfaceKind = Literal[
    "authoritative_state_surface",
    "diagnostic_state_surface",
    "provisional_state_surface",
    "warning_state_surface",
]
UXProvenanceHookTargetKind = Literal[
    "action_cluster",
    "authority_bearing_control",
    "evidence_bearing_region",
    "projection_unit",
    "state_distinction_surface",
]
UXBindingTargetKind = Literal[
    "advisory_action",
    "authoritative_action",
    "commit_or_approval_gate",
    "diagnostic_surface",
    "disabled_or_unavailable_gated_state",
    "required_evidence_reachability_anchor",
    "status_surface",
    "warning_surface",
]
UXAuthoritativeGateSourceKind = Literal[
    "accepted_governance_artifact",
    "accepted_v35_runtime_authority_artifact",
]
UXSurfaceEvent = Literal[
    "focus_evidence_lane",
    "focus_source_artifact",
    "open_commit_review",
    "run_advisory_action",
    "submit_commit_request",
]
UXInteractionPrecondition = Literal[
    "candidate_context_available",
    "commit_gate_rendered",
    "required_evidence_reachable",
    "trust_boundary_visible",
]
UXUserVisibleConsequence = Literal[
    "advisory_action_selection_visible",
    "commit_review_revealed",
    "evidence_focus_visible",
    "request_submission_visible",
    "source_focus_visible",
]
UXRequestedRuntimeEffectKind = Literal[
    "advisory_action_requested",
    "artifact_focus_requested",
    "commit_review_requested",
    "commit_submission_requested",
    "evidence_focus_requested",
]
UXRuntimeVisibleConsequenceKind = Literal[
    "advisory_selection_visible",
    "bounded_context_focus_visible",
    "gated_pending_confirmation_visible",
    "provisional_request_visible",
    "request_submission_visible",
    "status_feedback_visible",
]
UXRuntimeTruthPosture = Literal["accepted_effect_confirmed", "provisional", "request_only"]
UXRollbackPath = Literal["clear_pending_request", "none_required", "restore_previous_focus"]
UXFailureSurface = Literal["action_lane", "status_lane", "trust_boundary_lane"]
UXSuccessSurface = Literal["action_lane", "status_lane", "work_context_lane"]

UX_SURFACE_PROJECTION_SCHEMA = "ux_surface_projection@1"
UX_INTERACTION_CONTRACT_SCHEMA = "ux_interaction_contract@1"
FROZEN_V36B_PROVENANCE_HOOK_TARGETS: tuple[UXProvenanceHookTargetKind, ...] = (
    "projection_unit",
    "action_cluster",
    "authority_bearing_control",
    "evidence_bearing_region",
    "state_distinction_surface",
)
FROZEN_V36B_IMPLEMENTATION_BINDING_TARGETS: tuple[UXBindingTargetKind, ...] = (
    "commit_or_approval_gate",
    "advisory_action",
    "authoritative_action",
    "disabled_or_unavailable_gated_state",
    "required_evidence_reachability_anchor",
    "warning_surface",
    "status_surface",
    "diagnostic_surface",
)


class UXProjectionInteractionSupportingArtifactRefs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    ux_domain_packet_schema: UXDomainPacketSchemaVersion = UX_DOMAIN_PACKET_SCHEMA
    ux_morph_ir_schema: UXMorphIRSchemaVersion = UX_MORPH_IR_SCHEMA
    approved_profile_table_schema: V36AApprovedProfileTableSchemaVersion = (
        V36A_APPROVED_PROFILE_TABLE_SCHEMA
    )
    same_context_reachability_glossary_schema: V36ASameContextGlossarySchemaVersion = (
        V36A_SAME_CONTEXT_GLOSSARY_SCHEMA
    )


def build_v36b_stable_provenance_hook_id(
    *, reference_instance_id: str, target_kind: str, target_ref: str
) -> str:
    return f"v36b.prov:{reference_instance_id}:{target_kind}:{target_ref}"


def build_v36b_stable_binding_id(
    *,
    reference_instance_id: str,
    target_kind: str,
    target_ref: str,
) -> str:
    return f"v36b.bind:{reference_instance_id}:{target_kind}:{target_ref}"


def _reference_instance_id_from_v36b_target_ref(*, target_ref: str, field_name: str) -> str:
    reference_instance_id, separator, _suffix = target_ref.partition(":")
    if not separator or not reference_instance_id:
        raise ValueError(f"{field_name} must begin with the frozen reference_instance_id prefix")
    return reference_instance_id


def _assert_v36b_record_reference_instance_binding(
    *,
    reference_instance_id: str,
    hooks: list["UXStableProvenanceHook"],
    bindings: list["UXImplementationObservableBinding"],
) -> None:
    for index, hook in enumerate(hooks):
        hook_reference_instance_id = _reference_instance_id_from_v36b_target_ref(
            target_ref=hook.target_ref,
            field_name=f"stable_provenance_hooks[{index}].target_ref",
        )
        if hook_reference_instance_id != reference_instance_id:
            raise ValueError(
                "stable_provenance_hooks target_ref must bind to bundle reference_instance_id"
            )
    for index, binding in enumerate(bindings):
        binding_reference_instance_id = _reference_instance_id_from_v36b_target_ref(
            target_ref=binding.target_ref,
            field_name=f"implementation_observable_bindings[{index}].target_ref",
        )
        if binding_reference_instance_id != reference_instance_id:
            raise ValueError(
                "implementation_observable_bindings target_ref must bind to bundle "
                "reference_instance_id"
            )


class UXStableProvenanceHook(BaseModel):
    model_config = ConfigDict(extra="forbid")

    hook_id: str = Field(min_length=1)
    source_schema: Literal["ux_interaction_contract@1", "ux_surface_projection@1"]
    target_kind: UXProvenanceHookTargetKind
    target_ref: str = Field(min_length=1)
    source_path: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXStableProvenanceHook":
        expected = build_v36b_stable_provenance_hook_id(
            reference_instance_id=_reference_instance_id_from_v36b_target_ref(
                target_ref=self.target_ref,
                field_name="stable_provenance_hooks.target_ref",
            ),
            target_kind=self.target_kind,
            target_ref=self.target_ref,
        )
        if self.hook_id != expected:
            raise ValueError("stable provenance hook id must match the frozen deterministic format")
        return self


class UXImplementationObservableBinding(BaseModel):
    model_config = ConfigDict(extra="forbid")

    binding_id: str = Field(min_length=1)
    source_schema: Literal["ux_interaction_contract@1", "ux_surface_projection@1"]
    target_kind: UXBindingTargetKind
    target_ref: str = Field(min_length=1)
    binding_token: str = Field(min_length=1)
    source_path: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXImplementationObservableBinding":
        expected = build_v36b_stable_binding_id(
            reference_instance_id=_reference_instance_id_from_v36b_target_ref(
                target_ref=self.target_ref,
                field_name="implementation_observable_bindings.target_ref",
            ),
            target_kind=self.target_kind,
            target_ref=self.target_ref,
        )
        if self.binding_id != expected:
            raise ValueError("implementation binding id must match the frozen deterministic format")
        return self


class UXProjectionRegion(BaseModel):
    model_config = ConfigDict(extra="forbid")

    region_id: str = Field(min_length=1)
    region_kind: UXRegion
    placement_index: int = Field(ge=0)
    lane_ids: list[str]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXProjectionRegion":
        _assert_sorted_unique(self.lane_ids, field_name=f"region[{self.region_id}].lane_ids")
        return self


class UXProjectionLane(BaseModel):
    model_config = ConfigDict(extra="forbid")

    lane_id: str = Field(min_length=1)
    lane_role: UXProjectionLaneRole
    region_id: str = Field(min_length=1)
    placement_index: int = Field(ge=0)


class UXProjectionActionCluster(BaseModel):
    model_config = ConfigDict(extra="forbid")

    cluster_id: str = Field(min_length=1)
    cluster_kind: UXActionCluster
    lane_id: str = Field(min_length=1)
    authority_posture: UXActionAuthorityPosture
    primary_cluster: bool = False


class UXProjectionStateSurface(BaseModel):
    model_config = ConfigDict(extra="forbid")

    surface_id: str = Field(min_length=1)
    lane_id: str = Field(min_length=1)
    surface_kind: UXProjectionStateSurfaceKind


class UXEvidenceBeforeCommitProjection(BaseModel):
    model_config = ConfigDict(extra="forbid")

    same_context_reachability_glossary: V36ASameContextReachabilityGlossary
    required_evidence_region_ids: list[str]
    required_evidence_lane_ids: list[str]
    route_change_required: Literal[False] = False
    commit_or_destructive_action_required: Literal[False] = False

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXEvidenceBeforeCommitProjection":
        _assert_sorted_unique(
            self.required_evidence_region_ids,
            field_name="evidence_before_commit.required_evidence_region_ids",
        )
        _assert_sorted_unique(
            self.required_evidence_lane_ids,
            field_name="evidence_before_commit.required_evidence_lane_ids",
        )
        return self


class UXSurfaceProjection(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXSurfaceProjectionSchemaVersion = UX_SURFACE_PROJECTION_SCHEMA
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: UXApprovedProfileId
    supporting_artifacts: UXProjectionInteractionSupportingArtifactRefs = Field(
        default_factory=UXProjectionInteractionSupportingArtifactRefs
    )
    authority_boundary_policy: UXAuthorityBoundaryPolicy = Field(
        default_factory=UXAuthorityBoundaryPolicy
    )
    surface_compilation_units: list[UXSurfaceCompilationUnit]
    surface_root_id: str = Field(min_length=1)
    bounded_workbench_id: str = Field(min_length=1)
    responsive_behaviors: list[UXResponsiveBehavior]
    regions: list[UXProjectionRegion]
    lanes: list[UXProjectionLane]
    action_clusters: list[UXProjectionActionCluster]
    state_surfaces: list[UXProjectionStateSurface]
    evidence_before_commit: UXEvidenceBeforeCommitProjection
    stable_provenance_hooks: list[UXStableProvenanceHook]
    implementation_observable_bindings: list[UXImplementationObservableBinding]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXSurfaceProjection":
        _assert_exact_sequence(
            self.surface_compilation_units,
            expected=FROZEN_SURFACE_COMPILATION_UNITS,
            field_name="surface_compilation_units",
        )
        _assert_sorted_unique(self.responsive_behaviors, field_name="responsive_behaviors")
        region_ids = [region.region_id for region in self.regions]
        lane_ids = [lane.lane_id for lane in self.lanes]
        cluster_ids = [cluster.cluster_id for cluster in self.action_clusters]
        state_surface_ids = [surface.surface_id for surface in self.state_surfaces]
        _assert_sorted_unique(region_ids, field_name="regions.region_id")
        _assert_sorted_unique(lane_ids, field_name="lanes.lane_id")
        _assert_sorted_unique(cluster_ids, field_name="action_clusters.cluster_id")
        _assert_sorted_unique(state_surface_ids, field_name="state_surfaces.surface_id")

        region_id_set = set(region_ids)
        lane_id_set = set(lane_ids)
        lane_ids_by_region_id = {
            region.region_id: {
                lane.lane_id for lane in self.lanes if lane.region_id == region.region_id
            }
            for region in self.regions
        }
        for lane in self.lanes:
            if lane.region_id not in region_id_set:
                raise ValueError(f"lane references unknown region_id: {lane.region_id}")
        for region in self.regions:
            if any(lane_id not in lane_id_set for lane_id in region.lane_ids):
                raise ValueError(f"region references unknown lane_id: {region.region_id}")
            if set(region.lane_ids) != lane_ids_by_region_id[region.region_id]:
                raise ValueError(
                    f"region/lane membership mismatch for region_id: {region.region_id}"
                )
        for cluster in self.action_clusters:
            if cluster.lane_id not in lane_id_set:
                raise ValueError(f"action cluster references unknown lane_id: {cluster.cluster_id}")
        for surface in self.state_surfaces:
            if surface.lane_id not in lane_id_set:
                raise ValueError(f"state surface references unknown lane_id: {surface.surface_id}")

        if any(
            region_id not in region_id_set
            for region_id in self.evidence_before_commit.required_evidence_region_ids
        ):
            raise ValueError("evidence_before_commit references unknown region_id")
        if any(
            lane_id not in lane_id_set
            for lane_id in self.evidence_before_commit.required_evidence_lane_ids
        ):
            raise ValueError("evidence_before_commit references unknown lane_id")

        glossary = self.evidence_before_commit.same_context_reachability_glossary
        if glossary.reference_surface_family != self.reference_surface_family:
            raise ValueError("evidence_before_commit glossary reference_surface_family mismatch")
        if "provisional_state_surface" not in {
            surface.surface_kind for surface in self.state_surfaces
        }:
            raise ValueError("state_surfaces must include a provisional state surface")
        if "authoritative_state_surface" not in {
            surface.surface_kind for surface in self.state_surfaces
        }:
            raise ValueError("state_surfaces must include an authoritative state surface")
        _assert_v36b_record_reference_instance_binding(
            reference_instance_id=self.reference_instance_id,
            hooks=self.stable_provenance_hooks,
            bindings=self.implementation_observable_bindings,
        )
        return self


class UXAuthoritativeGateSource(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_kind: UXAuthoritativeGateSourceKind
    source_ref: str = Field(min_length=1)


class UXRequestedRuntimeEffect(BaseModel):
    model_config = ConfigDict(extra="forbid")

    effect_kind: UXRequestedRuntimeEffectKind
    descriptive_only: Literal[True] = True


class UXRuntimeVisibleConsequence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    outcome_kind: UXRuntimeVisibleConsequenceKind
    truth_posture: UXRuntimeTruthPosture

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXRuntimeVisibleConsequence":
        if self.truth_posture == "accepted_effect_confirmed":
            return self
        allowed_outcomes_by_truth_posture: dict[str, set[UXRuntimeVisibleConsequenceKind]] = {
            "provisional": {
                "gated_pending_confirmation_visible",
                "provisional_request_visible",
                "status_feedback_visible",
            },
            "request_only": {
                "request_submission_visible",
                "status_feedback_visible",
            },
        }
        if self.outcome_kind in allowed_outcomes_by_truth_posture[self.truth_posture]:
            return self
        raise ValueError(
            "runtime_visible_consequence must remain epistemic and must not overstate success"
        )


class UXInteractionContractEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    interaction_id: str = Field(min_length=1)
    action_cluster_id: str = Field(min_length=1)
    surface_event: UXSurfaceEvent
    ui_transition: SameContextReachableTerm
    preconditions: list[UXInteractionPrecondition]
    user_visible_consequence: UXUserVisibleConsequence
    requested_runtime_effect: UXRequestedRuntimeEffect
    runtime_visible_consequence: UXRuntimeVisibleConsequence
    authoritative: bool = False
    gated: bool = False
    committing: bool = False
    approval_bearing: bool = False
    authoritative_gate_source: UXAuthoritativeGateSource | None = None
    reversible: bool
    confirmation_required: bool
    evidence_required: bool
    rollback_path: UXRollbackPath
    failure_surface: UXFailureSurface
    success_surface: UXSuccessSurface

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXInteractionContractEntry":
        _assert_sorted_unique(
            self.preconditions,
            field_name=f"interaction_entries[{self.interaction_id}].preconditions",
        )
        requires_gate = self.authoritative or self.gated or self.committing or self.approval_bearing
        if requires_gate and self.authoritative_gate_source is None:
            raise ValueError(
                f"interaction entry {self.interaction_id} requires authoritative_gate_source"
            )
        if not requires_gate and self.authoritative_gate_source is not None:
            raise ValueError(
                f"interaction entry {self.interaction_id} must not carry authoritative_gate_source"
            )
        if self.committing and not self.confirmation_required:
            raise ValueError(
                f"interaction entry {self.interaction_id} must require confirmation when committing"
            )
        return self


class UXInteractionContract(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXInteractionContractSchemaVersion = UX_INTERACTION_CONTRACT_SCHEMA
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: UXApprovedProfileId
    supporting_artifacts: UXProjectionInteractionSupportingArtifactRefs = Field(
        default_factory=UXProjectionInteractionSupportingArtifactRefs
    )
    authority_boundary_policy: UXAuthorityBoundaryPolicy = Field(
        default_factory=UXAuthorityBoundaryPolicy
    )
    interaction_entries: list[UXInteractionContractEntry]
    stable_provenance_hooks: list[UXStableProvenanceHook]
    implementation_observable_bindings: list[UXImplementationObservableBinding]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXInteractionContract":
        interaction_ids = [entry.interaction_id for entry in self.interaction_entries]
        _assert_sorted_unique(interaction_ids, field_name="interaction_entries.interaction_id")
        _assert_v36b_record_reference_instance_binding(
            reference_instance_id=self.reference_instance_id,
            hooks=self.stable_provenance_hooks,
            bindings=self.implementation_observable_bindings,
        )
        return self


def canonicalize_ux_surface_projection_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = UXSurfaceProjection.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_interaction_contract_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = UXInteractionContract.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def assert_v36b_projection_interaction_binding(
    *,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
) -> None:
    for field_name in ("reference_surface_family", "reference_instance_id", "approved_profile_id"):
        if getattr(surface_projection, field_name) != getattr(interaction_contract, field_name):
            raise ValueError(f"projection/interaction binding mismatch for {field_name}")
    if surface_projection.supporting_artifacts != interaction_contract.supporting_artifacts:
        raise ValueError("projection/interaction binding mismatch for supporting_artifacts")
    if (
        surface_projection.authority_boundary_policy
        != interaction_contract.authority_boundary_policy
    ):
        raise ValueError("projection/interaction binding mismatch for authority_boundary_policy")


def _assert_minimum_provenance_hook_coverage(
    *, hooks: list[UXStableProvenanceHook], field_name: str
) -> None:
    present = {hook.target_kind for hook in hooks}
    missing = [target for target in FROZEN_V36B_PROVENANCE_HOOK_TARGETS if target not in present]
    if missing:
        raise ValueError(f"{field_name} missing required target kinds: {missing}")


def _assert_minimum_binding_coverage(
    *, bindings: list[UXImplementationObservableBinding], field_name: str
) -> None:
    present = {binding.target_kind for binding in bindings}
    missing = [
        target for target in FROZEN_V36B_IMPLEMENTATION_BINDING_TARGETS if target not in present
    ]
    if missing:
        raise ValueError(f"{field_name} missing required target kinds: {missing}")


def assert_v36b_reference_bundle_consistent(
    *,
    domain_packet: UXDomainPacket,
    morph_ir: UXMorphIR,
    approved_profile_table: V36AFirstFamilyApprovedProfileTable,
    same_context_glossary: V36ASameContextReachabilityGlossary,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
) -> None:
    assert_v36a_reference_bundle_consistent(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        approved_profile_table=approved_profile_table,
        same_context_glossary=same_context_glossary,
    )
    assert_v36b_projection_interaction_binding(
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
    )

    for field_name in ("reference_surface_family", "reference_instance_id", "approved_profile_id"):
        if getattr(surface_projection, field_name) != getattr(domain_packet, field_name):
            raise ValueError(
                f"v36b reference bundle must match released v36a reference pair for {field_name}"
            )
        if getattr(surface_projection, field_name) != getattr(morph_ir, field_name):
            raise ValueError(
                f"v36b reference bundle must match released v36a reference pair for {field_name}"
            )

    if (
        surface_projection.approved_profile_id
        != approved_profile_table.canonical_reference_profile_id
    ):
        raise ValueError("accepted v36b reference pair must use canonical reference profile id")
    approved_profile = approved_profile_for_id(
        approved_profile_table,
        approved_profile_id=surface_projection.approved_profile_id,
    )
    if approved_profile.profile_id != V36A_CANONICAL_REFERENCE_PROFILE_ID:
        raise ValueError("accepted v36b reference pair must use canonical reference profile id")

    if (
        surface_projection.evidence_before_commit.same_context_reachability_glossary
        != same_context_glossary
    ):
        raise ValueError(
            "projection must consume the released v36a same-context glossary without shadowing"
        )

    projection_cluster_ids = {cluster.cluster_id for cluster in surface_projection.action_clusters}
    for entry in interaction_contract.interaction_entries:
        if entry.action_cluster_id not in projection_cluster_ids:
            raise ValueError(
                "interaction entry references unknown projection action cluster: "
                f"{entry.action_cluster_id}"
            )

    combined_hooks = (
        surface_projection.stable_provenance_hooks + interaction_contract.stable_provenance_hooks
    )
    _assert_minimum_provenance_hook_coverage(
        hooks=combined_hooks,
        field_name="stable_provenance_hooks",
    )
    combined_bindings = (
        surface_projection.implementation_observable_bindings
        + interaction_contract.implementation_observable_bindings
    )
    _assert_minimum_binding_coverage(
        bindings=combined_bindings,
        field_name="implementation_observable_bindings",
    )


UXMorphDiagnosticsSchemaVersion = Literal["ux_morph_diagnostics@1"]
UXConformanceReportSchemaVersion = Literal["ux_conformance_report@1"]
UXDiagnosticSeverity = Literal["error", "warning", "advisory"]
UXConformanceOverallJudgment = Literal["pass", "fail", "needs_review"]
UXConformanceImpact = Literal["advisory_only", "blocks_pass", "needs_review"]
UXDiagnosticViolationFamily = Literal[
    "advisory_authoritative_boundary_visually_collapsed",
    "competing_primary_actions_in_one_region",
    "destructive_action_lacks_adequate_confirmation",
    "failure_mode_lacks_visible_recovery_path",
    "provisional_data_rendered_with_authoritative_styling",
    "requested_interaction_profile_conflicts_with_realized_command_grammar",
    "required_evidence_not_reachable_within_same_bounded_workbench_context",
    "utility_target_conflicts_with_density_or_information_posture",
]
UXRenderedSurfaceAssertionInputSchema = Literal[
    "v36c_rendered_reference_surface_binding_manifest@1",
    "v36c_rendered_reference_surface_contract@1",
    "v36c_rendered_reference_surface_semantic_snapshot@1",
]
UXCanonicalArtifactSchema = Literal[
    "ux_domain_packet@1",
    "ux_interaction_contract@1",
    "ux_morph_ir@1",
    "ux_surface_projection@1",
    "v36c_artifact_inspector_reference_surface_evidence@1",
    "v36c_rendered_reference_surface_binding_manifest@1",
    "v36c_rendered_reference_surface_contract@1",
    "v36c_rendered_reference_surface_semantic_snapshot@1",
]

UX_MORPH_DIAGNOSTICS_SCHEMA = "ux_morph_diagnostics@1"
UX_CONFORMANCE_REPORT_SCHEMA = "ux_conformance_report@1"
V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_SCHEMA = "v36c_rendered_reference_surface_contract@1"
V36C_RENDERED_REFERENCE_SURFACE_SNAPSHOT_SCHEMA = (
    "v36c_rendered_reference_surface_semantic_snapshot@1"
)
V36C_RENDERED_REFERENCE_SURFACE_BINDING_MANIFEST_SCHEMA = (
    "v36c_rendered_reference_surface_binding_manifest@1"
)
V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_EVIDENCE_SCHEMA = (
    "v36c_artifact_inspector_reference_surface_evidence@1"
)
FROZEN_V36D_DIAGNOSTICS_SEVERITY_TAXONOMY: tuple[UXDiagnosticSeverity, ...] = (
    "error",
    "warning",
    "advisory",
)
FROZEN_V36D_SEEDED_VIOLATION_FAMILIES: tuple[UXDiagnosticViolationFamily, ...] = (
    "advisory_authoritative_boundary_visually_collapsed",
    "competing_primary_actions_in_one_region",
    "destructive_action_lacks_adequate_confirmation",
    "failure_mode_lacks_visible_recovery_path",
    "provisional_data_rendered_with_authoritative_styling",
    "requested_interaction_profile_conflicts_with_realized_command_grammar",
    "required_evidence_not_reachable_within_same_bounded_workbench_context",
    "utility_target_conflicts_with_density_or_information_posture",
)
FROZEN_V36D_RENDERED_SURFACE_ASSERTION_INPUTS: tuple[UXRenderedSurfaceAssertionInputSchema, ...] = (
    "v36c_rendered_reference_surface_binding_manifest@1",
    "v36c_rendered_reference_surface_contract@1",
    "v36c_rendered_reference_surface_semantic_snapshot@1",
)
FROZEN_V36D_ALLOWED_EVIDENCE_REF_PREFIXES: tuple[str, ...] = (
    "apps/api/fixtures/ux_governance/",
    "artifacts/agent_harness/v63/evidence_inputs/",
    "packages/adeu_core_ir/schema/",
    "spec/",
)


def _assert_repo_relative_artifact_ref(ref: str, *, field_name: str) -> None:
    if not ref:
        raise ValueError(f"{field_name} must not be empty")
    if ref.startswith("/"):
        raise ValueError(f"{field_name} must be repo-relative")
    path = ref.split("#", 1)[0]
    parts = path.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise ValueError(f"{field_name} contains invalid path components")


def _assert_canonical_supporting_evidence_refs(refs: list[str], *, field_name: str) -> None:
    _assert_sorted_unique(refs, field_name=field_name)
    for ref in refs:
        _assert_repo_relative_artifact_ref(ref, field_name=field_name)
        if "urm_events.ndjson" in ref or "worker" in ref:
            raise ValueError(
                f"{field_name} must not treat event streams or worker prose "
                "as authoritative grounds"
            )
        if not any(ref.startswith(prefix) for prefix in FROZEN_V36D_ALLOWED_EVIDENCE_REF_PREFIXES):
            raise ValueError(f"{field_name} must resolve to the frozen canonical artifact stack")


def _expected_conformance_impact(*, severity: UXDiagnosticSeverity) -> UXConformanceImpact:
    if severity == "error":
        return "blocks_pass"
    if severity == "warning":
        return "needs_review"
    return "advisory_only"


def derive_v36d_overall_judgment(
    findings: list["UXMorphDiagnosticFinding"],
) -> UXConformanceOverallJudgment:
    severities = {finding.severity for finding in findings}
    if "error" in severities:
        return "fail"
    if "warning" in severities:
        return "needs_review"
    return "pass"


class UXMorphDiagnosticsSupportingArtifactRefs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    ux_domain_packet_schema: UXDomainPacketSchemaVersion = UX_DOMAIN_PACKET_SCHEMA
    ux_morph_ir_schema: UXMorphIRSchemaVersion = UX_MORPH_IR_SCHEMA
    ux_surface_projection_schema: UXSurfaceProjectionSchemaVersion = UX_SURFACE_PROJECTION_SCHEMA
    ux_interaction_contract_schema: UXInteractionContractSchemaVersion = (
        UX_INTERACTION_CONTRACT_SCHEMA
    )
    rendered_reference_surface_contract_schema: Literal[
        "v36c_rendered_reference_surface_contract@1"
    ] = V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_SCHEMA
    rendered_reference_surface_snapshot_schema: Literal[
        "v36c_rendered_reference_surface_semantic_snapshot@1"
    ] = V36C_RENDERED_REFERENCE_SURFACE_SNAPSHOT_SCHEMA
    rendered_reference_surface_binding_manifest_schema: Literal[
        "v36c_rendered_reference_surface_binding_manifest@1"
    ] = V36C_RENDERED_REFERENCE_SURFACE_BINDING_MANIFEST_SCHEMA
    rendered_reference_surface_evidence_schema: Literal[
        "v36c_artifact_inspector_reference_surface_evidence@1"
    ] = V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_EVIDENCE_SCHEMA


class UXDiagnosticProvenancePointer(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_schema: UXCanonicalArtifactSchema
    source_path: str = Field(min_length=1)
    target_ref: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXDiagnosticProvenancePointer":
        _assert_repo_relative_artifact_ref(
            self.source_path, field_name="provenance_pointers.source_path"
        )
        return self


class UXMorphDiagnosticFinding(BaseModel):
    model_config = ConfigDict(extra="forbid")

    finding_id: str = Field(min_length=1)
    violation_family: UXDiagnosticViolationFamily
    severity: UXDiagnosticSeverity
    provenance_pointers: list[UXDiagnosticProvenancePointer] = Field(min_length=1)
    rendered_surface_assertion_inputs_used: list[UXRenderedSurfaceAssertionInputSchema] = Field(
        min_length=1
    )
    supporting_evidence_refs: list[str] = Field(min_length=1)
    conformance_impact: UXConformanceImpact

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXMorphDiagnosticFinding":
        _assert_sorted_unique(
            self.rendered_surface_assertion_inputs_used,
            field_name=f"findings[{self.finding_id}].rendered_surface_assertion_inputs_used",
        )
        _assert_canonical_supporting_evidence_refs(
            self.supporting_evidence_refs,
            field_name=f"findings[{self.finding_id}].supporting_evidence_refs",
        )
        expected_impact = _expected_conformance_impact(severity=self.severity)
        if self.conformance_impact != expected_impact:
            raise ValueError(
                f"finding {self.finding_id} must use conformance_impact {expected_impact!r}"
            )
        return self


class UXMorphDiagnostics(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXMorphDiagnosticsSchemaVersion = UX_MORPH_DIAGNOSTICS_SCHEMA
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: UXApprovedProfileId
    supporting_artifacts: UXMorphDiagnosticsSupportingArtifactRefs = Field(
        default_factory=UXMorphDiagnosticsSupportingArtifactRefs
    )
    authority_boundary_policy: UXAuthorityBoundaryPolicy = Field(
        default_factory=UXAuthorityBoundaryPolicy
    )
    severity_taxonomy: list[UXDiagnosticSeverity]
    seeded_violation_families: list[UXDiagnosticViolationFamily]
    findings: list[UXMorphDiagnosticFinding]

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXMorphDiagnostics":
        _assert_exact_sequence(
            self.severity_taxonomy,
            expected=FROZEN_V36D_DIAGNOSTICS_SEVERITY_TAXONOMY,
            field_name="severity_taxonomy",
        )
        _assert_exact_sequence(
            self.seeded_violation_families,
            expected=FROZEN_V36D_SEEDED_VIOLATION_FAMILIES,
            field_name="seeded_violation_families",
        )
        finding_ids = [finding.finding_id for finding in self.findings]
        _assert_sorted_distinct(finding_ids, field_name="findings.finding_id")
        return self


class UXDiagnosticSeverityCounts(BaseModel):
    model_config = ConfigDict(extra="forbid")

    error: int = Field(ge=0)
    warning: int = Field(ge=0)
    advisory: int = Field(ge=0)


class UXConformanceAggregationRule(BaseModel):
    model_config = ConfigDict(extra="forbid")

    any_error: Literal["fail"] = "fail"
    no_error_and_any_warning: Literal["needs_review"] = "needs_review"
    only_advisory_or_no_findings: Literal["pass"] = "pass"


class UXConformanceDerivationMetadata(BaseModel):
    model_config = ConfigDict(extra="forbid")

    diagnostics_schema: UXMorphDiagnosticsSchemaVersion = UX_MORPH_DIAGNOSTICS_SCHEMA
    rendered_surface_assertion_inputs: list[UXRenderedSurfaceAssertionInputSchema]
    rendered_reference_surface_evidence_schema: Literal[
        "v36c_artifact_inspector_reference_surface_evidence@1"
    ] = V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_EVIDENCE_SCHEMA
    aggregation_rule: UXConformanceAggregationRule = Field(
        default_factory=UXConformanceAggregationRule
    )
    typed_summary_only: Literal[True] = True
    fresh_route_local_heuristics_introduced: Literal[False] = False
    canonical_artifact_truth_only: Literal[True] = True
    event_streams_and_worker_prose_provenance_only: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXConformanceDerivationMetadata":
        _assert_exact_sequence(
            self.rendered_surface_assertion_inputs,
            expected=FROZEN_V36D_RENDERED_SURFACE_ASSERTION_INPUTS,
            field_name="derivation_metadata.rendered_surface_assertion_inputs",
        )
        return self


class UXConformanceReportSupportingArtifactRefs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    ux_morph_diagnostics_schema: UXMorphDiagnosticsSchemaVersion = UX_MORPH_DIAGNOSTICS_SCHEMA
    rendered_reference_surface_contract_schema: Literal[
        "v36c_rendered_reference_surface_contract@1"
    ] = V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_SCHEMA
    rendered_reference_surface_snapshot_schema: Literal[
        "v36c_rendered_reference_surface_semantic_snapshot@1"
    ] = V36C_RENDERED_REFERENCE_SURFACE_SNAPSHOT_SCHEMA
    rendered_reference_surface_binding_manifest_schema: Literal[
        "v36c_rendered_reference_surface_binding_manifest@1"
    ] = V36C_RENDERED_REFERENCE_SURFACE_BINDING_MANIFEST_SCHEMA
    rendered_reference_surface_evidence_schema: Literal[
        "v36c_artifact_inspector_reference_surface_evidence@1"
    ] = V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_EVIDENCE_SCHEMA


class UXConformanceReport(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXConformanceReportSchemaVersion = UX_CONFORMANCE_REPORT_SCHEMA
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: UXApprovedProfileId
    supporting_artifacts: UXConformanceReportSupportingArtifactRefs = Field(
        default_factory=UXConformanceReportSupportingArtifactRefs
    )
    authority_boundary_policy: UXAuthorityBoundaryPolicy = Field(
        default_factory=UXAuthorityBoundaryPolicy
    )
    overall_judgment: UXConformanceOverallJudgment
    supporting_finding_ids: list[str]
    severity_counts: UXDiagnosticSeverityCounts
    failed_rule_families: list[UXDiagnosticViolationFamily]
    warning_rule_families: list[UXDiagnosticViolationFamily]
    derivation_metadata: UXConformanceDerivationMetadata

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXConformanceReport":
        _assert_sorted_distinct(
            self.supporting_finding_ids,
            field_name="supporting_finding_ids",
        )
        _assert_sorted_distinct(
            self.failed_rule_families,
            field_name="failed_rule_families",
        )
        _assert_sorted_distinct(
            self.warning_rule_families,
            field_name="warning_rule_families",
        )
        return self


def canonicalize_ux_morph_diagnostics_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = UXMorphDiagnostics.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_conformance_report_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = UXConformanceReport.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def _build_v36d_severity_counts(
    findings: list[UXMorphDiagnosticFinding],
) -> UXDiagnosticSeverityCounts:
    return UXDiagnosticSeverityCounts(
        error=sum(1 for finding in findings if finding.severity == "error"),
        warning=sum(1 for finding in findings if finding.severity == "warning"),
        advisory=sum(1 for finding in findings if finding.severity == "advisory"),
    )


def _rendered_surface_target_ref_set(rendered_binding_manifest: dict[str, Any]) -> set[str]:
    target_manifest = rendered_binding_manifest.get("target_manifest")
    if not isinstance(target_manifest, list):
        raise ValueError("rendered surface binding manifest must contain target_manifest")
    refs: set[str] = set()
    for entry in target_manifest:
        if not isinstance(entry, dict):
            raise ValueError(
                "rendered surface binding manifest target_manifest entries must be objects"
            )
        target_ref = entry.get("target_ref")
        if not isinstance(target_ref, str) or not target_ref:
            raise ValueError("rendered surface binding manifest target_ref must be non-empty")
        refs.add(target_ref)
    return refs


def _assert_v36d_rendered_surface_inputs_consistent(
    *,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
    same_context_glossary: V36ASameContextReachabilityGlossary,
    rendered_surface_contract: dict[str, Any],
    rendered_surface_snapshot: dict[str, Any],
    rendered_surface_binding_manifest: dict[str, Any],
    rendered_reference_surface_evidence: dict[str, Any],
) -> None:
    expected_route_id = "artifact_inspector_reference_surface"
    expected_route_path = "/artifact-inspector"
    expected_contract_schema = V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_SCHEMA
    expected_snapshot_schema = V36C_RENDERED_REFERENCE_SURFACE_SNAPSHOT_SCHEMA
    expected_binding_manifest_schema = V36C_RENDERED_REFERENCE_SURFACE_BINDING_MANIFEST_SCHEMA
    expected_evidence_schema = V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_EVIDENCE_SCHEMA

    if rendered_surface_contract.get("schema") != expected_contract_schema:
        raise ValueError("rendered_surface_contract must use the released v36c schema")
    if rendered_surface_snapshot.get("schema") != expected_snapshot_schema:
        raise ValueError("rendered_surface_snapshot must use the released v36c schema")
    if rendered_surface_binding_manifest.get("schema") != expected_binding_manifest_schema:
        raise ValueError("rendered_surface_binding_manifest must use the released v36c schema")
    if rendered_reference_surface_evidence.get("schema") != expected_evidence_schema:
        raise ValueError("rendered_reference_surface_evidence must use the released v36c schema")

    for field_name in ("reference_surface_family", "reference_instance_id", "approved_profile_id"):
        expected = getattr(surface_projection, field_name)
        if rendered_surface_contract.get(field_name) != expected:
            raise ValueError(f"rendered_surface_contract mismatch for {field_name}")
        if rendered_surface_snapshot.get(field_name) != expected:
            raise ValueError(f"rendered_surface_snapshot mismatch for {field_name}")
        if rendered_surface_binding_manifest.get(field_name) != expected:
            raise ValueError(f"rendered_surface_binding_manifest mismatch for {field_name}")
    if rendered_surface_contract.get("route_id") != expected_route_id:
        raise ValueError("rendered_surface_contract route_id mismatch")
    if rendered_surface_snapshot.get("route_id") != expected_route_id:
        raise ValueError("rendered_surface_snapshot route_id mismatch")
    if rendered_surface_binding_manifest.get("route_id") != expected_route_id:
        raise ValueError("rendered_surface_binding_manifest route_id mismatch")
    if rendered_reference_surface_evidence.get("rendered_surface_route_id") != expected_route_id:
        raise ValueError("rendered_reference_surface_evidence route_id mismatch")
    if rendered_surface_contract.get("route_path") != expected_route_path:
        raise ValueError("rendered_surface_contract route_path mismatch")
    if rendered_surface_snapshot.get("route_path") != expected_route_path:
        raise ValueError("rendered_surface_snapshot route_path mismatch")
    if rendered_surface_binding_manifest.get("route_path") != expected_route_path:
        raise ValueError("rendered_surface_binding_manifest route_path mismatch")
    if (
        rendered_reference_surface_evidence.get("rendered_surface_route_path")
        != expected_route_path
    ):
        raise ValueError("rendered_reference_surface_evidence route_path mismatch")
    if (
        rendered_surface_contract.get("diagnostics_lane_mode")
        != "placeholder_or_existing_artifact_backed_read_only_only"
    ):
        raise ValueError(
            "rendered surface diagnostics lane must remain the released v63 placeholder"
        )
    if rendered_surface_contract.get("truth_source_policy") != "accepted_v36_artifacts_only":
        raise ValueError("rendered surface truth source policy mismatch")
    if rendered_surface_contract.get("route_payload_parity_mode") != (
        "presentational_transform_only_no_authority_or_reachability_meaning_drift"
    ):
        raise ValueError("rendered surface parity mode mismatch")
    if rendered_surface_snapshot.get(
        "same_context_reachability_glossary"
    ) != same_context_glossary.model_dump(
        mode="json",
        exclude_none=True,
    ):
        raise ValueError(
            "rendered surface snapshot must consume the released same-context glossary"
        )

    rendered_target_refs = _rendered_surface_target_ref_set(rendered_surface_binding_manifest)
    projection_target_refs = (
        {hook.target_ref for hook in surface_projection.stable_provenance_hooks}
        | {binding.target_ref for binding in surface_projection.implementation_observable_bindings}
        | {hook.target_ref for hook in interaction_contract.stable_provenance_hooks}
        | {
            binding.target_ref
            for binding in interaction_contract.implementation_observable_bindings
        }
    )
    if not projection_target_refs.issubset(rendered_target_refs):
        raise ValueError("rendered surface binding manifest must expose the released v36b targets")


def assert_v36d_reference_bundle_consistent(
    *,
    domain_packet: UXDomainPacket,
    morph_ir: UXMorphIR,
    approved_profile_table: V36AFirstFamilyApprovedProfileTable,
    same_context_glossary: V36ASameContextReachabilityGlossary,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
    rendered_surface_contract: dict[str, Any],
    rendered_surface_snapshot: dict[str, Any],
    rendered_surface_binding_manifest: dict[str, Any],
    rendered_reference_surface_evidence: dict[str, Any],
    diagnostics: UXMorphDiagnostics,
    conformance_report: UXConformanceReport,
) -> None:
    assert_v36b_reference_bundle_consistent(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        approved_profile_table=approved_profile_table,
        same_context_glossary=same_context_glossary,
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
    )
    _assert_v36d_rendered_surface_inputs_consistent(
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
        same_context_glossary=same_context_glossary,
        rendered_surface_contract=rendered_surface_contract,
        rendered_surface_snapshot=rendered_surface_snapshot,
        rendered_surface_binding_manifest=rendered_surface_binding_manifest,
        rendered_reference_surface_evidence=rendered_reference_surface_evidence,
    )

    for field_name in ("reference_surface_family", "reference_instance_id", "approved_profile_id"):
        expected = getattr(domain_packet, field_name)
        if getattr(diagnostics, field_name) != expected:
            raise ValueError(f"diagnostics bundle mismatch for {field_name}")
        if getattr(conformance_report, field_name) != expected:
            raise ValueError(f"conformance report mismatch for {field_name}")

    approved_profile = approved_profile_for_id(
        approved_profile_table,
        approved_profile_id=diagnostics.approved_profile_id,
    )
    if approved_profile.profile_id != V36A_CANONICAL_REFERENCE_PROFILE_ID:
        raise ValueError("accepted v36d reference bundle must use canonical reference profile id")

    derived_supporting_finding_ids = [finding.finding_id for finding in diagnostics.findings]
    if conformance_report.supporting_finding_ids != derived_supporting_finding_ids:
        raise ValueError("conformance report must be derived from the diagnostics finding ids")

    expected_judgment = derive_v36d_overall_judgment(diagnostics.findings)
    if conformance_report.overall_judgment != expected_judgment:
        raise ValueError(
            "conformance report overall judgment must follow the frozen aggregation rule"
        )

    expected_counts = _build_v36d_severity_counts(diagnostics.findings)
    if conformance_report.severity_counts != expected_counts:
        raise ValueError("conformance report severity_counts must be derived from diagnostics")

    expected_failed_rule_families = sorted(
        {
            finding.violation_family
            for finding in diagnostics.findings
            if finding.severity == "error"
        }
    )
    if conformance_report.failed_rule_families != expected_failed_rule_families:
        raise ValueError("failed_rule_families must be derived from error findings")

    expected_warning_rule_families = sorted(
        {
            finding.violation_family
            for finding in diagnostics.findings
            if finding.severity == "warning"
        }
    )
    if conformance_report.warning_rule_families != expected_warning_rule_families:
        raise ValueError("warning_rule_families must be derived from warning findings")

    rendered_surface_schemas_used = set(FROZEN_V36D_RENDERED_SURFACE_ASSERTION_INPUTS)
    for finding in diagnostics.findings:
        if not set(finding.rendered_surface_assertion_inputs_used).issubset(
            rendered_surface_schemas_used
        ):
            raise ValueError(
                f"finding {finding.finding_id} must use only the frozen "
                "rendered-surface assertion inputs"
            )
        if (
            finding.violation_family
            == "requested_interaction_profile_conflicts_with_realized_command_grammar"
            and diagnostics.approved_profile_id
            != approved_profile_table.canonical_reference_profile_id
        ):
            raise ValueError(
                "requested profile/command grammar conflicts must bind to "
                "the frozen approved profile contract"
            )
