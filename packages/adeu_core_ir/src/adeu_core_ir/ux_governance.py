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
    context_pairs = {
        "primary_user_archetype": morph_ir.context.primary_user_archetype,
        "device_class": morph_ir.context.device_class,
        "risk_level": morph_ir.context.risk_level,
        "trust_sensitivity": morph_ir.context.trust_sensitivity,
        "interaction_mode": morph_ir.context.interaction_mode,
    }
    for field_name, value in context_pairs.items():
        if getattr(domain_packet, field_name) != value:
            raise ValueError(f"reference instance binding mismatch for {field_name}")


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
