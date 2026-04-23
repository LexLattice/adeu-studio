from __future__ import annotations

import hashlib
import json
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, model_validator

from .ux_governance import (
    V36A_REFERENCE_SURFACE_FAMILY,
    SameContextReachableTerm,
    UXApprovedProfileId,
    UXInteractionContract,
    UXReferenceSurfaceFamily,
    UXSurfaceProjection,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    approved_profile_for_id,
)

UXErgonomicRuleAuthorityStackSchemaVersion = Literal["ux_ergonomic_rule_authority_stack@1"]
UXComponentErgonomicRegistrySchemaVersion = Literal["ux_component_ergonomic_registry@1"]
UXComponentVisibilityContractSchemaVersion = Literal["ux_component_visibility_contract@1"]
UXErgonomicCandidateProjectionProfileTableSchemaVersion = Literal[
    "ux_ergonomic_candidate_projection_profile_table@1"
]
UXErgonomicCaseEnvelopeSchemaVersion = Literal["ux_ergonomic_case_envelope@1"]
UXErgonomicAdjudicationRequestSchemaVersion = Literal["ux_ergonomic_adjudication_request@1"]
UXErgonomicAdjudicationResultSchemaVersion = Literal["ux_ergonomic_adjudication_result@1"]
UXErgonomicRuntimeMeasurementEvidenceSchemaVersion = Literal[
    "ux_ergonomic_runtime_measurement_evidence@1"
]
UXErgonomicRuntimeBridgeReportSchemaVersion = Literal["ux_ergonomic_runtime_bridge_report@1"]

UXErgonomicAuthorityLayer = Literal[
    "constitutional_surface_invariant",
    "repo_local_policy",
    "external_standard_floor",
    "platform_preset",
    "user_declared_preference",
    "heuristic_utility",
]
UXErgonomicRuleForce = Literal["hard_block", "hard_floor", "advisory_ranking"]
UXErgonomicProvenanceState = Literal[
    "measured_runtime",
    "declared_case",
    "declared_user_profile",
    "verified_device_inventory",
    "inferred_heuristic",
    "unknown",
]
UXErgonomicAdmissibility = Literal[
    "none",
    "css_geometry_admissible",
    "planning_declared_css_geometry",
    "physical_size_admissible",
    "visual_angle_admissible",
    "runtime_conformance_admissible",
]
UXErgonomicPreferenceTier = Literal[
    "blocked",
    "discouraged",
    "marginal",
    "acceptable",
    "preferred",
]
UXErgonomicOverallJudgment = Literal["pass", "needs_review", "fail"]
UXErgonomicReportStatus = Literal[
    "valid",
    "invalid_request_basis_mismatch",
    "invalid_candidate_table_basis_mismatch",
    "invalid_visibility_contract_basis_mismatch",
    "invalid_case_envelope_admissibility",
    "invalid_unknown_candidate_ref",
]
UXErgonomicClassId = Literal[
    "erg_action_lane_container",
    "erg_work_context_lane",
    "erg_source_text_lane",
    "erg_evidence_lane",
    "erg_diagnostics_lane",
    "erg_status_surface",
    "erg_trust_boundary_surface",
    "erg_navigation_lane",
    "erg_advisory_action_cluster",
    "erg_comparison_action_cluster",
    "erg_commit_gate_action_cluster",
]
UXErgonomicSourceSemanticKind = Literal[
    "action_lane",
    "work_context_lane",
    "source_lane",
    "evidence_lane",
    "diagnostics_lane",
    "status_lane",
    "trust_boundary_lane",
    "navigation_lane",
    "advisory_action_cluster",
    "comparison_action_cluster",
    "commit_action_cluster",
]
UXErgonomicSurfaceUnit = Literal["lane", "action_cluster"]
UXErgonomicVisibilityState = Literal[
    "continuously_visible",
    "same_context_reachable",
    "gated_and_visible",
]
UXErgonomicCollapsePolicy = Literal[
    "never_collapse",
    "may_stack_same_context",
    "may_buffer_same_context",
    "may_progressively_disclose_same_context",
]
UXErgonomicRequirement = Literal["required", "not_required"]
UXErgonomicTaxonomyStatus = Literal["starter_frozen"]
UXErgonomicWindowOccupancyMode = Literal[
    "maximized_split_reference",
    "half_screen_split_reference",
    "narrow_stacked_same_context",
    "quarter_screen_inspector_safe_buffered",
]
UXErgonomicInputMode = Literal["mouse_fine", "touch_coarse", "hybrid", "pen"]
UXErgonomicTaskPosture = Literal[
    "compare_candidate_variant",
    "inspect_evidence_before_commit",
    "source_review",
]
UXErgonomicMeasurementSourceKind = Literal[
    "playwright_replay",
    "declared_fixture",
    "device_inventory",
    "user_profile",
    "heuristic_inference",
]
UXErgonomicMeasurementUnit = Literal["css_px", "ratio", "ppi", "mm"]
UXErgonomicObservedVisibilityState = Literal[
    "continuously_visible",
    "same_context_reachable",
    "gated_and_visible",
    "not_observed",
]
UXErgonomicObservedRevealTransition = SameContextReachableTerm | Literal[
    "unexpected_route_transition"
]
UXErgonomicCandidateProfileId = Literal[
    "artifact_inspector_maximized_split_reference",
    "artifact_inspector_half_screen_split_reference",
    "artifact_inspector_narrow_stacked_same_context",
    "artifact_inspector_quarter_screen_inspector_safe_buffered",
]
UXErgonomicComponentRefPrefix = Literal["lane", "action_cluster"]
UXErgonomicMeasurementObligationKind = Literal[
    "runtime_targetability_measurement",
    "runtime_text_measurement",
    "runtime_visibility_measurement",
]
UXErgonomicObligationSeverity = Literal["pass", "needs_review"]
UXErgonomicAmbiguitySeverity = Literal["advisory", "warning"]
UXErgonomicRuntimeBridgeStatus = Literal[
    "advisory_clean",
    "advisory_drift_detected",
    "advisory_incomplete_missing_evidence",
    "invalid_basis_mismatch",
    "invalid_runtime_evidence_shape",
]
UXErgonomicRuntimeMismatchFamily = Literal[
    "runtime_source_hash_mismatch",
    "runtime_missing_measurement_for_required_obligation",
    "runtime_measurement_provenance_inadmissible",
    "runtime_candidate_profile_not_realized",
    "runtime_targetability_below_adjudicated_floor",
    "runtime_text_floor_below_adjudicated_floor",
    "runtime_visibility_drift_from_adjudicated_claim",
    "runtime_same_context_reveal_drift",
    "runtime_required_evidence_not_observed",
    "runtime_trust_boundary_not_observed",
    "runtime_commit_gate_not_observed_or_not_targetable",
    "runtime_unexpected_route_transition",
    "runtime_unknown_component_ref",
]

UX_ERGONOMIC_RULE_AUTHORITY_STACK_SCHEMA = "ux_ergonomic_rule_authority_stack@1"
UX_COMPONENT_ERGONOMIC_REGISTRY_SCHEMA = "ux_component_ergonomic_registry@1"
UX_COMPONENT_VISIBILITY_CONTRACT_SCHEMA = "ux_component_visibility_contract@1"
UX_ERGONOMIC_CANDIDATE_PROJECTION_PROFILE_TABLE_SCHEMA = (
    "ux_ergonomic_candidate_projection_profile_table@1"
)
UX_ERGONOMIC_CASE_ENVELOPE_SCHEMA = "ux_ergonomic_case_envelope@1"
UX_ERGONOMIC_ADJUDICATION_REQUEST_SCHEMA = "ux_ergonomic_adjudication_request@1"
UX_ERGONOMIC_ADJUDICATION_RESULT_SCHEMA = "ux_ergonomic_adjudication_result@1"
UX_ERGONOMIC_RUNTIME_MEASUREMENT_EVIDENCE_SCHEMA = (
    "ux_ergonomic_runtime_measurement_evidence@1"
)
UX_ERGONOMIC_RUNTIME_BRIDGE_REPORT_SCHEMA = "ux_ergonomic_runtime_bridge_report@1"

FROZEN_V67A_ALLOWED_SOURCE_ARTIFACT_REF_PREFIXES: tuple[str, ...] = (
    "apps/api/fixtures/ux_governance/",
)
FROZEN_V67C_ALLOWED_SOURCE_ARTIFACT_REF_PREFIXES: tuple[str, ...] = (
    "apps/api/fixtures/ux_governance/",
    "apps/api/fixtures/ux_ergonomics/",
)
FROZEN_V67A_CLASS_IDS: tuple[UXErgonomicClassId, ...] = (
    "erg_action_lane_container",
    "erg_work_context_lane",
    "erg_source_text_lane",
    "erg_evidence_lane",
    "erg_diagnostics_lane",
    "erg_status_surface",
    "erg_trust_boundary_surface",
    "erg_navigation_lane",
    "erg_advisory_action_cluster",
    "erg_comparison_action_cluster",
    "erg_commit_gate_action_cluster",
)
FROZEN_V67A_CLASS_SEMANTIC_KIND: dict[UXErgonomicClassId, UXErgonomicSourceSemanticKind] = {
    "erg_action_lane_container": "action_lane",
    "erg_work_context_lane": "work_context_lane",
    "erg_source_text_lane": "source_lane",
    "erg_evidence_lane": "evidence_lane",
    "erg_diagnostics_lane": "diagnostics_lane",
    "erg_status_surface": "status_lane",
    "erg_trust_boundary_surface": "trust_boundary_lane",
    "erg_navigation_lane": "navigation_lane",
    "erg_advisory_action_cluster": "advisory_action_cluster",
    "erg_comparison_action_cluster": "comparison_action_cluster",
    "erg_commit_gate_action_cluster": "commit_action_cluster",
}
FROZEN_V67A_CLASS_SURFACE_UNIT: dict[UXErgonomicClassId, UXErgonomicSurfaceUnit] = {
    "erg_action_lane_container": "lane",
    "erg_work_context_lane": "lane",
    "erg_source_text_lane": "lane",
    "erg_evidence_lane": "lane",
    "erg_diagnostics_lane": "lane",
    "erg_status_surface": "lane",
    "erg_trust_boundary_surface": "lane",
    "erg_navigation_lane": "lane",
    "erg_advisory_action_cluster": "action_cluster",
    "erg_comparison_action_cluster": "action_cluster",
    "erg_commit_gate_action_cluster": "action_cluster",
}
FROZEN_V67A_COMPONENT_REF_SEQUENCE: tuple[str, ...] = (
    "lane:action-lane",
    "lane:work-context-lane",
    "lane:source-lane",
    "lane:evidence-lane",
    "lane:diagnostics-lane",
    "lane:status-lane",
    "lane:trust-boundary-lane",
    "lane:navigation-lane",
    "action_cluster:advisory-actions",
    "action_cluster:comparison-actions",
    "action_cluster:commit-actions",
)
FROZEN_V67A_COMPONENT_REF_TO_CLASS_ID: dict[str, UXErgonomicClassId] = {
    "lane:action-lane": "erg_action_lane_container",
    "lane:work-context-lane": "erg_work_context_lane",
    "lane:source-lane": "erg_source_text_lane",
    "lane:evidence-lane": "erg_evidence_lane",
    "lane:diagnostics-lane": "erg_diagnostics_lane",
    "lane:status-lane": "erg_status_surface",
    "lane:trust-boundary-lane": "erg_trust_boundary_surface",
    "lane:navigation-lane": "erg_navigation_lane",
    "action_cluster:advisory-actions": "erg_advisory_action_cluster",
    "action_cluster:comparison-actions": "erg_comparison_action_cluster",
    "action_cluster:commit-actions": "erg_commit_gate_action_cluster",
}
FROZEN_V67A_CANDIDATE_PROFILE_IDS: tuple[UXErgonomicCandidateProfileId, ...] = (
    "artifact_inspector_maximized_split_reference",
    "artifact_inspector_half_screen_split_reference",
    "artifact_inspector_narrow_stacked_same_context",
    "artifact_inspector_quarter_screen_inspector_safe_buffered",
)
FROZEN_V67A_CANDIDATE_PROFILE_APPROVED_PROFILE: dict[
    UXErgonomicCandidateProfileId, UXApprovedProfileId
] = {
    "artifact_inspector_maximized_split_reference": "artifact_inspector_reference",
    "artifact_inspector_half_screen_split_reference": "artifact_inspector_reference",
    "artifact_inspector_narrow_stacked_same_context": "artifact_inspector_alternate",
    "artifact_inspector_quarter_screen_inspector_safe_buffered": "artifact_inspector_alternate",
}
FROZEN_V67A_CANDIDATE_PROFILE_TARGET_ENVELOPE: dict[
    UXErgonomicCandidateProfileId, UXErgonomicWindowOccupancyMode
] = {
    "artifact_inspector_maximized_split_reference": "maximized_split_reference",
    "artifact_inspector_half_screen_split_reference": "half_screen_split_reference",
    "artifact_inspector_narrow_stacked_same_context": "narrow_stacked_same_context",
    "artifact_inspector_quarter_screen_inspector_safe_buffered": (
        "quarter_screen_inspector_safe_buffered"
    ),
}
FROZEN_V67A_REQUIRED_ACTION_IDS: tuple[str, ...] = (
    "open-commit-review",
    "run-advisory-action",
    "submit-commit-request",
)
FROZEN_V67A_REQUIRED_EVIDENCE_COMPONENT_REFS: tuple[str, ...] = (
    "lane:evidence-lane",
    "lane:status-lane",
    "lane:trust-boundary-lane",
    "action_cluster:commit-actions",
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


def _assert_repo_relative_artifact_ref(ref: str, *, field_name: str) -> None:
    if not ref:
        raise ValueError(f"{field_name} must not be empty")
    if ref.startswith("/"):
        raise ValueError(f"{field_name} must be repo-relative")
    path = ref.split("#", 1)[0]
    parts = path.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise ValueError(f"{field_name} contains invalid path components")


def _assert_v67a_source_artifact_ref(ref: str, *, field_name: str) -> None:
    _assert_repo_relative_artifact_ref(ref, field_name=field_name)
    if not any(
        ref.startswith(prefix) for prefix in FROZEN_V67A_ALLOWED_SOURCE_ARTIFACT_REF_PREFIXES
    ):
        raise ValueError(
            f"{field_name} must resolve to the frozen v67a released ux governance source stack"
        )


def _assert_v67c_source_artifact_ref(ref: str, *, field_name: str) -> None:
    _assert_repo_relative_artifact_ref(ref, field_name=field_name)
    if not any(
        ref.startswith(prefix) for prefix in FROZEN_V67C_ALLOWED_SOURCE_ARTIFACT_REF_PREFIXES
    ):
        raise ValueError(
            f"{field_name} must resolve to the frozen v67c ergonomic/governance source stack"
        )


def _canonical_json(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_canonical_json(value: object) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _resolve_repo_relative_artifact_path(
    *,
    ref: str,
    field_name: str,
    repository_root: Path | None = None,
) -> Path:
    _assert_repo_relative_artifact_ref(ref, field_name=field_name)
    root = repository_root or repo_root(anchor=Path(__file__))
    root_resolved = root.resolve()
    relative_path = Path(ref.split("#", 1)[0])
    candidate = root / relative_path
    current = root
    for part in relative_path.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(f"{field_name} must not resolve through symlinked path components")
    try:
        resolved = candidate.resolve(strict=True)
    except FileNotFoundError:
        raise ValueError(f"{field_name} must resolve to an existing repo file")
    if not resolved.is_relative_to(root_resolved):
        raise ValueError(f"{field_name} must remain within the repository root")
    if not resolved.is_file():
        raise ValueError(f"{field_name} must resolve to an existing repo file")
    return resolved


def _load_repo_relative_json_artifact(
    *,
    ref: str,
    field_name: str,
    repository_root: Path | None = None,
) -> object:
    resolved = _resolve_repo_relative_artifact_path(
        ref=ref,
        field_name=field_name,
        repository_root=repository_root,
    )
    try:
        return json.loads(resolved.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"{field_name} must resolve to canonical json content") from exc


def _parse_component_ref(
    component_ref: str, *, field_name: str
) -> tuple[UXErgonomicComponentRefPrefix, str]:
    prefix, separator, identifier = component_ref.partition(":")
    if separator != ":" or prefix not in {"lane", "action_cluster"} or not identifier:
        raise ValueError(f"{field_name} must use lane:<id> or action_cluster:<id>")
    return prefix, identifier


def _source_artifact_hash_refs(rows: list["UXErgonomicSourceArtifactHash"]) -> list[str]:
    return [row.artifact_ref for row in rows]


def _assert_source_refs_and_hashes_align(
    *,
    source_artifact_refs: list[str],
    source_artifact_hashes: list["UXErgonomicSourceArtifactHash"],
    field_name: str,
) -> None:
    _assert_sorted_unique(source_artifact_refs, field_name=f"{field_name}.source_artifact_refs")
    hash_refs = _source_artifact_hash_refs(source_artifact_hashes)
    _assert_sorted_unique(hash_refs, field_name=f"{field_name}.source_artifact_hashes")
    if source_artifact_refs != hash_refs:
        raise ValueError(f"{field_name} source_artifact_refs must match source_artifact_hashes")


def _assert_source_artifact_hashes_match_actual(
    rows: list["UXErgonomicSourceArtifactHash"],
    *,
    field_name: str,
    repository_root: Path | None = None,
) -> None:
    for index, row in enumerate(rows):
        payload = _load_repo_relative_json_artifact(
            ref=row.artifact_ref,
            field_name=f"{field_name}[{index}].artifact_ref",
            repository_root=repository_root,
        )
        expected_hash = _sha256_canonical_json(payload)
        if row.artifact_hash != expected_hash:
            raise ValueError(
                f"{field_name} must match actual canonical source artifact payload hashes "
                f"for artifact_ref {row.artifact_ref}"
            )


class UXErgonomicRuleOverridePolicy(BaseModel):
    model_config = ConfigDict(extra="forbid")

    may_raise: bool
    may_lower: bool
    may_override_constitutional_invariant: bool
    may_override_repo_local_policy: bool
    may_override_external_standard_floor: bool


class UXErgonomicRuleConstraint(BaseModel):
    model_config = ConfigDict(extra="forbid")

    metric: str = Field(min_length=1)
    minimum_or_none: float | None = Field(default=None, ge=0)
    unit_or_none: str | None = None


class UXErgonomicRuleEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    rule_id: str = Field(min_length=1)
    authority_layer: UXErgonomicAuthorityLayer
    force: UXErgonomicRuleForce
    source_kind: str = Field(min_length=1)
    source_ref: str = Field(min_length=1)
    adopted_by_repo_policy: bool = False
    applies_to_component_classes: list[UXErgonomicClassId] = Field(min_length=1)
    applies_to_input_modes: list[UXErgonomicInputMode] = Field(min_length=1)
    constraint: UXErgonomicRuleConstraint
    override_policy: UXErgonomicRuleOverridePolicy
    provenance_state: UXErgonomicProvenanceState

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicRuleEntry":
        _assert_sorted_unique(
            self.applies_to_component_classes,
            field_name=f"rules[{self.rule_id}].applies_to_component_classes",
        )
        _assert_sorted_unique(
            self.applies_to_input_modes,
            field_name=f"rules[{self.rule_id}].applies_to_input_modes",
        )
        if self.authority_layer == "platform_preset" and self.force in {
            "hard_block",
            "hard_floor",
        }:
            if not self.adopted_by_repo_policy:
                raise ValueError(
                    f"rule {self.rule_id} must not treat platform preset as hard law "
                    "without repo adoption"
                )
        if self.authority_layer == "user_declared_preference":
            if self.override_policy.may_lower:
                raise ValueError(
                    f"rule {self.rule_id} must not allow user preference to lower hard floors"
                )
        if self.authority_layer == "heuristic_utility" and self.force != "advisory_ranking":
            raise ValueError(
                f"rule {self.rule_id} must use advisory_ranking when authority_layer "
                "is heuristic_utility"
            )
        if self.force == "advisory_ranking" and self.authority_layer != "heuristic_utility":
            raise ValueError(
                f"rule {self.rule_id} may use advisory_ranking only for heuristic_utility"
            )
        return self


class UXErgonomicRuleAuthorityStack(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXErgonomicRuleAuthorityStackSchemaVersion = UX_ERGONOMIC_RULE_AUTHORITY_STACK_SCHEMA
    rule_stack_id: str = Field(min_length=1)
    rules: list[UXErgonomicRuleEntry] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicRuleAuthorityStack":
        rule_ids = [rule.rule_id for rule in self.rules]
        _assert_sorted_distinct(rule_ids, field_name="rules.rule_id")
        authority_order = {
            "constitutional_surface_invariant": 0,
            "repo_local_policy": 1,
            "external_standard_floor": 2,
            "platform_preset": 3,
            "user_declared_preference": 4,
            "heuristic_utility": 5,
        }
        observed = [authority_order[rule.authority_layer] for rule in self.rules]
        if observed != sorted(observed):
            raise ValueError("rules must remain ordered by ergonomic authority precedence")
        return self


class UXComponentErgonomicClassRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    class_id: UXErgonomicClassId
    applies_to_surface_units: list[UXErgonomicSurfaceUnit] = Field(min_length=1)
    allowed_source_semantic_kinds: list[UXErgonomicSourceSemanticKind] = Field(min_length=1)
    default_visibility_requirement: UXErgonomicVisibilityState
    default_targetability_requirement: UXErgonomicRequirement
    default_readability_requirement: UXErgonomicRequirement
    allowed_collapse_policies: list[UXErgonomicCollapsePolicy] = Field(min_length=1)
    rule_bindings: list[str] = Field(min_length=1)
    taxonomy_status: UXErgonomicTaxonomyStatus = "starter_frozen"

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXComponentErgonomicClassRow":
        _assert_sorted_unique(
            self.applies_to_surface_units,
            field_name=f"class_rows[{self.class_id}].applies_to_surface_units",
        )
        _assert_sorted_unique(
            self.allowed_source_semantic_kinds,
            field_name=f"class_rows[{self.class_id}].allowed_source_semantic_kinds",
        )
        _assert_sorted_unique(
            self.allowed_collapse_policies,
            field_name=f"class_rows[{self.class_id}].allowed_collapse_policies",
        )
        _assert_sorted_unique(
            self.rule_bindings,
            field_name=f"class_rows[{self.class_id}].rule_bindings",
        )
        normalized = self.class_id.lower()
        if any(widget_token in normalized for widget_token in _WIDGET_SEMANTIC_TOKENS):
            raise ValueError(
                f"class_rows[{self.class_id}] must remain ergonomic, not widget-native"
            )
        return self


class UXComponentErgonomicRegistry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXComponentErgonomicRegistrySchemaVersion = UX_COMPONENT_ERGONOMIC_REGISTRY_SCHEMA
    registry_id: str = Field(min_length=1)
    registry_version: str = Field(min_length=1)
    class_rows: list[UXComponentErgonomicClassRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXComponentErgonomicRegistry":
        class_ids = [row.class_id for row in self.class_rows]
        _assert_exact_sequence(
            class_ids,
            expected=FROZEN_V67A_CLASS_IDS,
            field_name="class_rows.class_id",
        )
        for row in self.class_rows:
            expected_semantic_kind = FROZEN_V67A_CLASS_SEMANTIC_KIND[row.class_id]
            if row.allowed_source_semantic_kinds != [expected_semantic_kind]:
                raise ValueError(
                    f"class_rows[{row.class_id}] must bind exactly to {expected_semantic_kind!r}"
                )
            expected_surface_unit = FROZEN_V67A_CLASS_SURFACE_UNIT[row.class_id]
            if row.applies_to_surface_units != [expected_surface_unit]:
                raise ValueError(
                    f"class_rows[{row.class_id}] must apply exactly to {expected_surface_unit!r}"
                )
        return self


class UXErgonomicSourceArtifactHash(BaseModel):
    model_config = ConfigDict(extra="forbid")

    artifact_ref: str = Field(min_length=1)
    artifact_hash: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicSourceArtifactHash":
        _assert_v67a_source_artifact_ref(
            self.artifact_ref,
            field_name="source_artifact_hashes.artifact_ref",
        )
        return self


class UXComponentVisibilityContractRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    component_ref: str = Field(min_length=1)
    semantic_kind: UXErgonomicSourceSemanticKind
    ergonomic_class_id: UXErgonomicClassId
    visibility_state: UXErgonomicVisibilityState
    collapse_policy: UXErgonomicCollapsePolicy
    reveal_transition_or_none: SameContextReachableTerm | None = None
    continuous_visibility_required: bool

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXComponentVisibilityContractRow":
        _parse_component_ref(
            self.component_ref,
            field_name=f"component_rows[{self.component_ref}].component_ref",
        )
        if (
            self.visibility_state == "same_context_reachable"
            and self.reveal_transition_or_none is None
        ):
            raise ValueError(
                f"component_rows[{self.component_ref}] must carry "
                "reveal_transition_or_none when same_context_reachable"
            )
        return self


class UXComponentVisibilityContract(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXComponentVisibilityContractSchemaVersion = UX_COMPONENT_VISIBILITY_CONTRACT_SCHEMA
    contract_id: str = Field(min_length=1)
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    source_artifact_refs: list[str] = Field(min_length=1)
    source_artifact_hashes: list[UXErgonomicSourceArtifactHash] = Field(min_length=1)
    component_rows: list[UXComponentVisibilityContractRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXComponentVisibilityContract":
        _assert_source_refs_and_hashes_align(
            source_artifact_refs=self.source_artifact_refs,
            source_artifact_hashes=self.source_artifact_hashes,
            field_name="ux_component_visibility_contract",
        )
        component_refs = [row.component_ref for row in self.component_rows]
        _assert_sorted_distinct(component_refs, field_name="component_rows.component_ref")
        return self


class UXErgonomicCandidateProjectionShape(BaseModel):
    model_config = ConfigDict(extra="forbid")

    region_refs: list[str] = Field(min_length=1)
    lane_refs: list[str] = Field(min_length=1)
    action_cluster_refs: list[str] = Field(min_length=1)
    same_context_reveal_terms: list[SameContextReachableTerm] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicCandidateProjectionShape":
        _assert_sorted_unique(
            self.region_refs,
            field_name="projection_shape.region_refs",
        )
        _assert_sorted_unique(
            self.lane_refs,
            field_name="projection_shape.lane_refs",
        )
        _assert_sorted_unique(
            self.action_cluster_refs,
            field_name="projection_shape.action_cluster_refs",
        )
        _assert_sorted_unique(
            self.same_context_reveal_terms,
            field_name="projection_shape.same_context_reveal_terms",
        )
        return self


class UXErgonomicCandidateVisibilityClaim(BaseModel):
    model_config = ConfigDict(extra="forbid")

    component_ref: str = Field(min_length=1)
    visibility_state: UXErgonomicVisibilityState
    collapse_policy: UXErgonomicCollapsePolicy
    reveal_transition_or_none: SameContextReachableTerm | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicCandidateVisibilityClaim":
        _parse_component_ref(
            self.component_ref,
            field_name=f"component_visibility_claims[{self.component_ref}].component_ref",
        )
        if (
            self.visibility_state == "same_context_reachable"
            and self.reveal_transition_or_none is None
        ):
            raise ValueError(
                f"component_visibility_claims[{self.component_ref}] must carry "
                "reveal_transition_or_none when same_context_reachable"
            )
        return self


class UXErgonomicActionTargetingClaim(BaseModel):
    model_config = ConfigDict(extra="forbid")

    action_ref: str = Field(min_length=1)
    min_target_size_css_px: int = Field(ge=1)
    gate_visible_before_action: bool


class UXErgonomicCandidateProjectionProfileRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    candidate_profile_id: UXErgonomicCandidateProfileId
    approved_profile_id: UXApprovedProfileId
    target_envelope: UXErgonomicWindowOccupancyMode
    projection_shape: UXErgonomicCandidateProjectionShape
    component_visibility_claims: list[UXErgonomicCandidateVisibilityClaim] = Field(min_length=1)
    action_targeting_claims: list[UXErgonomicActionTargetingClaim] = Field(min_length=1)
    free_aesthetic_variables_declared: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicCandidateProjectionProfileRow":
        component_refs = [row.component_ref for row in self.component_visibility_claims]
        _assert_sorted_distinct(
            component_refs,
            field_name=f"candidate_rows[{self.candidate_profile_id}].component_visibility_claims",
        )
        action_refs = [row.action_ref for row in self.action_targeting_claims]
        _assert_sorted_distinct(
            action_refs,
            field_name=f"candidate_rows[{self.candidate_profile_id}].action_targeting_claims",
        )
        if action_refs != list(FROZEN_V67A_REQUIRED_ACTION_IDS):
            raise ValueError(
                f"candidate_rows[{self.candidate_profile_id}] must carry the frozen "
                "starter action targeting set"
            )
        _assert_sorted_unique(
            self.free_aesthetic_variables_declared,
            field_name=f"candidate_rows[{self.candidate_profile_id}].free_aesthetic_variables_declared",
        )
        expected_approved_profile_id = FROZEN_V67A_CANDIDATE_PROFILE_APPROVED_PROFILE[
            self.candidate_profile_id
        ]
        if self.approved_profile_id != expected_approved_profile_id:
            raise ValueError(
                f"candidate_rows[{self.candidate_profile_id}] must bind to "
                f"approved_profile_id {expected_approved_profile_id!r}"
            )
        expected_target_envelope = FROZEN_V67A_CANDIDATE_PROFILE_TARGET_ENVELOPE[
            self.candidate_profile_id
        ]
        if self.target_envelope != expected_target_envelope:
            raise ValueError(
                f"candidate_rows[{self.candidate_profile_id}] must bind to "
                f"target_envelope {expected_target_envelope!r}"
            )
        return self


class UXErgonomicCandidateProjectionProfileTable(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXErgonomicCandidateProjectionProfileTableSchemaVersion = (
        UX_ERGONOMIC_CANDIDATE_PROJECTION_PROFILE_TABLE_SCHEMA
    )
    candidate_profile_table_id: str = Field(min_length=1)
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    source_artifact_refs: list[str] = Field(min_length=1)
    source_artifact_hashes: list[UXErgonomicSourceArtifactHash] = Field(min_length=1)
    candidate_rows: list[UXErgonomicCandidateProjectionProfileRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicCandidateProjectionProfileTable":
        _assert_source_refs_and_hashes_align(
            source_artifact_refs=self.source_artifact_refs,
            source_artifact_hashes=self.source_artifact_hashes,
            field_name="ux_ergonomic_candidate_projection_profile_table",
        )
        candidate_ids = [row.candidate_profile_id for row in self.candidate_rows]
        _assert_exact_sequence(
            candidate_ids,
            expected=FROZEN_V67A_CANDIDATE_PROFILE_IDS,
            field_name="candidate_rows.candidate_profile_id",
        )
        return self


class UXErgonomicNumericMeasurement(BaseModel):
    model_config = ConfigDict(extra="forbid")

    numeric_value: float = Field(ge=0)
    unit: UXErgonomicMeasurementUnit
    provenance_state: UXErgonomicProvenanceState
    admissibility: UXErgonomicAdmissibility
    source_kind: UXErgonomicMeasurementSourceKind
    source_ref_or_none: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicNumericMeasurement":
        if self.source_ref_or_none is not None:
            _assert_repo_relative_artifact_ref(
                self.source_ref_or_none,
                field_name="numeric_measurement.source_ref_or_none",
            )
        return self


class UXErgonomicRectMeasurement(BaseModel):
    model_config = ConfigDict(extra="forbid")

    width_css_px: int = Field(ge=1)
    height_css_px: int = Field(ge=1)
    provenance_state: UXErgonomicProvenanceState
    admissibility: UXErgonomicAdmissibility
    source_kind: UXErgonomicMeasurementSourceKind
    source_ref_or_none: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicRectMeasurement":
        if self.source_ref_or_none is not None:
            _assert_repo_relative_artifact_ref(
                self.source_ref_or_none,
                field_name="rect_measurement.source_ref_or_none",
            )
        return self


class UXErgonomicCaseEnvelope(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXErgonomicCaseEnvelopeSchemaVersion = UX_ERGONOMIC_CASE_ENVELOPE_SCHEMA
    case_envelope_id: str = Field(min_length=1)
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    window_occupancy_mode: UXErgonomicWindowOccupancyMode
    input_mode: UXErgonomicInputMode
    task_posture: UXErgonomicTaskPosture
    viewport_css_geometry: UXErgonomicRectMeasurement
    available_surface_css_geometry: UXErgonomicRectMeasurement
    zoom_scale_or_none: UXErgonomicNumericMeasurement | None = None
    device_pixel_ratio_or_none: UXErgonomicNumericMeasurement | None = None
    physical_screen_ppi_or_none: UXErgonomicNumericMeasurement | None = None
    viewing_distance_mm_or_none: UXErgonomicNumericMeasurement | None = None
    preferred_target_min_css_px_or_none: UXErgonomicNumericMeasurement | None = None
    preferred_text_min_css_px_or_none: UXErgonomicNumericMeasurement | None = None
    physical_size_reasoning_required: bool = False
    visual_angle_reasoning_required: bool = False

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicCaseEnvelope":
        assert_ux_case_envelope_admissibility_consistent(case_envelope=self)
        return self


class UXErgonomicAdjudicationRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXErgonomicAdjudicationRequestSchemaVersion = UX_ERGONOMIC_ADJUDICATION_REQUEST_SCHEMA
    request_id: str = Field(min_length=1)
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    source_artifact_refs: list[str] = Field(min_length=1)
    source_artifact_hashes: list[UXErgonomicSourceArtifactHash] = Field(min_length=1)
    rule_stack_ref: str = Field(min_length=1)
    registry_ref: str = Field(min_length=1)
    visibility_contract_ref: str = Field(min_length=1)
    candidate_profile_table_ref: str = Field(min_length=1)
    case_envelope_ref: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicAdjudicationRequest":
        _assert_source_refs_and_hashes_align(
            source_artifact_refs=self.source_artifact_refs,
            source_artifact_hashes=self.source_artifact_hashes,
            field_name="ux_ergonomic_adjudication_request",
        )
        return self


class UXErgonomicBlockedCandidateRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    candidate_profile_id: UXErgonomicCandidateProfileId
    blocking_reason_codes: list[str] = Field(min_length=1)
    authority_layers_triggered: list[UXErgonomicAuthorityLayer] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicBlockedCandidateRow":
        _assert_sorted_unique(
            self.blocking_reason_codes,
            field_name=f"blocked_candidate_rows[{self.candidate_profile_id}].blocking_reason_codes",
        )
        _assert_sorted_unique(
            self.authority_layers_triggered,
            field_name=f"blocked_candidate_rows[{self.candidate_profile_id}].authority_layers_triggered",
        )
        return self


class UXErgonomicFeasibleCandidateRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    candidate_profile_id: UXErgonomicCandidateProfileId
    preference_tier: UXErgonomicPreferenceTier
    supporting_reason_codes: list[str] = Field(min_length=1)
    residual_ambiguity_or_none: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicFeasibleCandidateRow":
        if self.preference_tier == "blocked":
            raise ValueError(
                f"feasible_candidate_rows[{self.candidate_profile_id}] must not use blocked tier"
            )
        _assert_sorted_unique(
            self.supporting_reason_codes,
            field_name=f"feasible_candidate_rows[{self.candidate_profile_id}].supporting_reason_codes",
        )
        return self


class UXErgonomicAmbiguityRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    ambiguity_id: str = Field(min_length=1)
    ambiguity_kind: str = Field(min_length=1)
    affected_candidate_ids: list[UXErgonomicCandidateProfileId] = Field(min_length=1)
    severity: UXErgonomicAmbiguitySeverity
    reason_codes: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicAmbiguityRow":
        _assert_sorted_unique(
            self.affected_candidate_ids,
            field_name=f"ambiguity_rows[{self.ambiguity_id}].affected_candidate_ids",
        )
        _assert_sorted_unique(
            self.reason_codes,
            field_name=f"ambiguity_rows[{self.ambiguity_id}].reason_codes",
        )
        return self


class UXErgonomicMeasurementObligationRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    obligation_id: str = Field(min_length=1)
    candidate_profile_id: UXErgonomicCandidateProfileId
    measurement_kind: UXErgonomicMeasurementObligationKind
    required_for: UXErgonomicObligationSeverity
    reason_codes: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicMeasurementObligationRow":
        _assert_sorted_unique(
            self.reason_codes,
            field_name=f"measurement_obligation_rows[{self.obligation_id}].reason_codes",
        )
        return self


class UXErgonomicAdjudicationResult(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXErgonomicAdjudicationResultSchemaVersion = UX_ERGONOMIC_ADJUDICATION_RESULT_SCHEMA
    result_id: str = Field(min_length=1)
    request_ref: str = Field(min_length=1)
    source_artifact_refs: list[str] = Field(min_length=1)
    source_artifact_hashes: list[UXErgonomicSourceArtifactHash] = Field(min_length=1)
    report_status: UXErgonomicReportStatus
    overall_judgment: UXErgonomicOverallJudgment
    blocked_candidate_rows: list[UXErgonomicBlockedCandidateRow] = Field(default_factory=list)
    feasible_candidate_rows: list[UXErgonomicFeasibleCandidateRow] = Field(default_factory=list)
    ambiguity_rows: list[UXErgonomicAmbiguityRow] = Field(default_factory=list)
    measurement_obligation_rows: list[UXErgonomicMeasurementObligationRow] = Field(
        default_factory=list
    )

    @model_validator(mode="before")
    @classmethod
    def _reject_scalar_scores(cls, payload: Any) -> Any:
        if not isinstance(payload, dict):
            return payload
        for row in payload.get("feasible_candidate_rows", []):
            if isinstance(row, dict) and any(
                key in row for key in ("scalar_preference_score", "preference_score", "tier_score")
            ):
                raise ValueError("results cannot export scalar preference scores")
        return payload

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicAdjudicationResult":
        _assert_source_refs_and_hashes_align(
            source_artifact_refs=self.source_artifact_refs,
            source_artifact_hashes=self.source_artifact_hashes,
            field_name="ux_ergonomic_adjudication_result",
        )
        blocked_ids = [row.candidate_profile_id for row in self.blocked_candidate_rows]
        feasible_ids = [row.candidate_profile_id for row in self.feasible_candidate_rows]
        _assert_sorted_distinct(
            blocked_ids,
            field_name="blocked_candidate_rows.candidate_profile_id",
        )
        _assert_sorted_distinct(
            feasible_ids,
            field_name="feasible_candidate_rows.candidate_profile_id",
        )
        if set(blocked_ids) & set(feasible_ids):
            raise ValueError("blocked_candidate_rows and feasible_candidate_rows must be disjoint")
        if self.report_status != "valid":
            if (
                self.blocked_candidate_rows
                or self.feasible_candidate_rows
                or self.ambiguity_rows
                or self.measurement_obligation_rows
            ):
                raise ValueError(
                    "invalid adjudication results must not carry candidate or "
                    "obligation rows"
                )
            if self.overall_judgment == "pass":
                raise ValueError(
                    "invalid adjudication results must not carry pass "
                    "overall_judgment"
                )
        if self.overall_judgment == "pass" and not self.feasible_candidate_rows:
            raise ValueError("pass overall_judgment requires feasible_candidate_rows")
        if self.overall_judgment == "fail" and self.feasible_candidate_rows:
            raise ValueError("fail overall_judgment must not carry feasible_candidate_rows")
        return self


class UXErgonomicRuntimeBridgeSourceArtifactHash(BaseModel):
    model_config = ConfigDict(extra="forbid")

    artifact_ref: str = Field(min_length=1)
    artifact_hash: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicRuntimeBridgeSourceArtifactHash":
        _assert_v67c_source_artifact_ref(
            self.artifact_ref,
            field_name="runtime_bridge_source_artifact_hashes.artifact_ref",
        )
        return self


class UXErgonomicMeasuredBoundingBoxCssPx(BaseModel):
    model_config = ConfigDict(extra="forbid")

    x: int = Field(ge=0)
    y: int = Field(ge=0)
    width: int = Field(ge=1)
    height: int = Field(ge=1)


class UXErgonomicRuntimeMeasurementRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    component_ref: str = Field(min_length=1)
    candidate_profile_id: UXErgonomicCandidateProfileId
    measured_bounding_box_css_px: UXErgonomicMeasuredBoundingBoxCssPx
    computed_font_size_css_px_or_none: int | None = Field(default=None, ge=1)
    computed_line_height_css_px_or_none: int | None = Field(default=None, ge=1)
    observed_visibility_state: UXErgonomicObservedVisibilityState
    observed_reveal_transition_or_none: UXErgonomicObservedRevealTransition | None = None
    provenance_state: UXErgonomicProvenanceState
    source_kind: UXErgonomicMeasurementSourceKind
    source_ref: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicRuntimeMeasurementRow":
        _parse_component_ref(
            self.component_ref,
            field_name=f"measurement_rows[{self.component_ref}].component_ref",
        )
        _assert_repo_relative_artifact_ref(
            self.source_ref,
            field_name=f"measurement_rows[{self.component_ref}].source_ref",
        )
        if (
            self.observed_visibility_state == "same_context_reachable"
            and self.observed_reveal_transition_or_none is None
        ):
            raise ValueError(
                f"measurement_rows[{self.component_ref}] must carry "
                "observed_reveal_transition_or_none when observed_visibility_state is "
                "same_context_reachable"
            )
        if (
            self.observed_reveal_transition_or_none is not None
            and self.observed_visibility_state != "same_context_reachable"
            and self.observed_reveal_transition_or_none != "unexpected_route_transition"
        ):
            raise ValueError(
                f"measurement_rows[{self.component_ref}] may carry a same-context reveal "
                "transition only when observed_visibility_state is same_context_reachable"
            )
        return self


class UXErgonomicRuntimeMeasurementEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXErgonomicRuntimeMeasurementEvidenceSchemaVersion = (
        UX_ERGONOMIC_RUNTIME_MEASUREMENT_EVIDENCE_SCHEMA
    )
    evidence_id: str = Field(min_length=1)
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    candidate_profile_id: UXErgonomicCandidateProfileId
    request_ref: str = Field(min_length=1)
    adjudication_result_ref: str = Field(min_length=1)
    ux_morph_diagnostics_ref_or_none: str | None = None
    ux_conformance_report_ref_or_none: str | None = None
    source_artifact_refs: list[str] = Field(min_length=1)
    source_artifact_hashes: list[UXErgonomicRuntimeBridgeSourceArtifactHash] = Field(min_length=1)
    measurement_rows: list[UXErgonomicRuntimeMeasurementRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicRuntimeMeasurementEvidence":
        _assert_source_refs_and_hashes_align(
            source_artifact_refs=self.source_artifact_refs,
            source_artifact_hashes=self.source_artifact_hashes,
            field_name="ux_ergonomic_runtime_measurement_evidence",
        )
        measurement_component_refs = [row.component_ref for row in self.measurement_rows]
        _assert_sorted_distinct(
            measurement_component_refs,
            field_name="measurement_rows.component_ref",
        )
        if any(
            row.candidate_profile_id != self.candidate_profile_id
            for row in self.measurement_rows
        ):
            raise ValueError(
                "measurement_rows candidate_profile_id must match the top-level "
                "candidate_profile_id"
            )
        if self.ux_morph_diagnostics_ref_or_none is not None:
            _assert_v67c_source_artifact_ref(
                self.ux_morph_diagnostics_ref_or_none,
                field_name="ux_morph_diagnostics_ref_or_none",
            )
        if self.ux_conformance_report_ref_or_none is not None:
            _assert_v67c_source_artifact_ref(
                self.ux_conformance_report_ref_or_none,
                field_name="ux_conformance_report_ref_or_none",
            )
        return self


class UXErgonomicRuntimeMismatchRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    mismatch_id: str = Field(min_length=1)
    mismatch_family: UXErgonomicRuntimeMismatchFamily
    candidate_profile_id_or_none: UXErgonomicCandidateProfileId | None = None
    component_ref_or_none: str | None = None
    obligation_id_or_none: str | None = None
    source_ref_or_none: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicRuntimeMismatchRow":
        if self.component_ref_or_none is not None:
            _parse_component_ref(
                self.component_ref_or_none,
                field_name=f"mismatch_rows[{self.mismatch_id}].component_ref_or_none",
            )
        if self.source_ref_or_none is not None:
            _assert_repo_relative_artifact_ref(
                self.source_ref_or_none,
                field_name=f"mismatch_rows[{self.mismatch_id}].source_ref_or_none",
            )
        return self


class UXErgonomicRuntimeBridgeReport(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: UXErgonomicRuntimeBridgeReportSchemaVersion = UX_ERGONOMIC_RUNTIME_BRIDGE_REPORT_SCHEMA
    bridge_report_id: str = Field(min_length=1)
    reference_surface_family: UXReferenceSurfaceFamily = V36A_REFERENCE_SURFACE_FAMILY
    reference_instance_id: str = Field(min_length=1)
    request_ref: str = Field(min_length=1)
    adjudication_result_ref: str = Field(min_length=1)
    runtime_measurement_evidence_ref: str = Field(min_length=1)
    ux_morph_diagnostics_ref_or_none: str | None = None
    ux_conformance_report_ref_or_none: str | None = None
    source_artifact_refs: list[str] = Field(min_length=1)
    source_artifact_hashes: list[UXErgonomicRuntimeBridgeSourceArtifactHash] = Field(min_length=1)
    bridge_status: UXErgonomicRuntimeBridgeStatus
    mismatch_rows: list[UXErgonomicRuntimeMismatchRow] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UXErgonomicRuntimeBridgeReport":
        _assert_source_refs_and_hashes_align(
            source_artifact_refs=self.source_artifact_refs,
            source_artifact_hashes=self.source_artifact_hashes,
            field_name="ux_ergonomic_runtime_bridge_report",
        )
        mismatch_ids = [row.mismatch_id for row in self.mismatch_rows]
        _assert_sorted_distinct(
            mismatch_ids,
            field_name="mismatch_rows.mismatch_id",
        )
        if self.bridge_status == "advisory_clean" and self.mismatch_rows:
            raise ValueError("advisory_clean bridge reports must not carry mismatch_rows")
        if self.bridge_status != "advisory_clean" and not self.mismatch_rows:
            raise ValueError("non-clean bridge reports must carry mismatch_rows")
        if self.ux_morph_diagnostics_ref_or_none is not None:
            _assert_v67c_source_artifact_ref(
                self.ux_morph_diagnostics_ref_or_none,
                field_name="ux_morph_diagnostics_ref_or_none",
            )
        if self.ux_conformance_report_ref_or_none is not None:
            _assert_v67c_source_artifact_ref(
                self.ux_conformance_report_ref_or_none,
                field_name="ux_conformance_report_ref_or_none",
            )
        return self


def canonicalize_ux_ergonomic_rule_authority_stack_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = UXErgonomicRuleAuthorityStack.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_component_ergonomic_registry_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = UXComponentErgonomicRegistry.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_component_visibility_contract_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = UXComponentVisibilityContract.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_ergonomic_candidate_projection_profile_table_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = UXErgonomicCandidateProjectionProfileTable.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_ergonomic_case_envelope_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = UXErgonomicCaseEnvelope.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_ergonomic_adjudication_request_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = UXErgonomicAdjudicationRequest.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_ergonomic_adjudication_result_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = UXErgonomicAdjudicationResult.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_ergonomic_runtime_measurement_evidence_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = UXErgonomicRuntimeMeasurementEvidence.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_ux_ergonomic_runtime_bridge_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = UXErgonomicRuntimeBridgeReport.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def assert_ux_ergonomic_candidate_projection_table_bound_to_approved_profiles(
    *,
    candidate_projection_table: UXErgonomicCandidateProjectionProfileTable,
    approved_profile_table: V36AFirstFamilyApprovedProfileTable,
) -> None:
    if (
        candidate_projection_table.reference_surface_family
        != approved_profile_table.reference_surface_family
    ):
        raise ValueError("candidate projection table reference_surface_family mismatch")
    for row in candidate_projection_table.candidate_rows:
        approved_profile_for_id(
            approved_profile_table,
            approved_profile_id=row.approved_profile_id,
        )


def assert_ux_ergonomic_candidate_projection_table_bound_to_surface_projection(
    *,
    candidate_projection_table: UXErgonomicCandidateProjectionProfileTable,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
    same_context_glossary: V36ASameContextReachabilityGlossary,
) -> None:
    if (
        candidate_projection_table.reference_surface_family
        != surface_projection.reference_surface_family
    ):
        raise ValueError("candidate projection table reference_surface_family mismatch")
    if candidate_projection_table.reference_instance_id != surface_projection.reference_instance_id:
        raise ValueError("candidate projection table reference_instance_id mismatch")
    if interaction_contract.reference_instance_id != surface_projection.reference_instance_id:
        raise ValueError("interaction contract reference_instance_id mismatch")
    if (
        same_context_glossary.reference_surface_family
        != surface_projection.reference_surface_family
    ):
        raise ValueError("same_context glossary reference_surface_family mismatch")

    valid_region_ids = {region.region_id for region in surface_projection.regions}
    valid_lane_ids = {lane.lane_id for lane in surface_projection.lanes}
    valid_cluster_ids = {cluster.cluster_id for cluster in surface_projection.action_clusters}
    valid_action_ids = {entry.interaction_id for entry in interaction_contract.interaction_entries}
    valid_same_context_terms = set(same_context_glossary.same_context_reachable)

    for row in candidate_projection_table.candidate_rows:
        if any(
            region_ref not in valid_region_ids
            for region_ref in row.projection_shape.region_refs
        ):
            raise ValueError(
                f"candidate {row.candidate_profile_id} references unknown region "
                "in projection_shape.region_refs"
            )
        if any(lane_ref not in valid_lane_ids for lane_ref in row.projection_shape.lane_refs):
            raise ValueError(
                f"candidate {row.candidate_profile_id} references unknown lane "
                "in projection_shape.lane_refs"
            )
        if any(
            cluster_ref not in valid_cluster_ids
            for cluster_ref in row.projection_shape.action_cluster_refs
        ):
            raise ValueError(
                f"candidate {row.candidate_profile_id} references unknown action "
                "cluster in projection_shape.action_cluster_refs"
            )
        if any(
            term not in valid_same_context_terms
            for term in row.projection_shape.same_context_reveal_terms
        ):
            raise ValueError(
                f"candidate {row.candidate_profile_id} uses unknown same-context reveal term"
            )
        for claim in row.component_visibility_claims:
            prefix, identifier = _parse_component_ref(
                claim.component_ref,
                field_name=f"candidate_rows[{row.candidate_profile_id}].component_visibility_claims.component_ref",
            )
            if prefix == "lane" and identifier not in valid_lane_ids:
                raise ValueError(
                    f"candidate {row.candidate_profile_id} references unknown lane component_ref"
                )
            if prefix == "action_cluster" and identifier not in valid_cluster_ids:
                raise ValueError(
                    f"candidate {row.candidate_profile_id} references unknown "
                    "action_cluster component_ref"
                )
        for targeting_claim in row.action_targeting_claims:
            if targeting_claim.action_ref not in valid_action_ids:
                raise ValueError(
                    f"candidate {row.candidate_profile_id} references unknown "
                    "interaction action_ref"
                )


def assert_ux_visibility_contract_complete_for_projection(
    *,
    visibility_contract: UXComponentVisibilityContract,
    surface_projection: UXSurfaceProjection,
) -> None:
    if visibility_contract.reference_surface_family != surface_projection.reference_surface_family:
        raise ValueError("visibility contract reference_surface_family mismatch")
    if visibility_contract.reference_instance_id != surface_projection.reference_instance_id:
        raise ValueError("visibility contract reference_instance_id mismatch")

    required_component_refs = sorted(FROZEN_V67A_COMPONENT_REF_SEQUENCE)
    observed_component_refs = [row.component_ref for row in visibility_contract.component_rows]
    if observed_component_refs != required_component_refs:
        raise ValueError("visibility contract must cover the frozen starter component ref set")

    valid_lane_ids = {lane.lane_id for lane in surface_projection.lanes}
    valid_cluster_ids = {cluster.cluster_id for cluster in surface_projection.action_clusters}
    for row in visibility_contract.component_rows:
        expected_class_id = FROZEN_V67A_COMPONENT_REF_TO_CLASS_ID[row.component_ref]
        if row.ergonomic_class_id != expected_class_id:
            raise ValueError(
                f"visibility contract row {row.component_ref} must use "
                f"ergonomic_class_id {expected_class_id!r}"
            )
        expected_semantic_kind = FROZEN_V67A_CLASS_SEMANTIC_KIND[expected_class_id]
        if row.semantic_kind != expected_semantic_kind:
            raise ValueError(
                f"visibility contract row {row.component_ref} must use "
                f"semantic_kind {expected_semantic_kind!r}"
            )
        prefix, identifier = _parse_component_ref(
            row.component_ref,
            field_name=f"component_rows[{row.component_ref}].component_ref",
        )
        if prefix == "lane" and identifier not in valid_lane_ids:
            raise ValueError(f"visibility contract row {row.component_ref} references unknown lane")
        if prefix == "action_cluster" and identifier not in valid_cluster_ids:
            raise ValueError(
                f"visibility contract row {row.component_ref} references unknown action cluster"
            )
        if (
            row.component_ref in FROZEN_V67A_REQUIRED_EVIDENCE_COMPONENT_REFS
            and not row.continuous_visibility_required
        ):
            raise ValueError(
                f"visibility contract row {row.component_ref} must remain "
                "continuously visible in V67-A"
            )


def assert_ux_case_envelope_admissibility_consistent(
    *,
    case_envelope: UXErgonomicCaseEnvelope,
) -> None:
    css_allowed = {"css_geometry_admissible", "planning_declared_css_geometry"}
    if case_envelope.viewport_css_geometry.admissibility not in css_allowed:
        raise ValueError("viewport_css_geometry must remain css-geometry-admissible only")
    if case_envelope.available_surface_css_geometry.admissibility not in css_allowed:
        raise ValueError("available_surface_css_geometry must remain css-geometry-admissible only")

    if case_envelope.preferred_target_min_css_px_or_none is not None:
        if (
            case_envelope.preferred_target_min_css_px_or_none.provenance_state
            != "declared_user_profile"
        ):
            raise ValueError(
                "preferred_target_min_css_px_or_none must use declared_user_profile provenance"
            )
    if case_envelope.preferred_text_min_css_px_or_none is not None:
        if (
            case_envelope.preferred_text_min_css_px_or_none.provenance_state
            != "declared_user_profile"
        ):
            raise ValueError(
                "preferred_text_min_css_px_or_none must use declared_user_profile provenance"
            )

    device_pixel_ratio = case_envelope.device_pixel_ratio_or_none
    physical_screen_ppi = case_envelope.physical_screen_ppi_or_none
    viewing_distance_mm = case_envelope.viewing_distance_mm_or_none
    physical_chain_available = (
        device_pixel_ratio is not None
        and device_pixel_ratio.unit == "ratio"
        and device_pixel_ratio.admissibility == "physical_size_admissible"
        and physical_screen_ppi is not None
        and physical_screen_ppi.unit == "ppi"
        and physical_screen_ppi.admissibility == "physical_size_admissible"
    )
    visual_chain_available = (
        physical_chain_available
        and viewing_distance_mm is not None
        and viewing_distance_mm.unit == "mm"
        and viewing_distance_mm.admissibility == "visual_angle_admissible"
    )
    if case_envelope.physical_size_reasoning_required and not physical_chain_available:
        raise ValueError(
            "physical_size_reasoning_required must not be true when "
            "physical-size chain is inadmissible"
        )
    if case_envelope.visual_angle_reasoning_required and not visual_chain_available:
        raise ValueError(
            "visual_angle_reasoning_required must not be true when "
            "visual-angle chain is inadmissible"
        )


def assert_ux_ergonomic_bundle_source_binding_consistent(
    *,
    rule_authority_stack: UXErgonomicRuleAuthorityStack,
    registry: UXComponentErgonomicRegistry,
    visibility_contract: UXComponentVisibilityContract,
    candidate_projection_table: UXErgonomicCandidateProjectionProfileTable,
    case_envelope: UXErgonomicCaseEnvelope,
    request: UXErgonomicAdjudicationRequest,
    result: UXErgonomicAdjudicationResult | None = None,
) -> None:
    repository_root = repo_root(anchor=Path(__file__))
    if (
        visibility_contract.reference_surface_family
        != candidate_projection_table.reference_surface_family
    ):
        raise ValueError(
            "visibility contract and candidate table reference_surface_family "
            "mismatch"
        )
    if (
        visibility_contract.reference_instance_id
        != candidate_projection_table.reference_instance_id
    ):
        raise ValueError("visibility contract and candidate table reference_instance_id mismatch")
    if request.reference_surface_family != visibility_contract.reference_surface_family:
        raise ValueError("request reference_surface_family mismatch")
    if request.reference_instance_id != visibility_contract.reference_instance_id:
        raise ValueError("request reference_instance_id mismatch")
    if case_envelope.reference_surface_family != request.reference_surface_family:
        raise ValueError("case envelope reference_surface_family mismatch")
    if case_envelope.reference_instance_id != request.reference_instance_id:
        raise ValueError("case envelope reference_instance_id mismatch")

    if request.rule_stack_ref != rule_authority_stack.rule_stack_id:
        raise ValueError("request.rule_stack_ref must bind to rule_stack_id")
    if request.registry_ref != registry.registry_id:
        raise ValueError("request.registry_ref must bind to registry_id")
    if request.visibility_contract_ref != visibility_contract.contract_id:
        raise ValueError("request.visibility_contract_ref must bind to contract_id")
    if request.candidate_profile_table_ref != candidate_projection_table.candidate_profile_table_id:
        raise ValueError(
            "request.candidate_profile_table_ref must bind to "
            "candidate_profile_table_id"
        )
    if request.case_envelope_ref != case_envelope.case_envelope_id:
        raise ValueError("request.case_envelope_ref must bind to case_envelope_id")

    expected_source_refs = visibility_contract.source_artifact_refs
    if candidate_projection_table.source_artifact_refs != expected_source_refs:
        raise ValueError(
            "candidate projection table must reuse visibility contract "
            "source_artifact_refs"
        )
    if request.source_artifact_refs != expected_source_refs:
        raise ValueError("request must reuse starter source_artifact_refs")
    expected_hash_rows = visibility_contract.source_artifact_hashes
    if candidate_projection_table.source_artifact_hashes != expected_hash_rows:
        raise ValueError(
            "candidate projection table must reuse visibility contract "
            "source_artifact_hashes"
        )
    if request.source_artifact_hashes != expected_hash_rows:
        raise ValueError("request must reuse starter source_artifact_hashes")

    _assert_source_artifact_hashes_match_actual(
        visibility_contract.source_artifact_hashes,
        field_name="visibility_contract.source_artifact_hashes",
        repository_root=repository_root,
    )
    if result is not None:
        if result.request_ref != request.request_id:
            raise ValueError("result.request_ref must bind to request_id")
        if result.source_artifact_refs != expected_source_refs:
            raise ValueError("result must reuse starter source_artifact_refs")
        if result.source_artifact_hashes != expected_hash_rows:
            raise ValueError("result must reuse starter source_artifact_hashes")


def assert_ux_adjudication_result_consistent_with_request(
    *,
    result: UXErgonomicAdjudicationResult,
    request: UXErgonomicAdjudicationRequest,
    candidate_projection_table: UXErgonomicCandidateProjectionProfileTable,
) -> None:
    if result.request_ref != request.request_id:
        raise ValueError("result.request_ref must bind to request_id")
    valid_candidate_ids = {
        row.candidate_profile_id for row in candidate_projection_table.candidate_rows
    }
    blocked_ids = {row.candidate_profile_id for row in result.blocked_candidate_rows}
    feasible_ids = {row.candidate_profile_id for row in result.feasible_candidate_rows}
    obligation_ids = {row.candidate_profile_id for row in result.measurement_obligation_rows}
    if not blocked_ids.issubset(valid_candidate_ids):
        raise ValueError("blocked_candidate_rows must use candidate ids from the candidate table")
    if not feasible_ids.issubset(valid_candidate_ids):
        raise ValueError("feasible_candidate_rows must use candidate ids from the candidate table")
    if not obligation_ids.issubset(valid_candidate_ids):
        raise ValueError(
            "measurement_obligation_rows must use candidate ids from the "
            "candidate table"
        )
    for row in result.ambiguity_rows:
        if not set(row.affected_candidate_ids).issubset(valid_candidate_ids):
            raise ValueError("ambiguity_rows must use candidate ids from the candidate table")
