from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Iterable, TypeVar

from pydantic import BaseModel, ConfigDict, Field, ValidationError

from .ux_governance import (
    UX_DOMAIN_PACKET_SCHEMA,
    UX_INTERACTION_CONTRACT_SCHEMA,
    UX_MORPH_IR_SCHEMA,
    UX_SURFACE_PROJECTION_SCHEMA,
    V36C_RENDERED_REFERENCE_SURFACE_BINDING_MANIFEST_SCHEMA,
    V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_SCHEMA,
    V36C_RENDERED_REFERENCE_SURFACE_SNAPSHOT_SCHEMA,
    UXConformanceReport,
    UXDomainPacket,
    UXInteractionContract,
    UXMorphDiagnostics,
    UXMorphIR,
    UXSurfaceProjection,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    assert_v36a_reference_bundle_consistent,
    assert_v36b_reference_bundle_consistent,
    assert_v36d_reference_bundle_consistent,
    canonicalize_ux_conformance_report_payload,
    canonicalize_ux_interaction_contract_payload,
    canonicalize_ux_morph_diagnostics_payload,
    canonicalize_ux_surface_projection_payload,
)

V36A_UX_DOMAIN_MORPH_IR_EVIDENCE_SCHEMA = "v36a_ux_domain_morph_ir_evidence@1"
V36A_UX_DOMAIN_MORPH_IR_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md#v36a_ux_domain_morph_ir_contract@1"
)
V36B_SURFACE_PROJECTION_INTERACTION_EVIDENCE_SCHEMA = (
    "v36b_surface_projection_interaction_evidence@1"
)
V36B_SURFACE_PROJECTION_INTERACTION_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md#v36b_surface_projection_interaction_contract@1"
)
V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_EVIDENCE_SCHEMA = (
    "v36c_artifact_inspector_reference_surface_evidence@1"
)
V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md#v36c_artifact_inspector_reference_surface_contract@1"
)
V36D_MORPH_DIAGNOSTICS_CONFORMANCE_EVIDENCE_SCHEMA = (
    "v36d_morph_diagnostics_conformance_evidence@1"
)
V36D_MORPH_DIAGNOSTICS_CONFORMANCE_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md#v36d_morph_diagnostics_conformance_contract@1"
)
STOP_GATE_METRICS_SCHEMA = "stop_gate_metrics@1"
EXPECTED_METRIC_KEY_CARDINALITY = 80
DEFAULT_V60_BASELINE_METRICS_PATH = "artifacts/stop_gate/metrics_v60_closeout.json"
DEFAULT_V61_BASELINE_METRICS_PATH = "artifacts/stop_gate/metrics_v61_closeout.json"
DEFAULT_V62_BASELINE_METRICS_PATH = "artifacts/stop_gate/metrics_v62_closeout.json"
DEFAULT_V63_BASELINE_METRICS_PATH = "artifacts/stop_gate/metrics_v63_closeout.json"

DEFAULT_UX_DOMAIN_PACKET_SCHEMA_PATH = "packages/adeu_core_ir/schema/ux_domain_packet.v1.json"
DEFAULT_UX_MORPH_IR_SCHEMA_PATH = "packages/adeu_core_ir/schema/ux_morph_ir.v1.json"
DEFAULT_UX_SURFACE_PROJECTION_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/ux_surface_projection.v1.json"
)
DEFAULT_UX_INTERACTION_CONTRACT_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/ux_interaction_contract.v1.json"
)
DEFAULT_UX_MORPH_DIAGNOSTICS_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/ux_morph_diagnostics.v1.json"
)
DEFAULT_UX_CONFORMANCE_REPORT_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/ux_conformance_report.v1.json"
)
DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus61/"
    "ux_domain_packet_artifact_inspector_reference.json"
)
DEFAULT_UX_MORPH_IR_REFERENCE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus61/ux_morph_ir_artifact_inspector_reference.json"
)
DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus62/"
    "ux_surface_projection_artifact_inspector_reference.json"
)
DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus62/"
    "ux_interaction_contract_artifact_inspector_reference.json"
)
DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus64/"
    "ux_morph_diagnostics_artifact_inspector_reference.json"
)
DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus64/"
    "ux_conformance_report_artifact_inspector_reference.json"
)
DEFAULT_APPROVED_PROFILE_TABLE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json"
)
DEFAULT_SAME_CONTEXT_GLOSSARY_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json"
)
DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus63/v36c_rendered_reference_surface_contract.json"
)
DEFAULT_V36C_RENDERED_SURFACE_SNAPSHOT_PATH = (
    "artifacts/agent_harness/v63/evidence_inputs/"
    "v36c_artifact_inspector_reference_surface_snapshot_v63.json"
)
DEFAULT_V36C_IMPLEMENTATION_BINDING_MANIFEST_PATH = (
    "artifacts/agent_harness/v63/evidence_inputs/"
    "v36c_artifact_inspector_reference_surface_binding_manifest_v63.json"
)
DEFAULT_V36C_REFERENCE_SURFACE_EVIDENCE_PATH = (
    "artifacts/agent_harness/v63/evidence_inputs/"
    "v36c_artifact_inspector_reference_surface_evidence_v63.json"
)
V36C_RENDERED_ROUTE_ID = "artifact_inspector_reference_surface"
V36C_RENDERED_ROUTE_PATH = "/artifact-inspector"
V36C_ROUTE_PAYLOAD_PARITY_MODE = (
    "presentational_transform_only_no_authority_or_reachability_meaning_drift"
)
V36C_DIAGNOSTICS_LANE_MODE = "placeholder_or_existing_artifact_backed_read_only_only"
V36C_TRUTH_SOURCE_POLICY = "accepted_v36_artifacts_only"
V36C_RENDERED_SURFACE_SNAPSHOT_KIND = "semantic_structured_route_snapshot@1"
V36C_RENDERED_SNAPSHOT_SCHEMA = "v36c_rendered_reference_surface_semantic_snapshot@1"
V36C_BINDING_MANIFEST_SCHEMA = "v36c_rendered_reference_surface_binding_manifest@1"

ModelT = TypeVar("ModelT", bound=BaseModel)
_FREE_FORM_POLICY_LOC = (
    "authority_boundary_policy",
    "no_free_form_ui_codegen_without_ir",
)
_AUTHORITY_MINTING_POLICY_LOC = (
    "authority_boundary_policy",
    "ui_artifacts_may_express_but_may_not_mint_authority",
)
_VISUAL_AUTHORITY_INFLATION_POLICY_LOC = (
    "authority_boundary_policy",
    "no_visual_authority_inflation",
)
_FORBIDDEN_AUTHORITATIVE_GATE_SOURCE_VALUES = {
    "page_local_constants",
    "ui_route_configuration",
    "ad_hoc_component_logic",
}
_IMPLEMENTATION_BINDING_REFERENCE_INSTANCE_ERROR = (
    "implementation_observable_bindings target_ref must bind to bundle reference_instance_id"
)
_RENDERED_PROVENANCE_TARGETS = (
    "rendered_regions",
    "authority_bearing_controls",
    "evidence_bearing_regions",
    "state_distinction_surfaces",
    "explicit_commit_or_handoff_boundary",
)
_RENDERED_BINDING_TARGETS = (
    "commit_or_approval_gates",
    "advisory_vs_authoritative_actions",
    "disabled_or_unavailable_gated_states",
    "required_evidence_reachability_anchors",
    "salience_bearing_warning_status_and_diagnostic_surfaces",
)
_REQUIRED_EPISTEMIC_STATES = (
    "loading",
    "draft",
    "candidate",
    "validated",
    "authoritative",
    "conflicted",
    "stale",
    "ambiguous",
)


class UXGovernanceEvidenceError(ValueError):
    pass


class MaterializedUXGovernanceEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    path: str = Field(min_length=1)
    hash: str = Field(min_length=64, max_length=64)
    payload: dict[str, Any]


class V36AUXDomainMorphIREvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V36A_UX_DOMAIN_MORPH_IR_EVIDENCE_SCHEMA, alias="schema")
    contract_source: str = V36A_UX_DOMAIN_MORPH_IR_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    ux_domain_packet_schema_path: str = Field(min_length=1)
    ux_domain_packet_schema_hash: str = Field(min_length=64, max_length=64)
    ux_morph_ir_schema_path: str = Field(min_length=1)
    ux_morph_ir_schema_hash: str = Field(min_length=64, max_length=64)
    ux_domain_packet_reference_path: str = Field(min_length=1)
    ux_domain_packet_reference_hash: str = Field(min_length=64, max_length=64)
    ux_morph_ir_reference_path: str = Field(min_length=1)
    ux_morph_ir_reference_hash: str = Field(min_length=64, max_length=64)
    approved_profile_table_path: str = Field(min_length=1)
    approved_profile_table_hash: str = Field(min_length=64, max_length=64)
    same_context_reachability_glossary_path: str = Field(min_length=1)
    same_context_reachability_glossary_hash: str = Field(min_length=64, max_length=64)
    adeu_split_vocabulary_frozen: bool
    approved_profile_table_frozen: bool
    approved_profile_cardinality_verified: bool
    reference_instance_binding_verified: bool
    reference_instance_required_and_present: bool
    deterministic_serialization_verified: bool
    no_free_form_ui_codegen_without_ir_preserved: bool
    ui_artifacts_may_express_but_may_not_mint_authority_preserved: bool
    v35_authority_baseline_unchanged: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v60: bool
    notes: str = Field(min_length=1)


class V36BSurfaceProjectionInteractionEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(
        default=V36B_SURFACE_PROJECTION_INTERACTION_EVIDENCE_SCHEMA,
        alias="schema",
    )
    contract_source: str = V36B_SURFACE_PROJECTION_INTERACTION_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    ux_surface_projection_schema_path: str = Field(min_length=1)
    ux_surface_projection_schema_hash: str = Field(min_length=64, max_length=64)
    ux_interaction_contract_schema_path: str = Field(min_length=1)
    ux_interaction_contract_schema_hash: str = Field(min_length=64, max_length=64)
    ux_surface_projection_reference_path: str = Field(min_length=1)
    ux_surface_projection_reference_hash: str = Field(min_length=64, max_length=64)
    ux_interaction_contract_reference_path: str = Field(min_length=1)
    ux_interaction_contract_reference_hash: str = Field(min_length=64, max_length=64)
    projection_interaction_binding_verified: bool
    v36a_reference_pair_binding_verified: bool
    reference_profile_id_verified_against_v36a_table: bool
    authoritative_gate_source_resolution_verified: bool
    forbidden_authoritative_gate_sources_rejected: bool
    stable_provenance_hooks_verified: bool
    implementation_observable_bindings_verified: bool
    binding_identifier_stability_verified: bool
    advisory_authoritative_boundary_preserved: bool
    no_glossary_shadowing_verified: bool
    evidence_before_commit_rule_preserved: bool
    runtime_visible_consequence_epistemic_boundary_preserved: bool
    no_visual_authority_inflation_preserved: bool
    v36a_substrate_consumed_without_drift: bool
    v35_authority_baseline_unchanged: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v61: bool
    notes: str = Field(min_length=1)


class V36CRenderedRouteLaneCluster(BaseModel):
    model_config = ConfigDict(extra="forbid")

    lane_id: str = Field(min_length=1)
    cluster_ids: list[str] = Field(min_length=1)


class V36CRenderedReferenceSurfaceContract(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(
        default="v36c_rendered_reference_surface_contract@1",
        alias="schema",
    )
    reference_surface_family: str = Field(min_length=1)
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: str = Field(min_length=1)
    route_id: str = Field(min_length=1)
    route_path: str = Field(min_length=1)
    rendered_surface_snapshot_kind: str = Field(min_length=1)
    route_payload_parity_mode: str = Field(min_length=1)
    diagnostics_lane_mode: str = Field(min_length=1)
    diagnostics_lane_notice: str = Field(min_length=1)
    diagnostics_lane_read_only_notice: str = Field(min_length=1)
    commit_boundary_id: str = Field(min_length=1)
    commit_boundary_notice: str = Field(min_length=1)
    truth_source_policy: str = Field(min_length=1)
    truth_source_notice: str = Field(min_length=1)
    epistemic_state_descriptions: dict[str, str] = Field(min_length=1)
    lane_cluster_rendering: list[V36CRenderedRouteLaneCluster] = Field(min_length=1)
    rendered_provenance_exposures: dict[str, list[str]] = Field(min_length=1)
    rendered_binding_exposures: dict[str, list[str]] = Field(min_length=1)


class V36CRenderedSurfaceSemanticSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V36C_RENDERED_SNAPSHOT_SCHEMA, alias="schema")
    route_contract_path: str = Field(min_length=1)
    route_contract_hash: str = Field(min_length=64, max_length=64)
    route_id: str = Field(min_length=1)
    route_path: str = Field(min_length=1)
    reference_surface_family: str = Field(min_length=1)
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: str = Field(min_length=1)
    rendered_surface_snapshot_kind: str = Field(min_length=1)
    route_payload_parity_mode: str = Field(min_length=1)
    diagnostics_lane_mode: str = Field(min_length=1)
    diagnostics_lane_notice: str = Field(min_length=1)
    diagnostics_lane_read_only_notice: str = Field(min_length=1)
    truth_source_policy: str = Field(min_length=1)
    truth_source_notice: str = Field(min_length=1)
    commit_boundary_id: str = Field(min_length=1)
    commit_boundary_notice: str = Field(min_length=1)
    required_evidence_lane_ids: list[str] = Field(min_length=1)
    required_evidence_region_ids: list[str] = Field(min_length=1)
    route_change_required: bool
    commit_or_destructive_action_required: bool
    same_context_reachability_glossary: dict[str, Any]
    rendered_region_ids: list[str] = Field(min_length=1)
    rendered_lane_ids: list[str] = Field(min_length=1)
    lane_cluster_rendering: list[V36CRenderedRouteLaneCluster] = Field(min_length=1)
    epistemic_state_descriptions: dict[str, str] = Field(min_length=1)
    state_surfaces: list[dict[str, str]] = Field(min_length=1)
    advisory_action_ids: list[str] = Field(min_length=1)
    authoritative_or_gated_action_ids: list[str] = Field(min_length=1)


class V36CRenderedSurfaceTargetManifestEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    target_ref: str = Field(min_length=1)
    binding_ids: list[str]
    binding_target_kinds: list[str]
    binding_tokens: list[str]
    hook_ids: list[str]
    hook_target_kinds: list[str]


class V36CRenderedSurfaceBindingManifest(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V36C_BINDING_MANIFEST_SCHEMA, alias="schema")
    route_contract_path: str = Field(min_length=1)
    route_contract_hash: str = Field(min_length=64, max_length=64)
    route_id: str = Field(min_length=1)
    route_path: str = Field(min_length=1)
    reference_surface_family: str = Field(min_length=1)
    reference_instance_id: str = Field(min_length=1)
    approved_profile_id: str = Field(min_length=1)
    rendered_provenance_exposures: dict[str, list[str]] = Field(min_length=1)
    rendered_binding_exposures: dict[str, list[str]] = Field(min_length=1)
    stable_provenance_hooks: list[dict[str, Any]] = Field(min_length=1)
    implementation_observable_bindings: list[dict[str, Any]] = Field(min_length=1)
    target_manifest: list[V36CRenderedSurfaceTargetManifestEntry] = Field(min_length=1)


class V36CArtifactInspectorReferenceSurfaceEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(
        default=V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_EVIDENCE_SCHEMA,
        alias="schema",
    )
    contract_source: str = V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    rendered_surface_route_id: str = Field(min_length=1)
    rendered_surface_route_path: str = Field(min_length=1)
    rendered_surface_snapshot_kind: str = Field(min_length=1)
    rendered_surface_snapshot_path: str = Field(min_length=1)
    rendered_surface_snapshot_hash: str = Field(min_length=64, max_length=64)
    implementation_binding_manifest_path: str = Field(min_length=1)
    implementation_binding_manifest_hash: str = Field(min_length=64, max_length=64)
    route_payload_parity_verified_as_presentational_only_transform: bool
    v36a_reference_pair_consumed_without_drift: bool
    v36b_reference_pair_consumed_without_drift: bool
    reference_profile_id_verified_against_v36a_table: bool
    epistemic_state_rendering_verified: bool
    advisory_authoritative_boundary_rendering_verified: bool
    same_context_evidence_visibility_preserved: bool
    no_route_level_glossary_shadowing_verified: bool
    explicit_commit_or_handoff_boundary_visible: bool
    stable_provenance_hooks_exposed: bool
    stable_provenance_hook_targets_exposed: bool
    implementation_observable_bindings_exposed: bool
    non_authoritative_event_or_worker_content_not_rendered_as_accepted_truth: bool
    no_visual_authority_inflation_preserved: bool
    no_unrelated_route_rewrite_detected: bool
    no_v36d_diagnostics_engine_widening: bool
    no_v36e_compiler_widening: bool
    v35_authority_baseline_unchanged: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v62: bool
    notes: str = Field(min_length=1)


class V36DMorphDiagnosticsConformanceEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(
        default=V36D_MORPH_DIAGNOSTICS_CONFORMANCE_EVIDENCE_SCHEMA,
        alias="schema",
    )
    contract_source: str = V36D_MORPH_DIAGNOSTICS_CONFORMANCE_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    ux_morph_diagnostics_schema_path: str = Field(min_length=1)
    ux_morph_diagnostics_schema_hash: str = Field(min_length=64, max_length=64)
    ux_conformance_report_schema_path: str = Field(min_length=1)
    ux_conformance_report_schema_hash: str = Field(min_length=64, max_length=64)
    ux_morph_diagnostics_reference_path: str = Field(min_length=1)
    ux_morph_diagnostics_reference_hash: str = Field(min_length=64, max_length=64)
    ux_conformance_report_reference_path: str = Field(min_length=1)
    ux_conformance_report_reference_hash: str = Field(min_length=64, max_length=64)
    reference_binding_tuple_equality_verified: bool
    v36a_reference_pair_consumed_without_drift: bool
    v36b_reference_pair_consumed_without_drift: bool
    v36c_rendered_surface_consumed_without_drift: bool
    reference_profile_id_verified_against_v36a_table: bool
    diagnostics_severity_taxonomy_verified: bool
    diagnostic_finding_structure_verified: bool
    diagnostics_provenance_pointer_resolution_verified: bool
    rendered_surface_assertion_bridge_verified: bool
    rendered_surface_assertion_bridge_no_fresh_heuristics_verified: bool
    conformance_aggregation_rule_verified: bool
    conformance_report_structure_verified: bool
    conformance_report_diagnostics_derivation_verified: bool
    destructive_confirmation_gap_detectable: bool
    same_context_reachability_violation_detectable: bool
    utility_posture_conflict_detectable: bool
    requested_profile_command_grammar_conflict_detectable: bool
    competing_primary_actions_detectable: bool
    provisional_authoritative_styling_violation_detectable: bool
    advisory_authoritative_boundary_collapse_detectable: bool
    recovery_path_gap_detectable: bool
    no_taste_engine_drift_detected: bool
    no_event_stream_or_worker_prose_truth_substitution: bool
    diagnostic_truth_substitution_rejected: bool
    v35_authority_baseline_unchanged: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v63: bool
    notes: str = Field(min_length=1)


def _canonical_json(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_canonical_json(value: object) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _pretty_canonical_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _resolve_repo_relative_path(
    *,
    root: Path,
    path_text: str,
    field_name: str,
    required_prefix: str | None = None,
) -> Path:
    if not path_text:
        raise UXGovernanceEvidenceError(f"{field_name} must not be empty")
    relative = Path(path_text)
    if relative.is_absolute():
        raise UXGovernanceEvidenceError(f"{field_name} must be repo-relative")
    if required_prefix is not None and not path_text.startswith(required_prefix):
        raise UXGovernanceEvidenceError(
            f"{field_name} must stay under the {required_prefix!r} subtree"
        )
    if any(part in {"", ".", ".."} for part in relative.parts):
        raise UXGovernanceEvidenceError(f"{field_name} contains invalid path components")
    resolved = (root / relative).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise UXGovernanceEvidenceError(f"{field_name} must stay within repository root") from exc
    return resolved


def _load_json_dict(*, path: Path, field_name: str) -> tuple[str, dict[str, Any]]:
    if not path.is_file():
        raise UXGovernanceEvidenceError(f"{field_name} does not exist")
    text = path.read_text(encoding="utf-8")
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        raise UXGovernanceEvidenceError(f"{field_name} is not valid JSON") from exc
    if not isinstance(payload, dict):
        raise UXGovernanceEvidenceError(f"{field_name} must contain a JSON object")
    return text, payload


def _validate_pretty_canonical_serialization(
    *,
    text: str,
    payload: dict[str, Any],
    field_name: str,
) -> None:
    expected = _pretty_canonical_json(payload)
    if text != expected:
        raise UXGovernanceEvidenceError(
            f"{field_name} must use the frozen pretty canonical JSON writer profile"
        )


def _load_stop_gate_metrics(*, path: Path, field_name: str) -> dict[str, Any]:
    _text, payload = _load_json_dict(path=path, field_name=field_name)
    if payload.get("schema") != STOP_GATE_METRICS_SCHEMA:
        raise UXGovernanceEvidenceError(f"{field_name} must use {STOP_GATE_METRICS_SCHEMA}")
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict) or not all(isinstance(key, str) for key in metrics):
        raise UXGovernanceEvidenceError(f"{field_name} metrics must be an object with string keys")
    return payload


def _load_validated_model(
    *,
    path: Path,
    field_name: str,
    model_type: type[ModelT],
) -> tuple[dict[str, Any], ModelT]:
    text, payload = _load_json_dict(path=path, field_name=field_name)
    _validate_pretty_canonical_serialization(text=text, payload=payload, field_name=field_name)
    try:
        model = model_type.model_validate(payload)
    except ValidationError as exc:
        for error in exc.errors():
            loc = tuple(error.get("loc", ()))
            if loc == _FREE_FORM_POLICY_LOC:
                raise UXGovernanceEvidenceError("free-form UI codegen bypass detected") from exc
            if loc == _AUTHORITY_MINTING_POLICY_LOC:
                raise UXGovernanceEvidenceError("authority-minting drift detected") from exc
        raise UXGovernanceEvidenceError(f"{field_name} is invalid") from exc
    return payload, model


def _load_frozen_schema(
    *,
    path: Path,
    field_name: str,
    model_type: type[BaseModel],
) -> dict[str, Any]:
    text, payload = _load_json_dict(path=path, field_name=field_name)
    _validate_pretty_canonical_serialization(text=text, payload=payload, field_name=field_name)
    expected = model_type.model_json_schema(by_alias=True)
    if payload != expected:
        raise UXGovernanceEvidenceError(f"{field_name} does not match the frozen exported schema")
    return payload


def _anchor_resolves_in_text(*, text: str, anchor: str) -> bool:
    return anchor in text


def _validation_error_message(error: dict[str, Any]) -> str:
    message = str(error.get("msg", ""))
    prefix = "Value error, "
    if message.startswith(prefix):
        return message[len(prefix) :]
    return message


def _raise_v36b_validation_error(*, field_name: str, exc: ValidationError) -> None:
    for error in exc.errors():
        loc = tuple(error.get("loc", ()))
        message = _validation_error_message(error)
        input_value = error.get("input")
        if "same_context_reachability_glossary" in loc:
            raise UXGovernanceEvidenceError(
                "projection must consume the released v36a same-context glossary without shadowing"
            ) from exc
        if loc == ("evidence_before_commit", "route_change_required"):
            raise UXGovernanceEvidenceError(
                "rendered surface cannot require a route change before required evidence"
            ) from exc
        if loc == ("evidence_before_commit", "commit_or_destructive_action_required"):
            raise UXGovernanceEvidenceError(
                "rendered surface cannot require a commit or destructive action before evidence"
            ) from exc
        if loc == _FREE_FORM_POLICY_LOC:
            raise UXGovernanceEvidenceError("free-form UI codegen bypass detected") from exc
        if loc == _AUTHORITY_MINTING_POLICY_LOC:
            raise UXGovernanceEvidenceError("authority-minting drift detected") from exc
        if loc == _VISUAL_AUTHORITY_INFLATION_POLICY_LOC:
            raise UXGovernanceEvidenceError("visual authority inflation drift detected") from exc
        if (
            isinstance(input_value, str)
            and input_value in _FORBIDDEN_AUTHORITATIVE_GATE_SOURCE_VALUES
        ):
            raise UXGovernanceEvidenceError("forbidden authoritative gate source detected") from exc
        if "requires authoritative_gate_source" in message:
            raise UXGovernanceEvidenceError("authoritative_gate_source resolution invalid") from exc
        if "must not carry authoritative_gate_source" in message:
            raise UXGovernanceEvidenceError(
                "advisory/authoritative boundary collapse detected"
            ) from exc
        if message in {
            "runtime_visible_consequence must remain epistemic and must not overstate success",
            "stable provenance hook id must match the frozen deterministic format",
            "implementation binding id must match the frozen deterministic format",
            "stable_provenance_hooks target_ref must bind to bundle reference_instance_id",
            _IMPLEMENTATION_BINDING_REFERENCE_INSTANCE_ERROR,
        }:
            raise UXGovernanceEvidenceError(message) from exc
    raise UXGovernanceEvidenceError(f"{field_name} is invalid") from exc


def _load_validated_v36b_model(
    *,
    path: Path,
    field_name: str,
    model_type: type[ModelT],
) -> tuple[dict[str, Any], ModelT]:
    text, payload = _load_json_dict(path=path, field_name=field_name)
    _validate_pretty_canonical_serialization(text=text, payload=payload, field_name=field_name)
    try:
        model = model_type.model_validate(payload)
    except ValidationError as exc:
        _raise_v36b_validation_error(field_name=field_name, exc=exc)
    return payload, model


def _raise_v36d_validation_error(*, field_name: str, exc: ValidationError) -> None:
    for error in exc.errors():
        loc = tuple(error.get("loc", ()))
        message = _validation_error_message(error)
        if loc == _FREE_FORM_POLICY_LOC:
            raise UXGovernanceEvidenceError("free-form UI codegen bypass detected") from exc
        if loc == _AUTHORITY_MINTING_POLICY_LOC:
            raise UXGovernanceEvidenceError("authority-minting drift detected") from exc
        if loc == _VISUAL_AUTHORITY_INFLATION_POLICY_LOC:
            raise UXGovernanceEvidenceError("visual authority inflation drift detected") from exc
        if "severity_taxonomy" in loc:
            raise UXGovernanceEvidenceError("diagnostics severity taxonomy drift detected") from exc
        if "seeded_violation_families" in loc or "seeded_violation_families" in message:
            raise UXGovernanceEvidenceError(
                "seeded violation family coverage drift detected"
            ) from exc
        if "rendered_surface_assertion_inputs_used" in loc:
            raise UXGovernanceEvidenceError(
                "rendered surface assertion bridge drift detected"
            ) from exc
        if "event streams or worker prose" in message and (
            "supporting_evidence_refs" in message or "source_path" in message
        ):
            raise UXGovernanceEvidenceError("diagnostic truth substitution detected") from exc
        if loc == ("derivation_metadata", "fresh_route_local_heuristics_introduced"):
            raise UXGovernanceEvidenceError(
                "rendered surface assertion bridge introduced fresh route-local heuristics"
            ) from exc
        if loc == ("derivation_metadata", "rendered_surface_assertion_inputs"):
            raise UXGovernanceEvidenceError(
                "rendered surface assertion bridge drift detected"
            ) from exc
        if loc == ("derivation_metadata", "canonical_artifact_truth_only"):
            raise UXGovernanceEvidenceError("conformance truth-source drift detected") from exc
        if loc == ("derivation_metadata", "event_streams_and_worker_prose_provenance_only"):
            raise UXGovernanceEvidenceError("conformance truth-source drift detected") from exc
        if loc == ("derivation_metadata", "typed_summary_only"):
            raise UXGovernanceEvidenceError(
                "conformance report must remain a typed summary"
            ) from exc
        if loc == ("supporting_finding_ids",) and "sorted distinct" in message:
            raise UXGovernanceEvidenceError(
                "conformance report supporting finding ids drift detected"
            ) from exc
    raise UXGovernanceEvidenceError(f"{field_name} is invalid") from exc


def _load_validated_v36d_model(
    *,
    path: Path,
    field_name: str,
    model_type: type[ModelT],
) -> tuple[dict[str, Any], ModelT]:
    text, payload = _load_json_dict(path=path, field_name=field_name)
    _validate_pretty_canonical_serialization(text=text, payload=payload, field_name=field_name)
    try:
        model = model_type.model_validate(payload)
    except ValidationError as exc:
        _raise_v36d_validation_error(field_name=field_name, exc=exc)
    return payload, model


def _validate_authoritative_gate_sources(
    *,
    repo_root: Path,
    interaction_contract: UXInteractionContract,
) -> None:
    for entry in interaction_contract.interaction_entries:
        requires_gate = (
            entry.authoritative or entry.gated or entry.committing or entry.approval_bearing
        )
        if not requires_gate:
            if entry.authoritative_gate_source is not None:
                raise UXGovernanceEvidenceError("advisory/authoritative boundary collapse detected")
            continue
        gate_source = entry.authoritative_gate_source
        if gate_source is None:
            raise UXGovernanceEvidenceError("authoritative_gate_source resolution invalid")
        path_text, separator, anchor = gate_source.source_ref.partition("#")
        if not separator or not anchor:
            raise UXGovernanceEvidenceError(
                "authoritative_gate_source source_ref must resolve to a committed docs anchor"
            )
        source_file = _resolve_repo_relative_path(
            root=repo_root,
            path_text=path_text,
            field_name="authoritative_gate_source.source_ref",
            required_prefix="docs/",
        )
        if not source_file.is_file():
            raise UXGovernanceEvidenceError(
                "authoritative_gate_source source_ref must resolve to a committed docs anchor"
            )
        source_text = source_file.read_text(encoding="utf-8")
        if not _anchor_resolves_in_text(text=source_text, anchor=anchor):
            raise UXGovernanceEvidenceError(
                "authoritative_gate_source source_ref must resolve to a committed docs anchor"
            )
        if gate_source.source_kind == "accepted_v35_runtime_authority_artifact":
            if path_text != "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md":
                raise UXGovernanceEvidenceError(
                    "accepted_v35_runtime_authority_artifact must resolve to the frozen "
                    "v35 runtime authority baseline"
                )


def _v36a_substrate_signature_payload(
    *,
    ux_domain_packet_reference_path: str,
    ux_domain_packet_reference_hash: str,
    ux_morph_ir_reference_path: str,
    ux_morph_ir_reference_hash: str,
    approved_profile_table_path: str,
    approved_profile_table_hash: str,
    same_context_reachability_glossary_path: str,
    same_context_reachability_glossary_hash: str,
) -> dict[str, str]:
    return {
        "approved_profile_table_hash": approved_profile_table_hash,
        "approved_profile_table_path": approved_profile_table_path,
        "same_context_reachability_glossary_hash": same_context_reachability_glossary_hash,
        "same_context_reachability_glossary_path": same_context_reachability_glossary_path,
        "ux_domain_packet_reference_hash": ux_domain_packet_reference_hash,
        "ux_domain_packet_reference_path": ux_domain_packet_reference_path,
        "ux_morph_ir_reference_hash": ux_morph_ir_reference_hash,
        "ux_morph_ir_reference_path": ux_morph_ir_reference_path,
    }


def _v36b_substrate_signature_payload(
    *,
    ux_surface_projection_reference_path: str,
    ux_surface_projection_reference_hash: str,
    ux_interaction_contract_reference_path: str,
    ux_interaction_contract_reference_hash: str,
) -> dict[str, str]:
    return {
        "ux_interaction_contract_reference_hash": ux_interaction_contract_reference_hash,
        "ux_interaction_contract_reference_path": ux_interaction_contract_reference_path,
        "ux_surface_projection_reference_hash": ux_surface_projection_reference_hash,
        "ux_surface_projection_reference_path": ux_surface_projection_reference_path,
    }


def _v36c_substrate_signature_payload(
    *,
    rendered_reference_surface_contract_path: str,
    rendered_reference_surface_contract_hash: str,
    rendered_surface_snapshot_path: str,
    rendered_surface_snapshot_hash: str,
    implementation_binding_manifest_path: str,
    implementation_binding_manifest_hash: str,
    rendered_reference_surface_evidence_path: str,
    rendered_reference_surface_evidence_hash: str,
) -> dict[str, str]:
    return {
        "implementation_binding_manifest_hash": implementation_binding_manifest_hash,
        "implementation_binding_manifest_path": implementation_binding_manifest_path,
        "rendered_reference_surface_contract_hash": rendered_reference_surface_contract_hash,
        "rendered_reference_surface_contract_path": rendered_reference_surface_contract_path,
        "rendered_reference_surface_evidence_hash": rendered_reference_surface_evidence_hash,
        "rendered_reference_surface_evidence_path": rendered_reference_surface_evidence_path,
        "rendered_surface_snapshot_hash": rendered_surface_snapshot_hash,
        "rendered_surface_snapshot_path": rendered_surface_snapshot_path,
    }


def _validate_v36b_reference_canonicalization(
    *,
    surface_projection_payload: dict[str, Any],
    interaction_contract_payload: dict[str, Any],
) -> None:
    if (
        canonicalize_ux_surface_projection_payload(surface_projection_payload)
        != surface_projection_payload
    ):
        raise UXGovernanceEvidenceError(
            "ux_surface_projection_reference_path must serialize canonically without drift"
        )
    if (
        canonicalize_ux_interaction_contract_payload(interaction_contract_payload)
        != interaction_contract_payload
    ):
        raise UXGovernanceEvidenceError(
            "ux_interaction_contract_reference_path must serialize canonically without drift"
        )


def _validate_v36d_reference_canonicalization(
    *,
    diagnostics_payload: dict[str, Any],
    conformance_report_payload: dict[str, Any],
) -> None:
    if canonicalize_ux_morph_diagnostics_payload(diagnostics_payload) != diagnostics_payload:
        raise UXGovernanceEvidenceError(
            "ux_morph_diagnostics_reference_path must serialize canonically without drift"
        )
    if (
        canonicalize_ux_conformance_report_payload(conformance_report_payload)
        != conformance_report_payload
    ):
        raise UXGovernanceEvidenceError(
            "ux_conformance_report_reference_path must serialize canonically without drift"
        )


def _resolve_artifact_ref_path(
    *,
    repo_root: Path,
    ref: str,
    field_name: str,
) -> Path:
    path_text = ref.split("#", 1)[0]
    return _resolve_repo_relative_path(
        root=repo_root,
        path_text=path_text,
        field_name=field_name,
    )


def _build_v36d_consumed_artifact_schema_map(
    *,
    ux_domain_packet_schema_path: str,
    ux_morph_ir_schema_path: str,
    ux_surface_projection_schema_path: str,
    ux_interaction_contract_schema_path: str,
    ux_domain_packet_reference_path: str,
    ux_morph_ir_reference_path: str,
    ux_surface_projection_reference_path: str,
    ux_interaction_contract_reference_path: str,
    rendered_reference_surface_contract_path: str,
    rendered_surface_snapshot_path: str,
    implementation_binding_manifest_path: str,
    rendered_reference_surface_evidence_path: str,
) -> dict[str, str]:
    return {
        ux_domain_packet_schema_path: UX_DOMAIN_PACKET_SCHEMA,
        ux_domain_packet_reference_path: UX_DOMAIN_PACKET_SCHEMA,
        ux_morph_ir_schema_path: UX_MORPH_IR_SCHEMA,
        ux_morph_ir_reference_path: UX_MORPH_IR_SCHEMA,
        ux_surface_projection_schema_path: UX_SURFACE_PROJECTION_SCHEMA,
        ux_surface_projection_reference_path: UX_SURFACE_PROJECTION_SCHEMA,
        ux_interaction_contract_schema_path: UX_INTERACTION_CONTRACT_SCHEMA,
        ux_interaction_contract_reference_path: UX_INTERACTION_CONTRACT_SCHEMA,
        rendered_reference_surface_contract_path: V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_SCHEMA,
        rendered_surface_snapshot_path: V36C_RENDERED_REFERENCE_SURFACE_SNAPSHOT_SCHEMA,
        implementation_binding_manifest_path: (
            V36C_RENDERED_REFERENCE_SURFACE_BINDING_MANIFEST_SCHEMA
        ),
        rendered_reference_surface_evidence_path: (
            V36C_ARTIFACT_INSPECTOR_REFERENCE_SURFACE_EVIDENCE_SCHEMA
        ),
    }


def _validate_v36d_provenance_resolution(
    *,
    repo_root: Path,
    diagnostics: UXMorphDiagnostics,
    consumed_artifact_schema_map: dict[str, str],
) -> None:
    for finding in diagnostics.findings:
        for provenance_pointer in finding.provenance_pointers:
            _resolve_artifact_ref_path(
                repo_root=repo_root,
                ref=provenance_pointer.source_path,
                field_name="diagnostics.provenance_pointers.source_path",
            )
            source_path = provenance_pointer.source_path.split("#", 1)[0]
            if (
                consumed_artifact_schema_map.get(source_path)
                != provenance_pointer.source_schema
            ):
                raise UXGovernanceEvidenceError(
                    "diagnostics provenance pointers must resolve to the "
                    "consumed canonical artifacts"
                )
        for evidence_ref in finding.supporting_evidence_refs:
            _resolve_artifact_ref_path(
                repo_root=repo_root,
                ref=evidence_ref,
                field_name="diagnostics.findings.supporting_evidence_refs",
            )
            evidence_path = evidence_ref.split("#", 1)[0]
            if evidence_path not in consumed_artifact_schema_map:
                raise UXGovernanceEvidenceError(
                    "diagnostic supporting evidence refs must resolve to the "
                    "consumed canonical artifacts"
                )


def _normalize_text(text: str) -> str:
    return " ".join(text.lower().split())


def _strip_reference_instance_prefix(target_ref: str) -> str:
    _reference_instance_id, separator, suffix = target_ref.partition(":")
    if not separator or not suffix:
        raise UXGovernanceEvidenceError("target_ref must contain a reference_instance_id prefix")
    return suffix


def _assert_minimum_coverage(
    *,
    label: str,
    actual: Iterable[str],
    required: Iterable[str],
) -> None:
    actual_set = set(actual)
    for required_value in required:
        if required_value not in actual_set:
            raise UXGovernanceEvidenceError(
                f"{label} is missing required target {required_value!r}"
            )


def _assert_exposure_refs_present(
    *,
    label: str,
    actual_refs: Iterable[str],
    expected_refs: Iterable[str],
) -> None:
    _assert_minimum_coverage(
        label=label,
        actual=actual_refs,
        required=expected_refs,
    )


def _build_lane_cluster_map(
    surface_projection: UXSurfaceProjection,
) -> dict[str, list[str]]:
    by_lane: dict[str, list[str]] = {}
    for cluster in surface_projection.action_clusters:
        by_lane.setdefault(cluster.lane_id, []).append(cluster.cluster_id)
    return by_lane


def _combined_provenance_hooks(
    *,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
) -> list[dict[str, Any]]:
    hooks = [
        *(hook.model_dump(mode="json") for hook in surface_projection.stable_provenance_hooks),
        *(hook.model_dump(mode="json") for hook in interaction_contract.stable_provenance_hooks),
    ]
    return sorted(hooks, key=lambda hook: str(hook["hook_id"]))


def _combined_implementation_bindings(
    *,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
) -> list[dict[str, Any]]:
    bindings = [
        *(
            binding.model_dump(mode="json")
            for binding in surface_projection.implementation_observable_bindings
        ),
        *(
            binding.model_dump(mode="json")
            for binding in interaction_contract.implementation_observable_bindings
        ),
    ]
    return sorted(bindings, key=lambda binding: str(binding["binding_id"]))


def _build_v36c_target_manifest(
    *,
    provenance_hooks: list[dict[str, Any]],
    implementation_bindings: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    by_target: dict[str, dict[str, Any]] = {}

    def ensure(target_ref: str) -> dict[str, Any]:
        existing = by_target.get(target_ref)
        if existing is not None:
            return existing
        created = {
            "target_ref": target_ref,
            "binding_ids": [],
            "binding_target_kinds": [],
            "binding_tokens": [],
            "hook_ids": [],
            "hook_target_kinds": [],
        }
        by_target[target_ref] = created
        return created

    for hook in provenance_hooks:
        target = ensure(str(hook["target_ref"]))
        target["hook_ids"].append(str(hook["hook_id"]))
        target["hook_target_kinds"].append(str(hook["target_kind"]))
    for binding in implementation_bindings:
        target = ensure(str(binding["target_ref"]))
        target["binding_ids"].append(str(binding["binding_id"]))
        target["binding_target_kinds"].append(str(binding["target_kind"]))
        target["binding_tokens"].append(str(binding["binding_token"]))

    payload: list[dict[str, Any]] = []
    for target_ref in sorted(by_target):
        entry = by_target[target_ref]
        payload.append(
            {
                "target_ref": target_ref,
                "binding_ids": sorted(entry["binding_ids"]),
                "binding_target_kinds": sorted(entry["binding_target_kinds"]),
                "binding_tokens": sorted(entry["binding_tokens"]),
                "hook_ids": sorted(entry["hook_ids"]),
                "hook_target_kinds": sorted(entry["hook_target_kinds"]),
            }
        )
    return payload


def _validate_v36c_rendered_surface_contract(
    *,
    rendered_surface_contract: V36CRenderedReferenceSurfaceContract,
    domain_packet: UXDomainPacket,
    morph_ir: UXMorphIR,
    approved_profile_table: V36AFirstFamilyApprovedProfileTable,
    same_context_glossary: V36ASameContextReachabilityGlossary,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
) -> None:
    if rendered_surface_contract.route_id != V36C_RENDERED_ROUTE_ID:
        raise UXGovernanceEvidenceError("rendered surface contract route_id drift detected")
    if rendered_surface_contract.route_path != V36C_RENDERED_ROUTE_PATH:
        raise UXGovernanceEvidenceError("rendered surface contract route_path drift detected")
    if rendered_surface_contract.route_payload_parity_mode != V36C_ROUTE_PAYLOAD_PARITY_MODE:
        raise UXGovernanceEvidenceError("rendered surface contract parity mode drift detected")
    if rendered_surface_contract.diagnostics_lane_mode != V36C_DIAGNOSTICS_LANE_MODE:
        raise UXGovernanceEvidenceError("diagnostics lane mode drift detected")
    if rendered_surface_contract.truth_source_policy != V36C_TRUTH_SOURCE_POLICY:
        raise UXGovernanceEvidenceError("truth source policy drift detected")
    if (
        rendered_surface_contract.rendered_surface_snapshot_kind
        != V36C_RENDERED_SURFACE_SNAPSHOT_KIND
    ):
        raise UXGovernanceEvidenceError("rendered surface snapshot kind drift detected")
    for label, candidate in (
        ("ux_domain_packet@1", domain_packet),
        ("ux_morph_ir@1", morph_ir),
        ("ux_surface_projection@1", surface_projection),
        ("ux_interaction_contract@1", interaction_contract),
    ):
        if rendered_surface_contract.reference_surface_family != candidate.reference_surface_family:
            raise UXGovernanceEvidenceError(
                f"rendered surface contract reference_surface_family drifted from {label}"
            )
        if rendered_surface_contract.reference_instance_id != candidate.reference_instance_id:
            raise UXGovernanceEvidenceError(
                f"rendered surface contract reference_instance_id drifted from {label}"
            )
        if rendered_surface_contract.approved_profile_id != candidate.approved_profile_id:
            raise UXGovernanceEvidenceError(
                f"rendered surface contract approved_profile_id drifted from {label}"
            )
    if (
        rendered_surface_contract.approved_profile_id
        != approved_profile_table.canonical_reference_profile_id
    ):
        raise UXGovernanceEvidenceError(
            "rendered surface contract approved_profile_id must use the canonical v36a profile"
        )
    if rendered_surface_contract.approved_profile_id not in {
        profile.profile_id for profile in approved_profile_table.profiles
    }:
        raise UXGovernanceEvidenceError(
            "rendered surface contract approved_profile_id must be present in the v36a table"
        )
    if (
        rendered_surface_contract.reference_surface_family
        != same_context_glossary.reference_surface_family
    ):
        raise UXGovernanceEvidenceError(
            "rendered surface contract reference surface family drift detected"
        )

    lane_cluster_map = _build_lane_cluster_map(surface_projection)
    declared_lane_ids = {
        cluster_rendering.lane_id
        for cluster_rendering in rendered_surface_contract.lane_cluster_rendering
    }
    if declared_lane_ids != set(lane_cluster_map):
        raise UXGovernanceEvidenceError("rendered lane cluster coverage drift detected")
    for cluster_rendering in rendered_surface_contract.lane_cluster_rendering:
        actual = lane_cluster_map.get(cluster_rendering.lane_id, [])
        if actual != cluster_rendering.cluster_ids:
            raise UXGovernanceEvidenceError(
                f"rendered lane cluster mapping drift detected for {cluster_rendering.lane_id!r}"
            )

    _assert_minimum_coverage(
        label="rendered provenance exposure targets",
        actual=rendered_surface_contract.rendered_provenance_exposures.keys(),
        required=_RENDERED_PROVENANCE_TARGETS,
    )
    _assert_minimum_coverage(
        label="rendered binding exposure targets",
        actual=rendered_surface_contract.rendered_binding_exposures.keys(),
        required=_RENDERED_BINDING_TARGETS,
    )
    for refs in rendered_surface_contract.rendered_provenance_exposures.values():
        if not refs:
            raise UXGovernanceEvidenceError("rendered provenance exposure refs must not be empty")
    for refs in rendered_surface_contract.rendered_binding_exposures.values():
        if not refs:
            raise UXGovernanceEvidenceError("rendered binding exposure refs must not be empty")

    _assert_exposure_refs_present(
        label="rendered region exposure refs",
        actual_refs=rendered_surface_contract.rendered_provenance_exposures["rendered_regions"],
        expected_refs=(region.region_id for region in surface_projection.regions),
    )
    _assert_exposure_refs_present(
        label="authority-bearing control exposure refs",
        actual_refs=rendered_surface_contract.rendered_provenance_exposures[
            "authority_bearing_controls"
        ],
        expected_refs=(
            entry.interaction_id
            for entry in interaction_contract.interaction_entries
            if entry.authoritative or entry.gated or entry.approval_bearing
        ),
    )
    _assert_exposure_refs_present(
        label="evidence-bearing region exposure refs",
        actual_refs=rendered_surface_contract.rendered_provenance_exposures[
            "evidence_bearing_regions"
        ],
        expected_refs=(
            [
                *surface_projection.evidence_before_commit.required_evidence_region_ids,
                *surface_projection.evidence_before_commit.required_evidence_lane_ids,
            ]
        ),
    )
    _assert_exposure_refs_present(
        label="state distinction surface exposure refs",
        actual_refs=rendered_surface_contract.rendered_provenance_exposures[
            "state_distinction_surfaces"
        ],
        expected_refs=(surface.surface_id for surface in surface_projection.state_surfaces),
    )
    _assert_exposure_refs_present(
        label="explicit commit boundary exposure refs",
        actual_refs=rendered_surface_contract.rendered_provenance_exposures[
            "explicit_commit_or_handoff_boundary"
        ],
        expected_refs=[rendered_surface_contract.commit_boundary_id],
    )
    _assert_exposure_refs_present(
        label="commit or approval gate exposure refs",
        actual_refs=rendered_surface_contract.rendered_binding_exposures[
            "commit_or_approval_gates"
        ],
        expected_refs=[
            "open-commit-review",
            "submit-commit-request",
            "submit-commit-request-disabled",
        ],
    )
    _assert_exposure_refs_present(
        label="advisory vs authoritative action exposure refs",
        actual_refs=rendered_surface_contract.rendered_binding_exposures[
            "advisory_vs_authoritative_actions"
        ],
        expected_refs=(entry.interaction_id for entry in interaction_contract.interaction_entries),
    )
    _assert_exposure_refs_present(
        label="disabled gated state exposure refs",
        actual_refs=rendered_surface_contract.rendered_binding_exposures[
            "disabled_or_unavailable_gated_states"
        ],
        expected_refs=["submit-commit-request-disabled"],
    )
    _assert_exposure_refs_present(
        label="required evidence reachability anchor exposure refs",
        actual_refs=rendered_surface_contract.rendered_binding_exposures[
            "required_evidence_reachability_anchors"
        ],
        expected_refs=(
            _strip_reference_instance_prefix(binding.target_ref)
            for binding in surface_projection.implementation_observable_bindings
            if binding.target_kind == "required_evidence_reachability_anchor"
        ),
    )
    _assert_exposure_refs_present(
        label="salience-bearing surface exposure refs",
        actual_refs=rendered_surface_contract.rendered_binding_exposures[
            "salience_bearing_warning_status_and_diagnostic_surfaces"
        ],
        expected_refs=(
            _strip_reference_instance_prefix(binding.target_ref)
            for binding in surface_projection.implementation_observable_bindings
            if binding.target_kind in {"warning_surface", "status_surface", "diagnostic_surface"}
        ),
    )

    diagnostics_notice = _normalize_text(
        rendered_surface_contract.diagnostics_lane_read_only_notice
    )
    if (
        "no new severity" not in diagnostics_notice
        or "no local conformance judgment" not in diagnostics_notice
        or "no ui heuristic" not in diagnostics_notice
    ):
        raise UXGovernanceEvidenceError("diagnostics placeholder widening detected")

    truth_notice = _normalize_text(rendered_surface_contract.truth_source_notice)
    if (
        "event streams or worker prose are not rendered here as accepted truth" not in truth_notice
        or "non-authoritative" not in truth_notice
    ):
        raise UXGovernanceEvidenceError(
            "non-authoritative event or worker content truth labeling drift detected"
        )

    if set(rendered_surface_contract.epistemic_state_descriptions) != set(
        _REQUIRED_EPISTEMIC_STATES
    ):
        raise UXGovernanceEvidenceError("epistemic state descriptions drift detected")


def materialize_v36a_ux_domain_morph_ir_evidence(
    *,
    repo_root: Path,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
    ux_domain_packet_schema_path: str = DEFAULT_UX_DOMAIN_PACKET_SCHEMA_PATH,
    ux_morph_ir_schema_path: str = DEFAULT_UX_MORPH_IR_SCHEMA_PATH,
    ux_domain_packet_reference_path: str = DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
    ux_morph_ir_reference_path: str = DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
    approved_profile_table_path: str = DEFAULT_APPROVED_PROFILE_TABLE_PATH,
    same_context_reachability_glossary_path: str = DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
) -> MaterializedUXGovernanceEvidence:
    repo_root = repo_root.resolve()
    if not repo_root.is_dir():
        raise UXGovernanceEvidenceError("repository root does not exist")
    if baseline_metrics_path != DEFAULT_V60_BASELINE_METRICS_PATH:
        raise UXGovernanceEvidenceError(
            "baseline_metrics_path must point to the frozen v60 closeout metrics artifact"
        )

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )
    domain_schema_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_domain_packet_schema_path,
        field_name="ux_domain_packet_schema_path",
        required_prefix="packages/",
    )
    morph_schema_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_ir_schema_path,
        field_name="ux_morph_ir_schema_path",
        required_prefix="packages/",
    )
    domain_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_domain_packet_reference_path,
        field_name="ux_domain_packet_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    morph_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_ir_reference_path,
        field_name="ux_morph_ir_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    approved_profile_table_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=approved_profile_table_path,
        field_name="approved_profile_table_path",
        required_prefix="apps/api/fixtures/",
    )
    same_context_glossary_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=same_context_reachability_glossary_path,
        field_name="same_context_reachability_glossary_path",
        required_prefix="apps/api/fixtures/",
    )

    baseline_metrics = _load_stop_gate_metrics(
        path=baseline_metrics_file,
        field_name="baseline_metrics_path",
    )
    current_metrics = _load_stop_gate_metrics(
        path=current_metrics_file,
        field_name="current_metrics_path",
    )
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    current_metric_keys = set(current_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise UXGovernanceEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise UXGovernanceEvidenceError("metric key set must remain exactly equal to v60")

    domain_schema_payload = _load_frozen_schema(
        path=domain_schema_file,
        field_name="ux_domain_packet_schema_path",
        model_type=UXDomainPacket,
    )
    morph_schema_payload = _load_frozen_schema(
        path=morph_schema_file,
        field_name="ux_morph_ir_schema_path",
        model_type=UXMorphIR,
    )
    domain_payload, domain_packet = _load_validated_model(
        path=domain_reference_file,
        field_name="ux_domain_packet_reference_path",
        model_type=UXDomainPacket,
    )
    morph_payload, morph_ir = _load_validated_model(
        path=morph_reference_file,
        field_name="ux_morph_ir_reference_path",
        model_type=UXMorphIR,
    )
    profile_table_payload, approved_profile_table = _load_validated_model(
        path=approved_profile_table_file,
        field_name="approved_profile_table_path",
        model_type=V36AFirstFamilyApprovedProfileTable,
    )
    glossary_payload, same_context_glossary = _load_validated_model(
        path=same_context_glossary_file,
        field_name="same_context_reachability_glossary_path",
        model_type=V36ASameContextReachabilityGlossary,
    )

    try:
        assert_v36a_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
        )
    except ValueError as exc:
        raise UXGovernanceEvidenceError(str(exc)) from exc

    evidence = V36AUXDomainMorphIREvidence(
        evidence_input_path=output_path,
        ux_domain_packet_schema_path=ux_domain_packet_schema_path,
        ux_domain_packet_schema_hash=_sha256_canonical_json(domain_schema_payload),
        ux_morph_ir_schema_path=ux_morph_ir_schema_path,
        ux_morph_ir_schema_hash=_sha256_canonical_json(morph_schema_payload),
        ux_domain_packet_reference_path=ux_domain_packet_reference_path,
        ux_domain_packet_reference_hash=_sha256_canonical_json(domain_payload),
        ux_morph_ir_reference_path=ux_morph_ir_reference_path,
        ux_morph_ir_reference_hash=_sha256_canonical_json(morph_payload),
        approved_profile_table_path=approved_profile_table_path,
        approved_profile_table_hash=_sha256_canonical_json(profile_table_payload),
        same_context_reachability_glossary_path=same_context_reachability_glossary_path,
        same_context_reachability_glossary_hash=_sha256_canonical_json(glossary_payload),
        adeu_split_vocabulary_frozen=True,
        approved_profile_table_frozen=True,
        approved_profile_cardinality_verified=len(approved_profile_table.profiles) == 2,
        reference_instance_binding_verified=True,
        reference_instance_required_and_present=True,
        deterministic_serialization_verified=True,
        no_free_form_ui_codegen_without_ir_preserved=True,
        ui_artifacts_may_express_but_may_not_mint_authority_preserved=True,
        v35_authority_baseline_unchanged=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v60=True,
        notes=(
            "v61 closeout evidence remains pre-projection, pre-rendered-surface, and "
            "pre-compiler; it verifies the typed ux-domain/morph substrate only."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(_pretty_canonical_json(payload), encoding="utf-8")
    return MaterializedUXGovernanceEvidence(
        path=output_path,
        hash=_sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v36b_surface_projection_interaction_evidence(
    *,
    repo_root: Path,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
    ux_surface_projection_schema_path: str = DEFAULT_UX_SURFACE_PROJECTION_SCHEMA_PATH,
    ux_interaction_contract_schema_path: str = DEFAULT_UX_INTERACTION_CONTRACT_SCHEMA_PATH,
    ux_surface_projection_reference_path: str = DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH,
    ux_interaction_contract_reference_path: str = DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH,
    ux_domain_packet_reference_path: str = DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
    ux_morph_ir_reference_path: str = DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
    approved_profile_table_path: str = DEFAULT_APPROVED_PROFILE_TABLE_PATH,
    same_context_reachability_glossary_path: str = DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
) -> MaterializedUXGovernanceEvidence:
    repo_root = repo_root.resolve()
    if not repo_root.is_dir():
        raise UXGovernanceEvidenceError("repository root does not exist")
    if baseline_metrics_path != DEFAULT_V61_BASELINE_METRICS_PATH:
        raise UXGovernanceEvidenceError(
            "baseline_metrics_path must point to the frozen v61 closeout metrics artifact"
        )

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )
    surface_projection_schema_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_surface_projection_schema_path,
        field_name="ux_surface_projection_schema_path",
        required_prefix="packages/",
    )
    interaction_contract_schema_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_interaction_contract_schema_path,
        field_name="ux_interaction_contract_schema_path",
        required_prefix="packages/",
    )
    surface_projection_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_surface_projection_reference_path,
        field_name="ux_surface_projection_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    interaction_contract_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_interaction_contract_reference_path,
        field_name="ux_interaction_contract_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    domain_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_domain_packet_reference_path,
        field_name="ux_domain_packet_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    morph_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_ir_reference_path,
        field_name="ux_morph_ir_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    approved_profile_table_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=approved_profile_table_path,
        field_name="approved_profile_table_path",
        required_prefix="apps/api/fixtures/",
    )
    same_context_glossary_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=same_context_reachability_glossary_path,
        field_name="same_context_reachability_glossary_path",
        required_prefix="apps/api/fixtures/",
    )

    baseline_metrics = _load_stop_gate_metrics(
        path=baseline_metrics_file,
        field_name="baseline_metrics_path",
    )
    current_metrics = _load_stop_gate_metrics(
        path=current_metrics_file,
        field_name="current_metrics_path",
    )
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    current_metric_keys = set(current_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise UXGovernanceEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise UXGovernanceEvidenceError("metric key set must remain exactly equal to v61")

    surface_projection_schema_payload = _load_frozen_schema(
        path=surface_projection_schema_file,
        field_name="ux_surface_projection_schema_path",
        model_type=UXSurfaceProjection,
    )
    interaction_contract_schema_payload = _load_frozen_schema(
        path=interaction_contract_schema_file,
        field_name="ux_interaction_contract_schema_path",
        model_type=UXInteractionContract,
    )
    surface_projection_payload, surface_projection = _load_validated_v36b_model(
        path=surface_projection_reference_file,
        field_name="ux_surface_projection_reference_path",
        model_type=UXSurfaceProjection,
    )
    interaction_contract_payload, interaction_contract = _load_validated_v36b_model(
        path=interaction_contract_reference_file,
        field_name="ux_interaction_contract_reference_path",
        model_type=UXInteractionContract,
    )
    domain_payload, domain_packet = _load_validated_model(
        path=domain_reference_file,
        field_name="ux_domain_packet_reference_path",
        model_type=UXDomainPacket,
    )
    morph_payload, morph_ir = _load_validated_model(
        path=morph_reference_file,
        field_name="ux_morph_ir_reference_path",
        model_type=UXMorphIR,
    )
    profile_table_payload, approved_profile_table = _load_validated_model(
        path=approved_profile_table_file,
        field_name="approved_profile_table_path",
        model_type=V36AFirstFamilyApprovedProfileTable,
    )
    glossary_payload, same_context_glossary = _load_validated_model(
        path=same_context_glossary_file,
        field_name="same_context_reachability_glossary_path",
        model_type=V36ASameContextReachabilityGlossary,
    )

    _validate_v36b_reference_canonicalization(
        surface_projection_payload=surface_projection_payload,
        interaction_contract_payload=interaction_contract_payload,
    )
    try:
        assert_v36b_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
        )
    except ValueError as exc:
        raise UXGovernanceEvidenceError(str(exc)) from exc
    _validate_authoritative_gate_sources(
        repo_root=repo_root,
        interaction_contract=interaction_contract,
    )

    v36a_substrate_signature = _sha256_canonical_json(
        _v36a_substrate_signature_payload(
            ux_domain_packet_reference_path=ux_domain_packet_reference_path,
            ux_domain_packet_reference_hash=_sha256_canonical_json(domain_payload),
            ux_morph_ir_reference_path=ux_morph_ir_reference_path,
            ux_morph_ir_reference_hash=_sha256_canonical_json(morph_payload),
            approved_profile_table_path=approved_profile_table_path,
            approved_profile_table_hash=_sha256_canonical_json(profile_table_payload),
            same_context_reachability_glossary_path=same_context_reachability_glossary_path,
            same_context_reachability_glossary_hash=_sha256_canonical_json(glossary_payload),
        )
    )

    evidence = V36BSurfaceProjectionInteractionEvidence(
        evidence_input_path=output_path,
        ux_surface_projection_schema_path=ux_surface_projection_schema_path,
        ux_surface_projection_schema_hash=_sha256_canonical_json(surface_projection_schema_payload),
        ux_interaction_contract_schema_path=ux_interaction_contract_schema_path,
        ux_interaction_contract_schema_hash=_sha256_canonical_json(
            interaction_contract_schema_payload
        ),
        ux_surface_projection_reference_path=ux_surface_projection_reference_path,
        ux_surface_projection_reference_hash=_sha256_canonical_json(surface_projection_payload),
        ux_interaction_contract_reference_path=ux_interaction_contract_reference_path,
        ux_interaction_contract_reference_hash=_sha256_canonical_json(interaction_contract_payload),
        projection_interaction_binding_verified=True,
        v36a_reference_pair_binding_verified=True,
        reference_profile_id_verified_against_v36a_table=True,
        authoritative_gate_source_resolution_verified=True,
        forbidden_authoritative_gate_sources_rejected=True,
        stable_provenance_hooks_verified=True,
        implementation_observable_bindings_verified=True,
        binding_identifier_stability_verified=True,
        advisory_authoritative_boundary_preserved=True,
        no_glossary_shadowing_verified=True,
        evidence_before_commit_rule_preserved=True,
        runtime_visible_consequence_epistemic_boundary_preserved=True,
        no_visual_authority_inflation_preserved=True,
        v36a_substrate_consumed_without_drift=True,
        v35_authority_baseline_unchanged=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v61=True,
        notes=(
            "v62 closeout evidence remains pre-rendered-surface, pre-diagnostics, and "
            "pre-compiler; it verifies the typed projection/interaction substrate only. "
            f"Consumed v36a substrate signature: {v36a_substrate_signature}."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(_pretty_canonical_json(payload), encoding="utf-8")
    return MaterializedUXGovernanceEvidence(
        path=output_path,
        hash=_sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v36c_artifact_inspector_reference_surface_evidence(
    *,
    repo_root: Path,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
    rendered_surface_snapshot_path: str = DEFAULT_V36C_RENDERED_SURFACE_SNAPSHOT_PATH,
    implementation_binding_manifest_path: str = DEFAULT_V36C_IMPLEMENTATION_BINDING_MANIFEST_PATH,
    rendered_reference_surface_contract_path: str = (
        DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH
    ),
    ux_surface_projection_reference_path: str = DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH,
    ux_interaction_contract_reference_path: str = DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH,
    ux_domain_packet_reference_path: str = DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
    ux_morph_ir_reference_path: str = DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
    approved_profile_table_path: str = DEFAULT_APPROVED_PROFILE_TABLE_PATH,
    same_context_reachability_glossary_path: str = DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
) -> MaterializedUXGovernanceEvidence:
    repo_root = repo_root.resolve()
    if not repo_root.is_dir():
        raise UXGovernanceEvidenceError("repository root does not exist")
    if baseline_metrics_path != DEFAULT_V62_BASELINE_METRICS_PATH:
        raise UXGovernanceEvidenceError(
            "baseline_metrics_path must point to the frozen v62 closeout metrics artifact"
        )

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    snapshot_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=rendered_surface_snapshot_path,
        field_name="rendered_surface_snapshot_path",
        required_prefix="artifacts/",
    )
    binding_manifest_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=implementation_binding_manifest_path,
        field_name="implementation_binding_manifest_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )
    rendered_surface_contract_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=rendered_reference_surface_contract_path,
        field_name="rendered_reference_surface_contract_path",
        required_prefix="apps/api/fixtures/",
    )
    surface_projection_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_surface_projection_reference_path,
        field_name="ux_surface_projection_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    interaction_contract_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_interaction_contract_reference_path,
        field_name="ux_interaction_contract_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    domain_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_domain_packet_reference_path,
        field_name="ux_domain_packet_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    morph_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_ir_reference_path,
        field_name="ux_morph_ir_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    approved_profile_table_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=approved_profile_table_path,
        field_name="approved_profile_table_path",
        required_prefix="apps/api/fixtures/",
    )
    same_context_glossary_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=same_context_reachability_glossary_path,
        field_name="same_context_reachability_glossary_path",
        required_prefix="apps/api/fixtures/",
    )

    baseline_metrics = _load_stop_gate_metrics(
        path=baseline_metrics_file,
        field_name="baseline_metrics_path",
    )
    current_metrics = _load_stop_gate_metrics(
        path=current_metrics_file,
        field_name="current_metrics_path",
    )
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    current_metric_keys = set(current_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise UXGovernanceEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise UXGovernanceEvidenceError("metric key set must remain exactly equal to v62")

    rendered_surface_contract_payload, rendered_surface_contract = _load_validated_model(
        path=rendered_surface_contract_file,
        field_name="rendered_reference_surface_contract_path",
        model_type=V36CRenderedReferenceSurfaceContract,
    )
    surface_projection_payload, surface_projection = _load_validated_v36b_model(
        path=surface_projection_reference_file,
        field_name="ux_surface_projection_reference_path",
        model_type=UXSurfaceProjection,
    )
    interaction_contract_payload, interaction_contract = _load_validated_v36b_model(
        path=interaction_contract_reference_file,
        field_name="ux_interaction_contract_reference_path",
        model_type=UXInteractionContract,
    )
    domain_payload, domain_packet = _load_validated_model(
        path=domain_reference_file,
        field_name="ux_domain_packet_reference_path",
        model_type=UXDomainPacket,
    )
    morph_payload, morph_ir = _load_validated_model(
        path=morph_reference_file,
        field_name="ux_morph_ir_reference_path",
        model_type=UXMorphIR,
    )
    profile_table_payload, approved_profile_table = _load_validated_model(
        path=approved_profile_table_file,
        field_name="approved_profile_table_path",
        model_type=V36AFirstFamilyApprovedProfileTable,
    )
    glossary_payload, same_context_glossary = _load_validated_model(
        path=same_context_glossary_file,
        field_name="same_context_reachability_glossary_path",
        model_type=V36ASameContextReachabilityGlossary,
    )

    _validate_v36b_reference_canonicalization(
        surface_projection_payload=surface_projection_payload,
        interaction_contract_payload=interaction_contract_payload,
    )
    try:
        assert_v36a_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
        )
        assert_v36b_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
        )
    except ValueError as exc:
        raise UXGovernanceEvidenceError(str(exc)) from exc
    _validate_authoritative_gate_sources(
        repo_root=repo_root,
        interaction_contract=interaction_contract,
    )
    _validate_v36c_rendered_surface_contract(
        rendered_surface_contract=rendered_surface_contract,
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        approved_profile_table=approved_profile_table,
        same_context_glossary=same_context_glossary,
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
    )

    if surface_projection.evidence_before_commit.route_change_required:
        raise UXGovernanceEvidenceError(
            "rendered surface cannot require a route change before required evidence"
        )
    if surface_projection.evidence_before_commit.commit_or_destructive_action_required:
        raise UXGovernanceEvidenceError(
            "rendered surface cannot require a commit or destructive action before evidence"
        )

    combined_hooks = _combined_provenance_hooks(
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
    )
    combined_bindings = _combined_implementation_bindings(
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
    )
    target_manifest = _build_v36c_target_manifest(
        provenance_hooks=combined_hooks,
        implementation_bindings=combined_bindings,
    )

    stable_provenance_target_kinds = {hook["target_kind"] for hook in combined_hooks}
    implementation_binding_target_kinds = {binding["target_kind"] for binding in combined_bindings}
    if "authority_bearing_control" not in stable_provenance_target_kinds:
        raise UXGovernanceEvidenceError(
            "stable provenance hooks must expose authority-bearing controls in the rendered surface"
        )
    if "action_cluster" not in stable_provenance_target_kinds:
        raise UXGovernanceEvidenceError(
            "stable provenance hooks must expose action clusters in the rendered surface"
        )
    if "commit_or_approval_gate" not in implementation_binding_target_kinds:
        raise UXGovernanceEvidenceError(
            "implementation bindings must expose commit or approval gates in the rendered surface"
        )
    if "advisory_action" not in implementation_binding_target_kinds:
        raise UXGovernanceEvidenceError(
            "implementation bindings must expose advisory actions in the rendered surface"
        )

    v36a_substrate_signature = _sha256_canonical_json(
        _v36a_substrate_signature_payload(
            ux_domain_packet_reference_path=ux_domain_packet_reference_path,
            ux_domain_packet_reference_hash=_sha256_canonical_json(domain_payload),
            ux_morph_ir_reference_path=ux_morph_ir_reference_path,
            ux_morph_ir_reference_hash=_sha256_canonical_json(morph_payload),
            approved_profile_table_path=approved_profile_table_path,
            approved_profile_table_hash=_sha256_canonical_json(profile_table_payload),
            same_context_reachability_glossary_path=same_context_reachability_glossary_path,
            same_context_reachability_glossary_hash=_sha256_canonical_json(glossary_payload),
        )
    )
    v36b_substrate_signature = _sha256_canonical_json(
        _v36b_substrate_signature_payload(
            ux_surface_projection_reference_path=ux_surface_projection_reference_path,
            ux_surface_projection_reference_hash=_sha256_canonical_json(surface_projection_payload),
            ux_interaction_contract_reference_path=ux_interaction_contract_reference_path,
            ux_interaction_contract_reference_hash=_sha256_canonical_json(
                interaction_contract_payload
            ),
        )
    )
    rendered_surface_contract_hash = _sha256_canonical_json(rendered_surface_contract_payload)

    snapshot = V36CRenderedSurfaceSemanticSnapshot(
        route_contract_path=rendered_reference_surface_contract_path,
        route_contract_hash=rendered_surface_contract_hash,
        route_id=rendered_surface_contract.route_id,
        route_path=rendered_surface_contract.route_path,
        reference_surface_family=rendered_surface_contract.reference_surface_family,
        reference_instance_id=rendered_surface_contract.reference_instance_id,
        approved_profile_id=rendered_surface_contract.approved_profile_id,
        rendered_surface_snapshot_kind=rendered_surface_contract.rendered_surface_snapshot_kind,
        route_payload_parity_mode=rendered_surface_contract.route_payload_parity_mode,
        diagnostics_lane_mode=rendered_surface_contract.diagnostics_lane_mode,
        diagnostics_lane_notice=rendered_surface_contract.diagnostics_lane_notice,
        diagnostics_lane_read_only_notice=rendered_surface_contract.diagnostics_lane_read_only_notice,
        truth_source_policy=rendered_surface_contract.truth_source_policy,
        truth_source_notice=rendered_surface_contract.truth_source_notice,
        commit_boundary_id=rendered_surface_contract.commit_boundary_id,
        commit_boundary_notice=rendered_surface_contract.commit_boundary_notice,
        required_evidence_lane_ids=surface_projection.evidence_before_commit.required_evidence_lane_ids,
        required_evidence_region_ids=surface_projection.evidence_before_commit.required_evidence_region_ids,
        route_change_required=surface_projection.evidence_before_commit.route_change_required,
        commit_or_destructive_action_required=surface_projection.evidence_before_commit.commit_or_destructive_action_required,
        same_context_reachability_glossary=surface_projection.evidence_before_commit.same_context_reachability_glossary.model_dump(
            mode="json"
        ),
        rendered_region_ids=[region.region_id for region in surface_projection.regions],
        rendered_lane_ids=[lane.lane_id for lane in surface_projection.lanes],
        lane_cluster_rendering=[
            entry.model_dump(mode="json")
            for entry in rendered_surface_contract.lane_cluster_rendering
        ],
        epistemic_state_descriptions=rendered_surface_contract.epistemic_state_descriptions,
        state_surfaces=[
            {
                "lane_id": surface.lane_id,
                "surface_id": surface.surface_id,
                "surface_kind": surface.surface_kind,
            }
            for surface in surface_projection.state_surfaces
        ],
        advisory_action_ids=sorted(
            entry.interaction_id
            for entry in interaction_contract.interaction_entries
            if not entry.authoritative
        ),
        authoritative_or_gated_action_ids=sorted(
            entry.interaction_id
            for entry in interaction_contract.interaction_entries
            if entry.authoritative or entry.gated or entry.approval_bearing
        ),
    )
    snapshot_payload = snapshot.model_dump(mode="json", by_alias=True)
    snapshot_file.parent.mkdir(parents=True, exist_ok=True)
    snapshot_file.write_text(_pretty_canonical_json(snapshot_payload), encoding="utf-8")

    binding_manifest = V36CRenderedSurfaceBindingManifest(
        route_contract_path=rendered_reference_surface_contract_path,
        route_contract_hash=rendered_surface_contract_hash,
        route_id=rendered_surface_contract.route_id,
        route_path=rendered_surface_contract.route_path,
        reference_surface_family=rendered_surface_contract.reference_surface_family,
        reference_instance_id=rendered_surface_contract.reference_instance_id,
        approved_profile_id=rendered_surface_contract.approved_profile_id,
        rendered_provenance_exposures=rendered_surface_contract.rendered_provenance_exposures,
        rendered_binding_exposures=rendered_surface_contract.rendered_binding_exposures,
        stable_provenance_hooks=combined_hooks,
        implementation_observable_bindings=combined_bindings,
        target_manifest=target_manifest,
    )
    binding_manifest_payload = binding_manifest.model_dump(mode="json", by_alias=True)
    binding_manifest_file.parent.mkdir(parents=True, exist_ok=True)
    binding_manifest_file.write_text(
        _pretty_canonical_json(binding_manifest_payload),
        encoding="utf-8",
    )

    evidence = V36CArtifactInspectorReferenceSurfaceEvidence(
        evidence_input_path=output_path,
        rendered_surface_route_id=rendered_surface_contract.route_id,
        rendered_surface_route_path=rendered_surface_contract.route_path,
        rendered_surface_snapshot_kind=rendered_surface_contract.rendered_surface_snapshot_kind,
        rendered_surface_snapshot_path=rendered_surface_snapshot_path,
        rendered_surface_snapshot_hash=_sha256_canonical_json(snapshot_payload),
        implementation_binding_manifest_path=implementation_binding_manifest_path,
        implementation_binding_manifest_hash=_sha256_canonical_json(binding_manifest_payload),
        route_payload_parity_verified_as_presentational_only_transform=True,
        v36a_reference_pair_consumed_without_drift=True,
        v36b_reference_pair_consumed_without_drift=True,
        reference_profile_id_verified_against_v36a_table=True,
        epistemic_state_rendering_verified=True,
        advisory_authoritative_boundary_rendering_verified=True,
        same_context_evidence_visibility_preserved=True,
        no_route_level_glossary_shadowing_verified=True,
        explicit_commit_or_handoff_boundary_visible=True,
        stable_provenance_hooks_exposed=True,
        stable_provenance_hook_targets_exposed=True,
        implementation_observable_bindings_exposed=True,
        non_authoritative_event_or_worker_content_not_rendered_as_accepted_truth=True,
        no_visual_authority_inflation_preserved=True,
        no_unrelated_route_rewrite_detected=True,
        no_v36d_diagnostics_engine_widening=True,
        no_v36e_compiler_widening=True,
        v35_authority_baseline_unchanged=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v62=True,
        notes=(
            "v63 closeout evidence remains pre-v36d diagnostics and pre-v36e compiler export; "
            "it verifies one bounded rendered reference surface only. "
            f"Consumed v36a substrate signature: {v36a_substrate_signature}. "
            f"Consumed v36b substrate signature: {v36b_substrate_signature}. "
            f"Consumed v63 rendered route contract hash: {rendered_surface_contract_hash}."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(_pretty_canonical_json(payload), encoding="utf-8")
    return MaterializedUXGovernanceEvidence(
        path=output_path,
        hash=_sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v36d_morph_diagnostics_conformance_evidence(
    *,
    repo_root: Path,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
    ux_morph_diagnostics_schema_path: str = DEFAULT_UX_MORPH_DIAGNOSTICS_SCHEMA_PATH,
    ux_conformance_report_schema_path: str = DEFAULT_UX_CONFORMANCE_REPORT_SCHEMA_PATH,
    ux_morph_diagnostics_reference_path: str = DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH,
    ux_conformance_report_reference_path: str = DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH,
    ux_domain_packet_schema_path: str = DEFAULT_UX_DOMAIN_PACKET_SCHEMA_PATH,
    ux_morph_ir_schema_path: str = DEFAULT_UX_MORPH_IR_SCHEMA_PATH,
    ux_surface_projection_schema_path: str = DEFAULT_UX_SURFACE_PROJECTION_SCHEMA_PATH,
    ux_interaction_contract_schema_path: str = DEFAULT_UX_INTERACTION_CONTRACT_SCHEMA_PATH,
    ux_domain_packet_reference_path: str = DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
    ux_morph_ir_reference_path: str = DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
    ux_surface_projection_reference_path: str = DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH,
    ux_interaction_contract_reference_path: str = DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH,
    approved_profile_table_path: str = DEFAULT_APPROVED_PROFILE_TABLE_PATH,
    same_context_reachability_glossary_path: str = DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
    rendered_reference_surface_contract_path: str = (
        DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH
    ),
    rendered_surface_snapshot_path: str = DEFAULT_V36C_RENDERED_SURFACE_SNAPSHOT_PATH,
    implementation_binding_manifest_path: str = (
        DEFAULT_V36C_IMPLEMENTATION_BINDING_MANIFEST_PATH
    ),
    rendered_reference_surface_evidence_path: str = (
        DEFAULT_V36C_REFERENCE_SURFACE_EVIDENCE_PATH
    ),
) -> MaterializedUXGovernanceEvidence:
    repo_root = repo_root.resolve()
    if not repo_root.is_dir():
        raise UXGovernanceEvidenceError("repository root does not exist")
    if baseline_metrics_path != DEFAULT_V63_BASELINE_METRICS_PATH:
        raise UXGovernanceEvidenceError(
            "baseline_metrics_path must point to the frozen v63 closeout metrics artifact"
        )

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )
    diagnostics_schema_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_diagnostics_schema_path,
        field_name="ux_morph_diagnostics_schema_path",
        required_prefix="packages/",
    )
    conformance_schema_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_conformance_report_schema_path,
        field_name="ux_conformance_report_schema_path",
        required_prefix="packages/",
    )
    diagnostics_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_diagnostics_reference_path,
        field_name="ux_morph_diagnostics_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    conformance_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_conformance_report_reference_path,
        field_name="ux_conformance_report_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_domain_packet_schema_path,
        field_name="ux_domain_packet_schema_path",
        required_prefix="packages/",
    )
    _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_ir_schema_path,
        field_name="ux_morph_ir_schema_path",
        required_prefix="packages/",
    )
    _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_surface_projection_schema_path,
        field_name="ux_surface_projection_schema_path",
        required_prefix="packages/",
    )
    _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_interaction_contract_schema_path,
        field_name="ux_interaction_contract_schema_path",
        required_prefix="packages/",
    )
    domain_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_domain_packet_reference_path,
        field_name="ux_domain_packet_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    morph_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_ir_reference_path,
        field_name="ux_morph_ir_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    surface_projection_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_surface_projection_reference_path,
        field_name="ux_surface_projection_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    interaction_contract_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_interaction_contract_reference_path,
        field_name="ux_interaction_contract_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    approved_profile_table_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=approved_profile_table_path,
        field_name="approved_profile_table_path",
        required_prefix="apps/api/fixtures/",
    )
    same_context_glossary_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=same_context_reachability_glossary_path,
        field_name="same_context_reachability_glossary_path",
        required_prefix="apps/api/fixtures/",
    )
    rendered_surface_contract_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=rendered_reference_surface_contract_path,
        field_name="rendered_reference_surface_contract_path",
        required_prefix="apps/api/fixtures/",
    )
    rendered_surface_snapshot_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=rendered_surface_snapshot_path,
        field_name="rendered_surface_snapshot_path",
        required_prefix="artifacts/",
    )
    implementation_binding_manifest_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=implementation_binding_manifest_path,
        field_name="implementation_binding_manifest_path",
        required_prefix="artifacts/",
    )
    rendered_surface_evidence_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=rendered_reference_surface_evidence_path,
        field_name="rendered_reference_surface_evidence_path",
        required_prefix="artifacts/",
    )

    baseline_metrics = _load_stop_gate_metrics(
        path=baseline_metrics_file,
        field_name="baseline_metrics_path",
    )
    current_metrics = _load_stop_gate_metrics(
        path=current_metrics_file,
        field_name="current_metrics_path",
    )
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    current_metric_keys = set(current_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise UXGovernanceEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise UXGovernanceEvidenceError("metric key set must remain exactly equal to v63")

    diagnostics_schema_payload = _load_frozen_schema(
        path=diagnostics_schema_file,
        field_name="ux_morph_diagnostics_schema_path",
        model_type=UXMorphDiagnostics,
    )
    conformance_schema_payload = _load_frozen_schema(
        path=conformance_schema_file,
        field_name="ux_conformance_report_schema_path",
        model_type=UXConformanceReport,
    )
    diagnostics_payload, diagnostics = _load_validated_v36d_model(
        path=diagnostics_reference_file,
        field_name="ux_morph_diagnostics_reference_path",
        model_type=UXMorphDiagnostics,
    )
    conformance_report_payload, conformance_report = _load_validated_v36d_model(
        path=conformance_reference_file,
        field_name="ux_conformance_report_reference_path",
        model_type=UXConformanceReport,
    )
    domain_payload, domain_packet = _load_validated_model(
        path=domain_reference_file,
        field_name="ux_domain_packet_reference_path",
        model_type=UXDomainPacket,
    )
    morph_payload, morph_ir = _load_validated_model(
        path=morph_reference_file,
        field_name="ux_morph_ir_reference_path",
        model_type=UXMorphIR,
    )
    surface_projection_payload, surface_projection = _load_validated_v36b_model(
        path=surface_projection_reference_file,
        field_name="ux_surface_projection_reference_path",
        model_type=UXSurfaceProjection,
    )
    interaction_contract_payload, interaction_contract = _load_validated_v36b_model(
        path=interaction_contract_reference_file,
        field_name="ux_interaction_contract_reference_path",
        model_type=UXInteractionContract,
    )
    profile_table_payload, approved_profile_table = _load_validated_model(
        path=approved_profile_table_file,
        field_name="approved_profile_table_path",
        model_type=V36AFirstFamilyApprovedProfileTable,
    )
    glossary_payload, same_context_glossary = _load_validated_model(
        path=same_context_glossary_file,
        field_name="same_context_reachability_glossary_path",
        model_type=V36ASameContextReachabilityGlossary,
    )
    rendered_surface_contract_payload, rendered_surface_contract = _load_validated_model(
        path=rendered_surface_contract_file,
        field_name="rendered_reference_surface_contract_path",
        model_type=V36CRenderedReferenceSurfaceContract,
    )
    rendered_surface_snapshot_payload, _ = _load_validated_model(
        path=rendered_surface_snapshot_file,
        field_name="rendered_surface_snapshot_path",
        model_type=V36CRenderedSurfaceSemanticSnapshot,
    )
    implementation_binding_manifest_payload, _ = _load_validated_model(
        path=implementation_binding_manifest_file,
        field_name="implementation_binding_manifest_path",
        model_type=V36CRenderedSurfaceBindingManifest,
    )
    rendered_surface_evidence_payload, rendered_surface_evidence = _load_validated_model(
        path=rendered_surface_evidence_file,
        field_name="rendered_reference_surface_evidence_path",
        model_type=V36CArtifactInspectorReferenceSurfaceEvidence,
    )

    _validate_v36b_reference_canonicalization(
        surface_projection_payload=surface_projection_payload,
        interaction_contract_payload=interaction_contract_payload,
    )
    _validate_v36d_reference_canonicalization(
        diagnostics_payload=diagnostics_payload,
        conformance_report_payload=conformance_report_payload,
    )
    _validate_authoritative_gate_sources(
        repo_root=repo_root,
        interaction_contract=interaction_contract,
    )
    _validate_v36c_rendered_surface_contract(
        rendered_surface_contract=rendered_surface_contract,
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        approved_profile_table=approved_profile_table,
        same_context_glossary=same_context_glossary,
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
    )

    if rendered_surface_evidence.rendered_surface_snapshot_path != rendered_surface_snapshot_path:
        raise UXGovernanceEvidenceError(
            "rendered surface evidence must point to the consumed v63 snapshot artifact"
        )
    if (
        rendered_surface_evidence.rendered_surface_snapshot_hash
        != _sha256_canonical_json(rendered_surface_snapshot_payload)
    ):
        raise UXGovernanceEvidenceError(
            "rendered surface evidence snapshot hash drift detected"
        )
    if (
        rendered_surface_evidence.implementation_binding_manifest_path
        != implementation_binding_manifest_path
    ):
        raise UXGovernanceEvidenceError(
            "rendered surface evidence must point to the consumed v63 binding manifest artifact"
        )
    if (
        rendered_surface_evidence.implementation_binding_manifest_hash
        != _sha256_canonical_json(implementation_binding_manifest_payload)
    ):
        raise UXGovernanceEvidenceError(
            "rendered surface evidence binding manifest hash drift detected"
        )
    if not rendered_surface_evidence.verification_passed:
        raise UXGovernanceEvidenceError(
            "rendered surface evidence must remain verification-passing"
        )

    try:
        assert_v36d_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
            rendered_surface_contract=rendered_surface_contract_payload,
            rendered_surface_snapshot=rendered_surface_snapshot_payload,
            rendered_surface_binding_manifest=implementation_binding_manifest_payload,
            rendered_reference_surface_evidence=rendered_surface_evidence_payload,
            diagnostics=diagnostics,
            conformance_report=conformance_report,
        )
    except ValueError as exc:
        raise UXGovernanceEvidenceError(str(exc)) from exc

    consumed_artifact_schema_map = _build_v36d_consumed_artifact_schema_map(
        ux_domain_packet_schema_path=ux_domain_packet_schema_path,
        ux_morph_ir_schema_path=ux_morph_ir_schema_path,
        ux_surface_projection_schema_path=ux_surface_projection_schema_path,
        ux_interaction_contract_schema_path=ux_interaction_contract_schema_path,
        ux_domain_packet_reference_path=ux_domain_packet_reference_path,
        ux_morph_ir_reference_path=ux_morph_ir_reference_path,
        ux_surface_projection_reference_path=ux_surface_projection_reference_path,
        ux_interaction_contract_reference_path=ux_interaction_contract_reference_path,
        rendered_reference_surface_contract_path=rendered_reference_surface_contract_path,
        rendered_surface_snapshot_path=rendered_surface_snapshot_path,
        implementation_binding_manifest_path=implementation_binding_manifest_path,
        rendered_reference_surface_evidence_path=rendered_reference_surface_evidence_path,
    )
    _validate_v36d_provenance_resolution(
        repo_root=repo_root,
        diagnostics=diagnostics,
        consumed_artifact_schema_map=consumed_artifact_schema_map,
    )

    seeded_violation_families = set(diagnostics.seeded_violation_families)
    v36a_substrate_signature = _sha256_canonical_json(
        _v36a_substrate_signature_payload(
            ux_domain_packet_reference_path=ux_domain_packet_reference_path,
            ux_domain_packet_reference_hash=_sha256_canonical_json(domain_payload),
            ux_morph_ir_reference_path=ux_morph_ir_reference_path,
            ux_morph_ir_reference_hash=_sha256_canonical_json(morph_payload),
            approved_profile_table_path=approved_profile_table_path,
            approved_profile_table_hash=_sha256_canonical_json(profile_table_payload),
            same_context_reachability_glossary_path=same_context_reachability_glossary_path,
            same_context_reachability_glossary_hash=_sha256_canonical_json(glossary_payload),
        )
    )
    v36b_substrate_signature = _sha256_canonical_json(
        _v36b_substrate_signature_payload(
            ux_surface_projection_reference_path=ux_surface_projection_reference_path,
            ux_surface_projection_reference_hash=_sha256_canonical_json(surface_projection_payload),
            ux_interaction_contract_reference_path=ux_interaction_contract_reference_path,
            ux_interaction_contract_reference_hash=_sha256_canonical_json(
                interaction_contract_payload
            ),
        )
    )
    v36c_substrate_signature = _sha256_canonical_json(
        _v36c_substrate_signature_payload(
            rendered_reference_surface_contract_path=rendered_reference_surface_contract_path,
            rendered_reference_surface_contract_hash=_sha256_canonical_json(
                rendered_surface_contract_payload
            ),
            rendered_surface_snapshot_path=rendered_surface_snapshot_path,
            rendered_surface_snapshot_hash=_sha256_canonical_json(
                rendered_surface_snapshot_payload
            ),
            implementation_binding_manifest_path=implementation_binding_manifest_path,
            implementation_binding_manifest_hash=_sha256_canonical_json(
                implementation_binding_manifest_payload
            ),
            rendered_reference_surface_evidence_path=rendered_reference_surface_evidence_path,
            rendered_reference_surface_evidence_hash=_sha256_canonical_json(
                rendered_surface_evidence_payload
            ),
        )
    )

    evidence = V36DMorphDiagnosticsConformanceEvidence(
        evidence_input_path=output_path,
        ux_morph_diagnostics_schema_path=ux_morph_diagnostics_schema_path,
        ux_morph_diagnostics_schema_hash=_sha256_canonical_json(diagnostics_schema_payload),
        ux_conformance_report_schema_path=ux_conformance_report_schema_path,
        ux_conformance_report_schema_hash=_sha256_canonical_json(conformance_schema_payload),
        ux_morph_diagnostics_reference_path=ux_morph_diagnostics_reference_path,
        ux_morph_diagnostics_reference_hash=_sha256_canonical_json(diagnostics_payload),
        ux_conformance_report_reference_path=ux_conformance_report_reference_path,
        ux_conformance_report_reference_hash=_sha256_canonical_json(
            conformance_report_payload
        ),
        reference_binding_tuple_equality_verified=True,
        v36a_reference_pair_consumed_without_drift=True,
        v36b_reference_pair_consumed_without_drift=True,
        v36c_rendered_surface_consumed_without_drift=True,
        reference_profile_id_verified_against_v36a_table=True,
        diagnostics_severity_taxonomy_verified=True,
        diagnostic_finding_structure_verified=True,
        diagnostics_provenance_pointer_resolution_verified=True,
        rendered_surface_assertion_bridge_verified=True,
        rendered_surface_assertion_bridge_no_fresh_heuristics_verified=True,
        conformance_aggregation_rule_verified=True,
        conformance_report_structure_verified=True,
        conformance_report_diagnostics_derivation_verified=True,
        destructive_confirmation_gap_detectable=(
            "destructive_action_lacks_adequate_confirmation" in seeded_violation_families
        ),
        same_context_reachability_violation_detectable=(
            "required_evidence_not_reachable_within_same_bounded_workbench_context"
            in seeded_violation_families
        ),
        utility_posture_conflict_detectable=(
            "utility_target_conflicts_with_density_or_information_posture"
            in seeded_violation_families
        ),
        requested_profile_command_grammar_conflict_detectable=(
            "requested_interaction_profile_conflicts_with_realized_command_grammar"
            in seeded_violation_families
        ),
        competing_primary_actions_detectable=(
            "competing_primary_actions_in_one_region" in seeded_violation_families
        ),
        provisional_authoritative_styling_violation_detectable=(
            "provisional_data_rendered_with_authoritative_styling"
            in seeded_violation_families
        ),
        advisory_authoritative_boundary_collapse_detectable=(
            "advisory_authoritative_boundary_visually_collapsed" in seeded_violation_families
        ),
        recovery_path_gap_detectable=(
            "failure_mode_lacks_visible_recovery_path" in seeded_violation_families
        ),
        no_taste_engine_drift_detected=True,
        no_event_stream_or_worker_prose_truth_substitution=True,
        diagnostic_truth_substitution_rejected=True,
        v35_authority_baseline_unchanged=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v63=True,
        notes=(
            "v64 closeout evidence remains pre-v36e compiler export and pre-lawful variant "
            "release; it verifies deterministic diagnostics and typed conformance over the "
            "released v36a/v36b/v36c substrate only. "
            f"Consumed v36a substrate signature: {v36a_substrate_signature}. "
            f"Consumed v36b substrate signature: {v36b_substrate_signature}. "
            f"Consumed v36c substrate signature: {v36c_substrate_signature}."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(_pretty_canonical_json(payload), encoding="utf-8")
    return MaterializedUXGovernanceEvidence(
        path=output_path,
        hash=_sha256_canonical_json(payload),
        payload=payload,
    )
