from __future__ import annotations

from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator

from .synthetic_pressure_mismatch import (
    SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA,
    SyntheticPressureMismatchAllowedAction,
    SyntheticPressureMismatchHarmKind,
    SyntheticPressureMismatchResolutionRoute,
    SyntheticPressureMismatchRule,
    SyntheticPressureMismatchRuleRegistry,
    SyntheticPressureMismatchSignalKind,
    canonicalize_synthetic_pressure_mismatch_rule_registry_payload,
)
from .synthetic_pressure_mismatch_observation import (
    SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA,
    SyntheticPressureMismatchConformanceReport,
    SyntheticPressureMismatchFindingRef,
    _assert_non_empty_text,
    _assert_sorted_unique,
    _canonical_json_hash,
    _load_repo_json_object,
    _normalize_repo_relative_path,
    _resolve_repository_root,
    _sha256_repo_file,
    _validation_context,
    canonicalize_synthetic_pressure_mismatch_conformance_report_payload,
)

SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_SCHEMA = "synthetic_pressure_mismatch_fix_plan@1"
V39D_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS75.md"
    "#v39d_synthetic_pressure_mismatch_fix_plan_contract@1"
)
V39D_SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_EVALUATOR_ID = (
    "adeu_core_ir.synthetic_pressure_mismatch_fix_plan.derive_v39d_fix_plan@1"
)
DEFAULT_V39D_CONFORMANCE_REPORT_REFERENCE_FIXTURE_PATH = (
    "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
    "synthetic_pressure_mismatch_conformance_report_v74_reference.json"
)

SyntheticPressureMismatchFixPlanSchemaVersion = Literal[
    "synthetic_pressure_mismatch_fix_plan@1"
]
SyntheticPressureMismatchPlanPosture = Literal[
    "forward_guidance_only",
    "meta_artifact_correction_only",
    "post_optimizer_guidance_only",
    "review_required",
    "safe_autofix_candidate",
]
SyntheticPressureMismatchProjectionKind = Literal[
    "candidate_action",
    "guidance",
    "meta_artifact_correction",
    "review_prompt",
]
SyntheticPressureMismatchProjectionRole = Literal["forward_agent", "post_optimizer"]
SyntheticPressureMismatchSourceFindingCategory = Literal[
    "deterministic_high_severity_findings",
    "meta_governance_findings",
    "review_only_findings",
    "safe_autofix_candidates",
]


def _source_finding_id_from_parts(
    *,
    observation_packet_id: str,
    rule_id: str,
    local_observation_locator: str,
) -> str:
    return f"{observation_packet_id}::{rule_id}::{local_observation_locator}"


def _source_finding_id_from_ref(ref: SyntheticPressureMismatchFindingRef) -> str:
    return _source_finding_id_from_parts(
        observation_packet_id=ref.observation_packet_id,
        rule_id=ref.rule_id,
        local_observation_locator=ref.local_observation_locator,
    )


def _projected_item_id(
    *,
    role: SyntheticPressureMismatchProjectionRole,
    source_finding_id: str,
    plan_posture: SyntheticPressureMismatchPlanPosture,
    projection_kind: SyntheticPressureMismatchProjectionKind,
    projected_next_step_text: str,
) -> str:
    digest = _canonical_json_hash(
        {
            "projection_kind": projection_kind,
            "projected_next_step_text": projected_next_step_text,
            "role": role,
            "source_finding_id": source_finding_id,
            "plan_posture": plan_posture,
        }
    )[:16]
    return f"v39d_v75_item_{digest}"


def _expected_projected_next_step_text(
    *,
    role: SyntheticPressureMismatchProjectionRole,
    plan_posture: SyntheticPressureMismatchPlanPosture,
    rule: SyntheticPressureMismatchRule,
) -> str:
    if role == "forward_agent":
        return rule.forward_agent_policy
    if plan_posture == "safe_autofix_candidate":
        return f"Candidate only: {rule.post_optimizer_policy}"
    return rule.post_optimizer_policy


def _plan_posture_for_category(
    *,
    role: SyntheticPressureMismatchProjectionRole,
    category: SyntheticPressureMismatchSourceFindingCategory,
) -> SyntheticPressureMismatchPlanPosture:
    if role == "forward_agent":
        return "forward_guidance_only"
    mapping: dict[
        SyntheticPressureMismatchSourceFindingCategory,
        SyntheticPressureMismatchPlanPosture,
    ] = {
        "safe_autofix_candidates": "safe_autofix_candidate",
        "deterministic_high_severity_findings": "review_required",
        "review_only_findings": "post_optimizer_guidance_only",
        "meta_governance_findings": "meta_artifact_correction_only",
    }
    return mapping[category]


def _projection_kind_for_posture(
    posture: SyntheticPressureMismatchPlanPosture,
) -> SyntheticPressureMismatchProjectionKind:
    mapping: dict[
        SyntheticPressureMismatchPlanPosture,
        SyntheticPressureMismatchProjectionKind,
    ] = {
        "forward_guidance_only": "guidance",
        "post_optimizer_guidance_only": "guidance",
        "safe_autofix_candidate": "candidate_action",
        "review_required": "review_prompt",
        "meta_artifact_correction_only": "meta_artifact_correction",
    }
    return mapping[posture]


class SyntheticPressureMismatchProjectedPlanItem(BaseModel):
    model_config = ConfigDict(
        extra="forbid",
        json_schema_extra={
            "allOf": [
                {
                    "if": {
                        "properties": {"plan_posture": {"const": "forward_guidance_only"}},
                        "required": ["plan_posture"],
                    },
                    "then": {"properties": {"projection_kind": {"const": "guidance"}}},
                },
                {
                    "if": {
                        "properties": {
                            "plan_posture": {"const": "post_optimizer_guidance_only"}
                        },
                        "required": ["plan_posture"],
                    },
                    "then": {"properties": {"projection_kind": {"const": "guidance"}}},
                },
                {
                    "if": {
                        "properties": {"plan_posture": {"const": "safe_autofix_candidate"}},
                        "required": ["plan_posture"],
                    },
                    "then": {
                        "properties": {"projection_kind": {"const": "candidate_action"}}
                    },
                },
                {
                    "if": {
                        "properties": {"plan_posture": {"const": "review_required"}},
                        "required": ["plan_posture"],
                    },
                    "then": {"properties": {"projection_kind": {"const": "review_prompt"}}},
                },
                {
                    "if": {
                        "properties": {
                            "plan_posture": {"const": "meta_artifact_correction_only"}
                        },
                        "required": ["plan_posture"],
                    },
                    "then": {
                        "properties": {
                            "projection_kind": {"const": "meta_artifact_correction"}
                        }
                    },
                },
            ]
        },
    )

    projected_item_id: str = Field(min_length=1)
    source_finding_id: str = Field(min_length=1)
    rule_id: str = Field(min_length=1)
    signal_kind: SyntheticPressureMismatchSignalKind
    harm_kind: SyntheticPressureMismatchHarmKind
    allowed_action: SyntheticPressureMismatchAllowedAction
    resolution_route: SyntheticPressureMismatchResolutionRoute
    source_observation_packet_id: str = Field(min_length=1)
    source_local_observation_locator: str = Field(min_length=1)
    plan_posture: SyntheticPressureMismatchPlanPosture
    projection_kind: SyntheticPressureMismatchProjectionKind
    projected_next_step_text: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchProjectedPlanItem":
        _assert_non_empty_text(
            self.projected_item_id,
            field_name="projected_items[].projected_item_id",
        )
        _assert_non_empty_text(
            self.source_finding_id,
            field_name="projected_items[].source_finding_id",
        )
        _assert_non_empty_text(self.rule_id, field_name="projected_items[].rule_id")
        _assert_non_empty_text(
            self.source_observation_packet_id,
            field_name="projected_items[].source_observation_packet_id",
        )
        _assert_non_empty_text(
            self.source_local_observation_locator,
            field_name="projected_items[].source_local_observation_locator",
        )
        _assert_non_empty_text(
            self.projected_next_step_text,
            field_name="projected_items[].projected_next_step_text",
        )
        expected_source_finding_id = _source_finding_id_from_parts(
            observation_packet_id=self.source_observation_packet_id,
            rule_id=self.rule_id,
            local_observation_locator=self.source_local_observation_locator,
        )
        if self.source_finding_id != expected_source_finding_id:
            raise ValueError(
                "projected_items[].source_finding_id must match the carried-through "
                "source observation binding"
            )
        if self.projection_kind != _projection_kind_for_posture(self.plan_posture):
            raise ValueError(
                "projected_items[].projection_kind must match the declared plan_posture"
            )
        return self


class SyntheticPressureMismatchFixPlanDerivationMetadata(BaseModel):
    model_config = ConfigDict(extra="forbid")

    evaluator_id: Literal[
        "adeu_core_ir.synthetic_pressure_mismatch_fix_plan.derive_v39d_fix_plan@1"
    ] = V39D_SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_EVALUATOR_ID
    evaluator_version: Literal["1"] = "1"
    conformance_report_reference_fixture_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    registry_reference_fixture_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    source_finding_ids: list[str] = Field(default_factory=list)
    advisory_only: Literal[True] = True
    repo_mutation_forbidden: Literal[True] = True
    executable_payload_forbidden: Literal[True] = True
    candidate_only_safe_autofix: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(
        self,
    ) -> "SyntheticPressureMismatchFixPlanDerivationMetadata":
        _assert_sorted_unique(
            self.source_finding_ids,
            field_name="derivation_metadata.source_finding_ids",
            allow_empty=True,
        )
        return self


class SyntheticPressureMismatchFixPlan(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: SyntheticPressureMismatchFixPlanSchemaVersion = (
        SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_SCHEMA
    )
    target_arc: Literal["vNext+75"] = "vNext+75"
    target_path: Literal["V39-D"] = "V39-D"
    contract_source: Literal[
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS75.md"
        "#v39d_synthetic_pressure_mismatch_fix_plan_contract@1"
    ] = V39D_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE
    fix_plan_id: str = Field(min_length=1)
    registry_schema: Literal["synthetic_pressure_mismatch_rule_registry@1"] = (
        SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA
    )
    registry_id: str = Field(min_length=1)
    registry_reference_fixture: str = Field(min_length=1)
    conformance_report_schema: Literal["synthetic_pressure_mismatch_conformance_report@1"] = (
        SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA
    )
    conformance_report_id: str = Field(min_length=1)
    conformance_report_reference_fixture: str = Field(min_length=1)
    aggregated_observation_packet_ids: list[str] = Field(min_length=1)
    forward_agent_projections: list[SyntheticPressureMismatchProjectedPlanItem] = Field(
        default_factory=list
    )
    post_optimizer_projections: list[SyntheticPressureMismatchProjectedPlanItem] = Field(
        default_factory=list
    )
    derivation_metadata: SyntheticPressureMismatchFixPlanDerivationMetadata

    @model_validator(mode="after")
    def _validate_contract(
        self,
        info: ValidationInfo,
    ) -> "SyntheticPressureMismatchFixPlan":
        repository_root = _resolve_repository_root(info)
        _assert_non_empty_text(self.fix_plan_id, field_name="fix_plan_id")
        _assert_non_empty_text(self.registry_id, field_name="registry_id")
        _assert_non_empty_text(
            self.conformance_report_id,
            field_name="conformance_report_id",
        )
        self.registry_reference_fixture = _normalize_repo_relative_path(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
        )
        self.conformance_report_reference_fixture = _normalize_repo_relative_path(
            self.conformance_report_reference_fixture,
            field_name="conformance_report_reference_fixture",
        )
        registry_payload = _load_repo_json_object(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
            repository_root=repository_root,
        )
        registry = SyntheticPressureMismatchRuleRegistry.model_validate(
            canonicalize_synthetic_pressure_mismatch_rule_registry_payload(registry_payload),
            context=_validation_context(repository_root),
        )
        report_payload = _load_repo_json_object(
            self.conformance_report_reference_fixture,
            field_name="conformance_report_reference_fixture",
            repository_root=repository_root,
        )
        conformance_report = SyntheticPressureMismatchConformanceReport.model_validate(
            canonicalize_synthetic_pressure_mismatch_conformance_report_payload(
                report_payload,
                repository_root=repository_root,
            ),
            context=_validation_context(repository_root),
        )
        if registry.registry_id != self.registry_id:
            raise ValueError("registry_id must match the referenced released registry fixture")
        if self.conformance_report_id != conformance_report.report_id:
            raise ValueError(
                "conformance_report_id must match the referenced released conformance report"
            )
        if conformance_report.registry_id != self.registry_id:
            raise ValueError(
                "conformance report registry_id must match the referenced released registry fixture"
            )
        if conformance_report.registry_reference_fixture != self.registry_reference_fixture:
            raise ValueError(
                "registry_reference_fixture must match the registry fixture carried by the "
                "released conformance report"
            )
        if (
            self.aggregated_observation_packet_ids
            != conformance_report.aggregated_observation_packet_ids
        ):
            raise ValueError(
                "aggregated_observation_packet_ids must match the released conformance report"
            )
        if (
            self.derivation_metadata.registry_reference_fixture_sha256
            != _sha256_repo_file(
                self.registry_reference_fixture,
                field_name="registry_reference_fixture",
                repository_root=repository_root,
            )
        ):
            raise ValueError(
                "derivation_metadata.registry_reference_fixture_sha256 must match "
                "registry_reference_fixture bytes"
            )
        if (
            self.derivation_metadata.conformance_report_reference_fixture_sha256
            != _sha256_repo_file(
                self.conformance_report_reference_fixture,
                field_name="conformance_report_reference_fixture",
                repository_root=repository_root,
            )
        ):
            raise ValueError(
                "derivation_metadata.conformance_report_reference_fixture_sha256 must match "
                "conformance_report_reference_fixture bytes"
            )
        _assert_sorted_unique(
            self.aggregated_observation_packet_ids,
            field_name="aggregated_observation_packet_ids",
            allow_empty=False,
        )
        rules_by_id = {rule.rule_id: rule for rule in registry.rules}
        report_category_by_finding_id = _report_category_by_source_finding_id(conformance_report)
        source_finding_ids = sorted(report_category_by_finding_id)
        if self.derivation_metadata.source_finding_ids != source_finding_ids:
            raise ValueError(
                "derivation_metadata.source_finding_ids must match the released conformance report"
            )
        _validate_projection_surface(
            field_name="forward_agent_projections",
            role="forward_agent",
            items=self.forward_agent_projections,
            rules_by_id=rules_by_id,
            report_category_by_finding_id=report_category_by_finding_id,
        )
        _validate_projection_surface(
            field_name="post_optimizer_projections",
            role="post_optimizer",
            items=self.post_optimizer_projections,
            rules_by_id=rules_by_id,
            report_category_by_finding_id=report_category_by_finding_id,
        )
        all_ids = sorted(
            [item.projected_item_id for item in self.forward_agent_projections]
            + [item.projected_item_id for item in self.post_optimizer_projections]
        )
        _assert_sorted_unique(
            all_ids,
            field_name="projected_item_id",
            allow_empty=True,
        )
        return self


def _report_category_by_source_finding_id(
    report: SyntheticPressureMismatchConformanceReport,
) -> dict[str, SyntheticPressureMismatchSourceFindingCategory]:
    category_map: dict[str, SyntheticPressureMismatchSourceFindingCategory] = {}
    for category_name, refs in (
        ("safe_autofix_candidates", report.safe_autofix_candidates),
        (
            "deterministic_high_severity_findings",
            report.deterministic_high_severity_findings,
        ),
        ("review_only_findings", report.review_only_findings),
        ("meta_governance_findings", report.meta_governance_findings),
    ):
        for ref in refs:
            category_map[_source_finding_id_from_ref(ref)] = category_name
    return category_map


def _validate_projection_surface(
    *,
    field_name: str,
    role: SyntheticPressureMismatchProjectionRole,
    items: list[SyntheticPressureMismatchProjectedPlanItem],
    rules_by_id: dict[str, SyntheticPressureMismatchRule],
    report_category_by_finding_id: dict[str, SyntheticPressureMismatchSourceFindingCategory],
) -> None:
    projected_item_ids = [item.projected_item_id for item in items]
    _assert_sorted_unique(
        projected_item_ids,
        field_name=f"{field_name}.projected_item_id",
        allow_empty=True,
    )
    semantic_ids: list[str] = []
    for item in items:
        try:
            rule = rules_by_id[item.rule_id]
        except KeyError as exc:
            raise ValueError(
                f"{field_name}[].rule_id must reference a released registry rule"
            ) from exc
        if item.signal_kind != rule.signal_kind:
            raise ValueError(
                f"{field_name}[].signal_kind must match the referenced registry rule"
            )
        if item.harm_kind != rule.harm_kind:
            raise ValueError(
                f"{field_name}[].harm_kind must match the referenced registry rule"
            )
        if item.allowed_action != rule.allowed_action:
            raise ValueError(
                f"{field_name}[].allowed_action must match the referenced registry rule"
            )
        if item.resolution_route != rule.resolution_route:
            raise ValueError(
                f"{field_name}[].resolution_route must match the referenced registry rule"
            )
        expected_text = _expected_projected_next_step_text(
            role=role,
            plan_posture=item.plan_posture,
            rule=rule,
        )
        if item.projected_next_step_text != expected_text:
            raise ValueError(
                f"{field_name}[].projected_next_step_text must equal the released role policy "
                "projection for this route"
            )
        try:
            source_category = report_category_by_finding_id[item.source_finding_id]
        except KeyError as exc:
            raise ValueError(
                f"{field_name}[].source_finding_id must match a released conformance finding"
            ) from exc
        expected_posture = _plan_posture_for_category(role=role, category=source_category)
        if item.plan_posture != expected_posture:
            raise ValueError(
                f"{field_name}[].plan_posture must match the released conformance route for "
                f"{source_category}"
            )
        semantic_ids.append(
            "::".join(
                (
                    role,
                    item.source_finding_id,
                    item.plan_posture,
                    item.projection_kind,
                )
            )
        )
    _assert_sorted_unique(
        semantic_ids,
        field_name=f"{field_name}.identity",
        allow_empty=True,
    )


def canonicalize_synthetic_pressure_mismatch_fix_plan_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = SyntheticPressureMismatchFixPlan.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return model.model_dump(mode="json", exclude_none=True)


def _load_conformance_report(
    conformance_report_reference_fixture_path: str,
    *,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchConformanceReport:
    payload = _load_repo_json_object(
        conformance_report_reference_fixture_path,
        field_name="conformance_report_reference_fixture_path",
        repository_root=repository_root,
    )
    canonical_payload = canonicalize_synthetic_pressure_mismatch_conformance_report_payload(
        payload,
        repository_root=repository_root,
    )
    return SyntheticPressureMismatchConformanceReport.model_validate(
        canonical_payload,
        context=_validation_context(repository_root),
    )


def _build_projected_item(
    *,
    role: SyntheticPressureMismatchProjectionRole,
    source_category: SyntheticPressureMismatchSourceFindingCategory,
    ref: SyntheticPressureMismatchFindingRef,
    rule: SyntheticPressureMismatchRule,
) -> dict[str, str]:
    plan_posture = _plan_posture_for_category(role=role, category=source_category)
    projection_kind = _projection_kind_for_posture(plan_posture)
    projected_next_step_text = _expected_projected_next_step_text(
        role=role,
        plan_posture=plan_posture,
        rule=rule,
    )
    source_finding_id = _source_finding_id_from_ref(ref)
    return {
        "projected_item_id": _projected_item_id(
            role=role,
            source_finding_id=source_finding_id,
            plan_posture=plan_posture,
            projection_kind=projection_kind,
            projected_next_step_text=projected_next_step_text,
        ),
        "source_finding_id": source_finding_id,
        "rule_id": ref.rule_id,
        "signal_kind": rule.signal_kind,
        "harm_kind": rule.harm_kind,
        "allowed_action": rule.allowed_action,
        "resolution_route": rule.resolution_route,
        "source_observation_packet_id": ref.observation_packet_id,
        "source_local_observation_locator": ref.local_observation_locator,
        "plan_posture": plan_posture,
        "projection_kind": projection_kind,
        "projected_next_step_text": projected_next_step_text,
    }


def derive_v39d_fix_plan(
    conformance_report_reference_fixture_path: str = (
        DEFAULT_V39D_CONFORMANCE_REPORT_REFERENCE_FIXTURE_PATH
    ),
    *,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchFixPlan:
    report = _load_conformance_report(
        conformance_report_reference_fixture_path,
        repository_root=repository_root,
    )
    registry_payload = _load_repo_json_object(
        report.registry_reference_fixture,
        field_name="registry_reference_fixture",
        repository_root=repository_root,
    )
    registry = SyntheticPressureMismatchRuleRegistry.model_validate(
        canonicalize_synthetic_pressure_mismatch_rule_registry_payload(registry_payload),
        context=_validation_context(repository_root),
    )
    rules_by_id = {rule.rule_id: rule for rule in registry.rules}

    forward_items: list[dict[str, str]] = []
    post_items: list[dict[str, str]] = []
    source_finding_ids: list[str] = []
    for category_name, refs in (
        ("safe_autofix_candidates", report.safe_autofix_candidates),
        (
            "deterministic_high_severity_findings",
            report.deterministic_high_severity_findings,
        ),
        ("review_only_findings", report.review_only_findings),
        ("meta_governance_findings", report.meta_governance_findings),
    ):
        for ref in refs:
            rule = rules_by_id[ref.rule_id]
            source_finding_ids.append(_source_finding_id_from_ref(ref))
            forward_items.append(
                _build_projected_item(
                    role="forward_agent",
                    source_category=category_name,
                    ref=ref,
                    rule=rule,
                )
            )
            post_items.append(
                _build_projected_item(
                    role="post_optimizer",
                    source_category=category_name,
                    ref=ref,
                    rule=rule,
                )
            )

    forward_items.sort(key=lambda entry: entry["projected_item_id"])
    post_items.sort(key=lambda entry: entry["projected_item_id"])
    source_finding_ids = sorted(source_finding_ids)
    normalized_report_ref = _normalize_repo_relative_path(
        conformance_report_reference_fixture_path,
        field_name="conformance_report_reference_fixture_path",
    )
    payload = {
        "fix_plan_id": f"{report.report_id}_fix_plan",
        "registry_id": registry.registry_id,
        "registry_reference_fixture": report.registry_reference_fixture,
        "conformance_report_id": report.report_id,
        "conformance_report_reference_fixture": normalized_report_ref,
        "aggregated_observation_packet_ids": report.aggregated_observation_packet_ids,
        "forward_agent_projections": forward_items,
        "post_optimizer_projections": post_items,
        "derivation_metadata": {
            "conformance_report_reference_fixture_sha256": _sha256_repo_file(
                normalized_report_ref,
                field_name="conformance_report_reference_fixture_path",
                repository_root=repository_root,
            ),
            "registry_reference_fixture_sha256": _sha256_repo_file(
                report.registry_reference_fixture,
                field_name="registry_reference_fixture",
                repository_root=repository_root,
            ),
            "source_finding_ids": source_finding_ids,
        },
    }
    return SyntheticPressureMismatchFixPlan.model_validate(
        payload,
        context=_validation_context(repository_root),
    )


__all__ = [
    "DEFAULT_V39D_CONFORMANCE_REPORT_REFERENCE_FIXTURE_PATH",
    "SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_SCHEMA",
    "V39D_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE",
    "V39D_SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_EVALUATOR_ID",
    "SyntheticPressureMismatchFixPlan",
    "SyntheticPressureMismatchFixPlanDerivationMetadata",
    "SyntheticPressureMismatchPlanPosture",
    "SyntheticPressureMismatchProjectedPlanItem",
    "SyntheticPressureMismatchProjectionKind",
    "canonicalize_synthetic_pressure_mismatch_fix_plan_payload",
    "derive_v39d_fix_plan",
]
