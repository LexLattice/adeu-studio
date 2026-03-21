from __future__ import annotations

import hashlib
import json
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator

EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA = "external_contribution_alignment_packet@1"
MODULE_CONFORMANCE_REPORT_SCHEMA = "module_conformance_report@1"
V39A_MODULE_CONFORMANCE_EVALUATOR_ID = (
    "adeu_core_ir.external_contribution_alignment.derive_v39a_module_conformance@1"
)

ExternalContributionAlignmentPacketSchemaVersion = Literal[
    "external_contribution_alignment_packet@1"
]
ModuleConformanceReportSchemaVersion = Literal["module_conformance_report@1"]
ExternalContributionSubjectKind = Literal["imported_pull_request_snapshot"]
ExternalContributionEvaluationLane = Literal["external_single_pr"]
ExternalContributionImpactClass = Literal["X0", "X1", "X2"]
ScopeSurfaceKind = Literal[
    "internal_only_utility",
    "externally_reachable_product_surface",
]
ObservedSurfaceKind = Literal[
    "internal_python_utility",
    "api_route",
    "urm_tool",
    "web_route",
    "schema_contract",
]
LocalizedSubjectInputRole = Literal[
    "claimed_scope_snapshot",
    "diff_snapshot",
    "metadata_snapshot",
]
ImportedMetaSequenceGapCode = Literal[
    "missing_declared_checks_at_arrival",
    "missing_post_docs",
    "missing_pre_docs",
    "missing_tests_at_arrival",
    "overclaimed_shipped_scope_at_arrival",
]
MaintainerAlignmentActionCode = Literal[
    "add_targeted_tests",
    "enforce_fail_closed_validation",
    "narrow_scope_claim",
    "record_alignment_artifacts",
    "record_checks_run",
]
ModuleFollowupCode = Literal[
    "add_targeted_tests",
    "enforce_fail_closed_validation",
    "narrow_scope_claim",
    "record_alignment_artifacts",
    "record_checks_run",
]
CodeAlignmentJudgment = Literal["pass", "needs_review", "fail"]
MetaSequenceAlignmentJudgment = Literal["native", "retrospectively_aligned", "not_aligned"]
ModuleConformanceOverallJudgment = Literal["pass", "needs_review", "fail"]
PrecedentStatus = Literal["non_precedent", "precedent_granted"]

_CODE_FOLLOWUPS: tuple[ModuleFollowupCode, ...] = (
    "add_targeted_tests",
    "enforce_fail_closed_validation",
    "record_checks_run",
)
_META_SEQUENCE_FOLLOWUPS: tuple[ModuleFollowupCode, ...] = (
    "record_checks_run",
    "record_alignment_artifacts",
)
_EXTERNAL_SURFACE_KINDS: tuple[ObservedSurfaceKind, ...] = ("api_route", "urm_tool", "web_route")


def _normalize_repo_relative_path(value: str, *, field_name: str) -> str:
    normalized = value.strip().replace("\\", "/")
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    if normalized.startswith("/") or normalized.startswith("../") or "/../" in normalized:
        raise ValueError(f"{field_name} must be repository-relative")
    return normalized


def _default_repository_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _resolve_repository_root(info: ValidationInfo | None = None) -> Path:
    if info is not None and isinstance(info.context, dict):
        repository_root = info.context.get("repository_root")
        if isinstance(repository_root, Path):
            return repository_root
    return _default_repository_root()


def _sha256_repo_file(
    value: str,
    *,
    field_name: str,
    repository_root: Path | None = None,
) -> str:
    normalized = _normalize_repo_relative_path(value, field_name=field_name)
    path = (repository_root or _default_repository_root()) / normalized
    if not path.is_file():
        raise ValueError(f"{field_name} must resolve to an existing repo file")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _assert_sorted_unique(
    values: list[str],
    *,
    field_name: str,
    allow_empty: bool = False,
) -> None:
    if not allow_empty and not values:
        raise ValueError(f"{field_name} must not be empty")
    if any(not value for value in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _canonical_json_hash(payload: dict[str, Any]) -> str:
    return hashlib.sha256(
        json.dumps(
            payload,
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        ).encode("utf-8")
    ).hexdigest()


def _load_repo_json_object(
    value: str,
    *,
    field_name: str,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    normalized = _normalize_repo_relative_path(value, field_name=field_name)
    path = (repository_root or _default_repository_root()) / normalized
    if not path.is_file():
        raise ValueError(f"{field_name} must resolve to an existing repo file")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"{field_name} must contain a JSON object") from exc
    if not isinstance(payload, dict):
        raise ValueError(f"{field_name} must contain a JSON object")
    return payload


def _scopes_differ(
    claimed_scope: "AlignmentScopeSnapshot",
    accepted_scope: "AlignmentScopeSnapshot",
) -> bool:
    return (
        claimed_scope.declared_surface_kind != accepted_scope.declared_surface_kind
        or claimed_scope.surface_refs != accepted_scope.surface_refs
    )


class LocalizedSubjectInput(BaseModel):
    model_config = ConfigDict(extra="forbid")

    input_id: str = Field(min_length=1)
    input_role: LocalizedSubjectInputRole
    path: str = Field(min_length=1)
    sha256: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(self, info: ValidationInfo) -> "LocalizedSubjectInput":
        repository_root = _resolve_repository_root(info)
        self.path = _normalize_repo_relative_path(
            self.path,
            field_name=f"localized_subject_inputs[{self.input_id}].path",
        )
        actual_hash = _sha256_repo_file(
            self.path,
            field_name=f"localized_subject_inputs[{self.input_id}].path",
            repository_root=repository_root,
        )
        if self.sha256 != actual_hash:
            raise ValueError(
                f"localized_subject_inputs[{self.input_id}].sha256 must match repo file bytes"
            )
        return self


class AlignmentScopeSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid")

    summary: str = Field(min_length=1)
    declared_surface_kind: ScopeSurfaceKind
    surface_refs: list[str]

    @model_validator(mode="after")
    def _validate_contract(self) -> "AlignmentScopeSnapshot":
        _assert_sorted_unique(
            self.surface_refs,
            field_name="scope.surface_refs",
            allow_empty=False,
        )
        return self


class ObservedReachableSurface(BaseModel):
    model_config = ConfigDict(extra="forbid")

    surface_ref: str = Field(min_length=1)
    surface_kind: ObservedSurfaceKind
    reachable: Literal[True] = True


class CodeAlignmentInputs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    bounded_change_scope: bool
    fail_closed_validation_in_accepted_diff: bool
    targeted_tests_present_in_accepted_diff: bool
    checks_run: list[str]

    @model_validator(mode="after")
    def _validate_contract(self) -> "CodeAlignmentInputs":
        _assert_sorted_unique(
            self.checks_run,
            field_name="code_alignment_inputs.checks_run",
            allow_empty=True,
        )
        return self


class PolicySourceSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid")

    path: str = Field(min_length=1)
    sha256: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(self, info: ValidationInfo) -> "PolicySourceSnapshot":
        repository_root = _resolve_repository_root(info)
        self.path = _normalize_repo_relative_path(self.path, field_name="policy_sources.path")
        actual_hash = _sha256_repo_file(
            self.path,
            field_name="policy_sources.path",
            repository_root=repository_root,
        )
        if self.sha256 != actual_hash:
            raise ValueError("policy_sources.sha256 must match repo file bytes")
        return self


class ModuleConformanceDerivationMetadata(BaseModel):
    model_config = ConfigDict(extra="forbid")

    evaluator_id: Literal[
        "adeu_core_ir.external_contribution_alignment.derive_v39a_module_conformance@1"
    ] = V39A_MODULE_CONFORMANCE_EVALUATOR_ID
    evaluator_version: Literal["1"] = "1"
    alignment_packet_hash: str = Field(pattern=r"^[0-9a-f]{64}$")
    policy_sources: list[PolicySourceSnapshot]
    default_precedent_status: Literal["non_precedent"] = "non_precedent"
    canonical_local_subject_only: Literal[True] = True
    reviewer_prose_only_forbidden: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(self) -> "ModuleConformanceDerivationMetadata":
        _assert_sorted_unique(
            [entry.path for entry in self.policy_sources],
            field_name="derivation_metadata.policy_sources.path",
            allow_empty=False,
        )
        return self


class ExternalContributionAlignmentPacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: ExternalContributionAlignmentPacketSchemaVersion = (
        EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA
    )
    subject_kind: ExternalContributionSubjectKind = "imported_pull_request_snapshot"
    evaluation_lane: ExternalContributionEvaluationLane = "external_single_pr"
    reference_fixture_id: str = Field(min_length=1)
    contribution_label: str = Field(min_length=1)
    structural_impact_class: ExternalContributionImpactClass
    localized_subject_inputs: list[LocalizedSubjectInput]
    policy_sources: list[PolicySourceSnapshot]
    claimed_scope: AlignmentScopeSnapshot
    observed_reachable_surfaces: list[ObservedReachableSurface]
    accepted_shipped_scope: AlignmentScopeSnapshot
    code_alignment_inputs: CodeAlignmentInputs
    imported_meta_sequence_gaps: list[ImportedMetaSequenceGapCode]
    maintainer_alignment_actions: list[MaintainerAlignmentActionCode]
    maintainer_precedent_status: PrecedentStatus = "non_precedent"
    maintainer_precedent_reason: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self, info: ValidationInfo) -> "ExternalContributionAlignmentPacket":
        repository_root = _resolve_repository_root(info)
        roles = [entry.input_role for entry in self.localized_subject_inputs]
        _assert_sorted_unique(
            [entry.input_id for entry in self.localized_subject_inputs],
            field_name="localized_subject_inputs.input_id",
            allow_empty=False,
        )
        if roles.count("claimed_scope_snapshot") != 1:
            raise ValueError(
                "localized_subject_inputs must include exactly one claimed_scope_snapshot"
            )
        if roles.count("diff_snapshot") != 1:
            raise ValueError("localized_subject_inputs must include exactly one diff_snapshot")
        if roles.count("metadata_snapshot") != 1:
            raise ValueError("localized_subject_inputs must include exactly one metadata_snapshot")
        _assert_sorted_unique(
            [entry.path for entry in self.policy_sources],
            field_name="policy_sources.path",
            allow_empty=False,
        )

        _assert_sorted_unique(
            [entry.surface_ref for entry in self.observed_reachable_surfaces],
            field_name="observed_reachable_surfaces.surface_ref",
            allow_empty=False,
        )
        _assert_sorted_unique(
            list(self.imported_meta_sequence_gaps),
            field_name="imported_meta_sequence_gaps",
            allow_empty=True,
        )
        _assert_sorted_unique(
            list(self.maintainer_alignment_actions),
            field_name="maintainer_alignment_actions",
            allow_empty=True,
        )
        actions = set(self.maintainer_alignment_actions)
        if (
            "add_targeted_tests" in actions
            and not self.code_alignment_inputs.targeted_tests_present_in_accepted_diff
        ):
            raise ValueError(
                "maintainer_alignment_actions cannot mark add_targeted_tests complete "
                "unless targeted tests are present in the accepted diff"
            )
        if (
            "enforce_fail_closed_validation" in actions
            and not self.code_alignment_inputs.fail_closed_validation_in_accepted_diff
        ):
            raise ValueError(
                "maintainer_alignment_actions cannot mark enforce_fail_closed_validation "
                "complete unless fail-closed validation is present in the accepted diff"
            )
        if "record_checks_run" in actions and not self.code_alignment_inputs.checks_run:
            raise ValueError(
                "maintainer_alignment_actions cannot mark record_checks_run complete "
                "unless code_alignment_inputs.checks_run is non-empty"
            )
        metadata_input = next(
            entry
            for entry in self.localized_subject_inputs
            if entry.input_role == "metadata_snapshot"
        )
        metadata_payload = _load_repo_json_object(
            metadata_input.path,
            field_name=f"localized_subject_inputs[{metadata_input.input_id}].path",
            repository_root=repository_root,
        )
        localized_surface_refs = metadata_payload.get("observed_internal_surface_refs", [])
        if not isinstance(localized_surface_refs, list) or any(
            not isinstance(value, str) for value in localized_surface_refs
        ):
            raise ValueError(
                "metadata_snapshot must provide observed_internal_surface_refs as a string list"
            )
        localized_public_surface_refs = metadata_payload.get("observed_public_surface_hits", [])
        if not isinstance(localized_public_surface_refs, list) or any(
            not isinstance(value, str) for value in localized_public_surface_refs
        ):
            raise ValueError(
                "metadata_snapshot must provide observed_public_surface_hits as a string list"
            )
        localized_surface_ref_set = {
            *localized_surface_refs,
            *localized_public_surface_refs,
        }
        observed_surface_refs = {
            entry.surface_ref for entry in self.observed_reachable_surfaces if entry.reachable
        }
        if not observed_surface_refs.issubset(localized_surface_ref_set):
            raise ValueError(
                "observed_reachable_surfaces.surface_ref must be localized in metadata_snapshot"
            )

        if not set(self.accepted_shipped_scope.surface_refs).issubset(observed_surface_refs):
            raise ValueError(
                "accepted_shipped_scope.surface_refs must be observed reachable surfaces"
            )

        has_external_surface = any(
            entry.surface_kind in _EXTERNAL_SURFACE_KINDS
            for entry in self.observed_reachable_surfaces
            if entry.reachable
        )
        if (
            self.accepted_shipped_scope.declared_surface_kind
            == "externally_reachable_product_surface"
            and not has_external_surface
        ):
            raise ValueError(
                "accepted_shipped_scope cannot claim externally reachable product "
                "surface without observed external surfaces"
            )
        if (
            self.maintainer_precedent_status == "precedent_granted"
            and not self.maintainer_precedent_reason
        ):
            raise ValueError(
                "maintainer_precedent_reason is required when precedent status is granted"
            )
        if (
            self.maintainer_precedent_status == "non_precedent"
            and self.maintainer_precedent_reason is not None
        ):
            raise ValueError(
                "maintainer_precedent_reason must be omitted when precedent status "
                "remains non_precedent"
            )
        return self


class ModuleConformanceReport(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: ModuleConformanceReportSchemaVersion = MODULE_CONFORMANCE_REPORT_SCHEMA
    subject_kind: ExternalContributionSubjectKind = "imported_pull_request_snapshot"
    evaluation_lane: ExternalContributionEvaluationLane = "external_single_pr"
    reference_fixture_id: str = Field(min_length=1)
    structural_impact_class: ExternalContributionImpactClass
    code_alignment_judgment: CodeAlignmentJudgment
    meta_sequence_alignment_judgment: MetaSequenceAlignmentJudgment
    overall_judgment: ModuleConformanceOverallJudgment
    claimed_scope: AlignmentScopeSnapshot
    observed_reachable_surfaces: list[ObservedReachableSurface]
    accepted_shipped_scope: AlignmentScopeSnapshot
    imported_meta_sequence_gaps: list[ImportedMetaSequenceGapCode]
    completed_alignment_actions: list[MaintainerAlignmentActionCode]
    unresolved_followup_codes: list[ModuleFollowupCode]
    precedent_status: PrecedentStatus = "non_precedent"
    precedent_reason: str | None = None
    derivation_metadata: ModuleConformanceDerivationMetadata

    @model_validator(mode="after")
    def _validate_contract(self) -> "ModuleConformanceReport":
        _assert_sorted_unique(
            [entry.surface_ref for entry in self.observed_reachable_surfaces],
            field_name="observed_reachable_surfaces.surface_ref",
            allow_empty=False,
        )
        _assert_sorted_unique(
            list(self.imported_meta_sequence_gaps),
            field_name="imported_meta_sequence_gaps",
            allow_empty=True,
        )
        _assert_sorted_unique(
            list(self.completed_alignment_actions),
            field_name="completed_alignment_actions",
            allow_empty=True,
        )
        _assert_sorted_unique(
            list(self.unresolved_followup_codes),
            field_name="unresolved_followup_codes",
            allow_empty=True,
        )
        if set(self.completed_alignment_actions) & set(self.unresolved_followup_codes):
            raise ValueError(
                "completed_alignment_actions and unresolved_followup_codes must remain disjoint"
            )
        observed_surface_refs = {
            entry.surface_ref for entry in self.observed_reachable_surfaces if entry.reachable
        }
        if not set(self.accepted_shipped_scope.surface_refs).issubset(observed_surface_refs):
            raise ValueError(
                "accepted_shipped_scope.surface_refs must be observed reachable surfaces"
            )
        has_external_surface = any(
            entry.surface_kind in _EXTERNAL_SURFACE_KINDS
            for entry in self.observed_reachable_surfaces
            if entry.reachable
        )
        if (
            self.accepted_shipped_scope.declared_surface_kind
            == "externally_reachable_product_surface"
            and not has_external_surface
        ):
            raise ValueError(
                "accepted_shipped_scope cannot claim externally reachable product "
                "surface without observed external surfaces"
            )
        if self.precedent_status == "precedent_granted" and not self.precedent_reason:
            raise ValueError("precedent_reason is required when precedent status is granted")
        if self.precedent_status == "non_precedent" and self.precedent_reason is not None:
            raise ValueError("precedent_reason must be omitted for non_precedent status")
        return self


def _validation_context(repository_root: Path | None) -> dict[str, Path] | None:
    if repository_root is None:
        return None
    return {"repository_root": repository_root}


def canonicalize_external_contribution_alignment_packet_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = ExternalContributionAlignmentPacket.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_module_conformance_report_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = ModuleConformanceReport.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return model.model_dump(mode="json", exclude_none=True)


def _derive_policy_sources(
    packet: ExternalContributionAlignmentPacket,
    *,
    repository_root: Path | None = None,
) -> list[PolicySourceSnapshot]:
    return [
        PolicySourceSnapshot.model_validate(
            entry.model_dump(mode="json"),
            context=_validation_context(repository_root),
        )
        for entry in packet.policy_sources
    ]


def _derive_unresolved_followup_codes(
    packet: ExternalContributionAlignmentPacket,
) -> list[ModuleFollowupCode]:
    followups: set[ModuleFollowupCode] = set()
    actions = set(packet.maintainer_alignment_actions)
    if not packet.code_alignment_inputs.fail_closed_validation_in_accepted_diff:
        followups.add("enforce_fail_closed_validation")
    if not packet.code_alignment_inputs.targeted_tests_present_in_accepted_diff:
        followups.add("add_targeted_tests")
    if not packet.code_alignment_inputs.checks_run:
        followups.add("record_checks_run")
    if packet.imported_meta_sequence_gaps and "record_alignment_artifacts" not in actions:
        followups.add("record_alignment_artifacts")
    if _scopes_differ(packet.claimed_scope, packet.accepted_shipped_scope):
        if "narrow_scope_claim" not in actions:
            followups.add("narrow_scope_claim")
    return sorted(followups)


def _derive_code_alignment_judgment(
    packet: ExternalContributionAlignmentPacket,
    unresolved_followups: list[ModuleFollowupCode],
) -> CodeAlignmentJudgment:
    observed_surface_refs = {
        entry.surface_ref for entry in packet.observed_reachable_surfaces if entry.reachable
    }
    accepted_scope_supported = set(packet.accepted_shipped_scope.surface_refs).issubset(
        observed_surface_refs
    )
    if (
        not accepted_scope_supported
        or not packet.code_alignment_inputs.fail_closed_validation_in_accepted_diff
    ):
        return "fail"
    if any(code in unresolved_followups for code in _CODE_FOLLOWUPS):
        return "needs_review"
    if not packet.code_alignment_inputs.bounded_change_scope:
        return "needs_review"
    return "pass"


def _derive_meta_sequence_alignment_judgment(
    packet: ExternalContributionAlignmentPacket,
    unresolved_followups: list[ModuleFollowupCode],
) -> MetaSequenceAlignmentJudgment:
    if not packet.imported_meta_sequence_gaps:
        return "native"
    if any(code in unresolved_followups for code in _META_SEQUENCE_FOLLOWUPS):
        return "not_aligned"
    return "retrospectively_aligned"


def _derive_overall_judgment(
    *,
    code_alignment_judgment: CodeAlignmentJudgment,
    meta_sequence_alignment_judgment: MetaSequenceAlignmentJudgment,
    unresolved_followups: list[ModuleFollowupCode],
) -> ModuleConformanceOverallJudgment:
    if code_alignment_judgment == "fail":
        return "fail"
    if (
        code_alignment_judgment == "needs_review"
        or meta_sequence_alignment_judgment == "not_aligned"
        or unresolved_followups
    ):
        return "needs_review"
    return "pass"


def derive_v39a_module_conformance(
    payload: dict[str, Any] | ExternalContributionAlignmentPacket,
    *,
    repository_root: Path | None = None,
) -> ModuleConformanceReport:
    packet_payload = (
        payload.model_dump(mode="json", exclude_none=True)
        if isinstance(payload, ExternalContributionAlignmentPacket)
        else deepcopy(payload)
    )
    canonical_packet_payload = canonicalize_external_contribution_alignment_packet_payload(
        packet_payload,
        repository_root=repository_root,
    )
    packet = ExternalContributionAlignmentPacket.model_validate(
        canonical_packet_payload,
        context=_validation_context(repository_root),
    )
    unresolved_followups = _derive_unresolved_followup_codes(packet)
    code_alignment_judgment = _derive_code_alignment_judgment(packet, unresolved_followups)
    meta_sequence_alignment_judgment = _derive_meta_sequence_alignment_judgment(
        packet,
        unresolved_followups,
    )
    overall_judgment = _derive_overall_judgment(
        code_alignment_judgment=code_alignment_judgment,
        meta_sequence_alignment_judgment=meta_sequence_alignment_judgment,
        unresolved_followups=unresolved_followups,
    )
    derivation_metadata = ModuleConformanceDerivationMetadata.model_validate(
        {
            "alignment_packet_hash": _canonical_json_hash(canonical_packet_payload),
            "policy_sources": [
                entry.model_dump(mode="json")
                for entry in _derive_policy_sources(packet, repository_root=repository_root)
            ],
        },
        context=_validation_context(repository_root),
    )
    report_payload = {
        "reference_fixture_id": packet.reference_fixture_id,
        "structural_impact_class": packet.structural_impact_class,
        "code_alignment_judgment": code_alignment_judgment,
        "meta_sequence_alignment_judgment": meta_sequence_alignment_judgment,
        "overall_judgment": overall_judgment,
        "claimed_scope": packet.claimed_scope.model_dump(mode="json"),
        "observed_reachable_surfaces": [
            entry.model_dump(mode="json") for entry in packet.observed_reachable_surfaces
        ],
        "accepted_shipped_scope": packet.accepted_shipped_scope.model_dump(mode="json"),
        "imported_meta_sequence_gaps": list(packet.imported_meta_sequence_gaps),
        "completed_alignment_actions": list(packet.maintainer_alignment_actions),
        "unresolved_followup_codes": unresolved_followups,
        "precedent_status": packet.maintainer_precedent_status,
        "precedent_reason": packet.maintainer_precedent_reason,
        "derivation_metadata": derivation_metadata.model_dump(mode="json", exclude_none=True),
    }
    return ModuleConformanceReport.model_validate(
        report_payload,
        context=_validation_context(repository_root),
    )


__all__ = [
    "EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA",
    "MODULE_CONFORMANCE_REPORT_SCHEMA",
    "V39A_MODULE_CONFORMANCE_EVALUATOR_ID",
    "CodeAlignmentInputs",
    "ExternalContributionAlignmentPacket",
    "LocalizedSubjectInput",
    "ModuleConformanceDerivationMetadata",
    "ModuleConformanceReport",
    "ObservedReachableSurface",
    "PolicySourceSnapshot",
    "AlignmentScopeSnapshot",
    "canonicalize_external_contribution_alignment_packet_payload",
    "canonicalize_module_conformance_report_payload",
    "derive_v39a_module_conformance",
]
