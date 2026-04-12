from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA = "constitutional_support_admission_record@1"
CONSTITUTIONAL_COHERENCE_REPORT_SCHEMA = "constitutional_coherence_report@1"
CONSTITUTIONAL_UNRESOLVED_SEAM_REGISTER_SCHEMA = (
    "constitutional_unresolved_seam_register@1"
)
CONSTITUTIONAL_COHERENCE_LANE_DRIFT_RECORD_SCHEMA = (
    "constitutional_coherence_lane_drift_record@1"
)

AUTHORITY_LAYER_VOCABULARY = ("lock", "planning", "support", "architecture_decomposition")
AUTHORITY_RELATION_VOCABULARY = (
    "released_lock",
    "planning_companion",
    "support_shaping_only",
    "support_descendant_exemplar",
    "coexisting_non_override",
)
PLACEMENT_BASIS_VOCABULARY = (
    "doctrine_surface",
    "schema_kind_definition",
    "artifact_instance",
    "runtime_kind_definition",
)
DOMINANT_FORCE_BAND_VOCABULARY = (
    "observational",
    "interpretive",
    "governing",
    "operative",
)

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

AuthorityLayer = Literal["lock", "planning", "support", "architecture_decomposition"]
AuthorityRelation = Literal[
    "released_lock",
    "planning_companion",
    "support_shaping_only",
    "support_descendant_exemplar",
    "coexisting_non_override",
]
PlacementBasis = Literal[
    "doctrine_surface",
    "schema_kind_definition",
    "artifact_instance",
    "runtime_kind_definition",
]
DominantForceBand = Literal["observational", "interpretive", "governing", "operative"]
PredicateStatus = Literal["pass", "warn", "not_evaluable_yet"]
DriftStatus = Literal["holds", "amended", "superseded", "not_selected_anymore"]


def _assert_present_text(value: str, *, field_name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{field_name} must be non-empty")
    return value


def _ordered_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for value in values:
        normalized = _assert_present_text(value, field_name=field_name)
        if normalized in seen:
            raise ValueError(f"{field_name} must be unique")
        seen.add(normalized)
        ordered.append(normalized)
    return ordered


class CoverageScope(BaseModel):
    model_config = MODEL_CONFIG

    scope_kind: str
    covered_paths: list[str]

    @model_validator(mode="after")
    def _validate_scope(self) -> CoverageScope:
        _assert_present_text(self.scope_kind, field_name="scope_kind")
        object.__setattr__(
            self,
            "covered_paths",
            _ordered_unique_texts(self.covered_paths, field_name="covered_paths"),
        )
        return self


class ConstitutionalSupportAdmissionRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA] = (
        CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA
    )
    admission_id: str
    artifact_ref: str
    authority_layer: AuthorityLayer
    current_authority_relation: AuthorityRelation
    allowed_kernel_use: list[str]
    forbidden_inference: list[str]
    later_promotion_requirement: list[str]
    placement_basis: PlacementBasis
    coverage_scope: CoverageScope
    dominant_force_band: DominantForceBand
    promotion_claim: bool = False
    promotion_witness_refs: list[str] = Field(default_factory=list)
    is_descendant_surface: bool = False
    parent_family_ref: str | None = None
    within_parent_entitlement: bool | None = None
    projection_mints_authority: bool = False

    @model_validator(mode="after")
    def _validate_record(self) -> ConstitutionalSupportAdmissionRecord:
        _assert_present_text(self.admission_id, field_name="admission_id")
        _assert_present_text(self.artifact_ref, field_name="artifact_ref")
        object.__setattr__(
            self,
            "allowed_kernel_use",
            _ordered_unique_texts(self.allowed_kernel_use, field_name="allowed_kernel_use"),
        )
        object.__setattr__(
            self,
            "forbidden_inference",
            _ordered_unique_texts(self.forbidden_inference, field_name="forbidden_inference"),
        )
        object.__setattr__(
            self,
            "later_promotion_requirement",
            _ordered_unique_texts(
                self.later_promotion_requirement,
                field_name="later_promotion_requirement",
            ),
        )
        object.__setattr__(
            self,
            "promotion_witness_refs",
            (
                _ordered_unique_texts(
                    self.promotion_witness_refs,
                    field_name="promotion_witness_refs",
                )
                if self.promotion_witness_refs
                else []
            ),
        )
        if self.promotion_claim and not self.promotion_witness_refs:
            raise ValueError("promotion_witness_refs required when promotion_claim is true")
        if self.is_descendant_surface:
            _assert_present_text(self.parent_family_ref or "", field_name="parent_family_ref")
            if self.within_parent_entitlement is not True:
                raise ValueError(
                    "within_parent_entitlement must be true for descendant surfaces"
                )
        elif self.parent_family_ref is not None or self.within_parent_entitlement is not None:
            raise ValueError(
                "parent_family_ref and within_parent_entitlement are descendant-only fields"
            )
        return self


class ConstitutionalCoherencePredicateEvaluation(BaseModel):
    model_config = MODEL_CONFIG

    predicate_id: str
    artifact_ref: str
    status: PredicateStatus
    evidence_source: str
    detail_note: str

    @model_validator(mode="after")
    def _validate_evaluation(self) -> ConstitutionalCoherencePredicateEvaluation:
        _assert_present_text(self.predicate_id, field_name="predicate_id")
        _assert_present_text(self.artifact_ref, field_name="artifact_ref")
        _assert_present_text(self.evidence_source, field_name="evidence_source")
        _assert_present_text(self.detail_note, field_name="detail_note")
        return self


class ConstitutionalCoherenceFinding(BaseModel):
    model_config = MODEL_CONFIG

    code: str
    artifact_ref: str
    predicate_id: str
    message: str

    @model_validator(mode="after")
    def _validate_finding(self) -> ConstitutionalCoherenceFinding:
        _assert_present_text(self.code, field_name="code")
        _assert_present_text(self.artifact_ref, field_name="artifact_ref")
        _assert_present_text(self.predicate_id, field_name="predicate_id")
        _assert_present_text(self.message, field_name="message")
        return self


class ConstitutionalCoherenceReport(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[CONSTITUTIONAL_COHERENCE_REPORT_SCHEMA] = (
        CONSTITUTIONAL_COHERENCE_REPORT_SCHEMA
    )
    report_id: str
    target_arc: str
    target_path: str
    checker_version: str
    checked_artifact_refs: list[str]
    evaluations: list[ConstitutionalCoherencePredicateEvaluation]
    warning_count: int
    warnings: list[ConstitutionalCoherenceFinding]

    @model_validator(mode="after")
    def _validate_report(self) -> ConstitutionalCoherenceReport:
        _assert_present_text(self.report_id, field_name="report_id")
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(self.checker_version, field_name="checker_version")
        object.__setattr__(
            self,
            "checked_artifact_refs",
            _ordered_unique_texts(
                self.checked_artifact_refs,
                field_name="checked_artifact_refs",
            ),
        )
        if self.warning_count != len(self.warnings):
            raise ValueError("warning_count must equal len(warnings)")
        return self


class ConstitutionalUnresolvedSeamEntry(BaseModel):
    model_config = MODEL_CONFIG

    seam_id: str
    artifact_ref: str
    predicate_id: str
    reason_kind: str
    required_follow_up: list[str]

    @model_validator(mode="after")
    def _validate_entry(self) -> ConstitutionalUnresolvedSeamEntry:
        _assert_present_text(self.seam_id, field_name="seam_id")
        _assert_present_text(self.artifact_ref, field_name="artifact_ref")
        _assert_present_text(self.predicate_id, field_name="predicate_id")
        _assert_present_text(self.reason_kind, field_name="reason_kind")
        object.__setattr__(
            self,
            "required_follow_up",
            _ordered_unique_texts(
                self.required_follow_up,
                field_name="required_follow_up",
            ),
        )
        return self


class ConstitutionalUnresolvedSeamRegister(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[CONSTITUTIONAL_UNRESOLVED_SEAM_REGISTER_SCHEMA] = (
        CONSTITUTIONAL_UNRESOLVED_SEAM_REGISTER_SCHEMA
    )
    register_id: str
    target_arc: str
    target_path: str
    entry_count: int
    entries: list[ConstitutionalUnresolvedSeamEntry]

    @model_validator(mode="after")
    def _validate_register(self) -> ConstitutionalUnresolvedSeamRegister:
        _assert_present_text(self.register_id, field_name="register_id")
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must equal len(entries)")
        return self


class ConstitutionalCoherenceLaneDriftEntry(BaseModel):
    model_config = MODEL_CONFIG

    assumption_ref: str
    status: DriftStatus
    note: str

    @model_validator(mode="after")
    def _validate_entry(self) -> ConstitutionalCoherenceLaneDriftEntry:
        _assert_present_text(self.assumption_ref, field_name="assumption_ref")
        _assert_present_text(self.note, field_name="note")
        return self


class ConstitutionalCoherenceLaneDriftRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[CONSTITUTIONAL_COHERENCE_LANE_DRIFT_RECORD_SCHEMA] = (
        CONSTITUTIONAL_COHERENCE_LANE_DRIFT_RECORD_SCHEMA
    )
    record_id: str
    target_arc: str
    target_path: str
    prior_lane_ref: str
    entry_count: int
    entries: list[ConstitutionalCoherenceLaneDriftEntry]

    @model_validator(mode="after")
    def _validate_record(self) -> ConstitutionalCoherenceLaneDriftRecord:
        _assert_present_text(self.record_id, field_name="record_id")
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(self.prior_lane_ref, field_name="prior_lane_ref")
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must equal len(entries)")
        return self


def compute_constitutional_support_admission_record_id(*, artifact_ref: str) -> str:
    digest = sha256_canonical_json({"artifact_ref": artifact_ref})
    return f"constitutional_admission:{digest[:16]}"


def compute_constitutional_report_id(
    *,
    target_arc: str,
    target_path: str,
    checked_artifact_refs: list[str],
    checker_version: str,
) -> str:
    digest = sha256_canonical_json(
        {
            "target_arc": target_arc,
            "target_path": target_path,
            "checked_artifact_refs": checked_artifact_refs,
            "checker_version": checker_version,
        }
    )
    return f"constitutional_report:{digest[:16]}"


def compute_constitutional_unresolved_seam_entry_id(
    *,
    artifact_ref: str,
    predicate_id: str,
) -> str:
    digest = sha256_canonical_json(
        {
            "artifact_ref": artifact_ref,
            "predicate_id": predicate_id,
        }
    )
    return f"constitutional_seam:{digest[:16]}"


def compute_constitutional_unresolved_seam_register_id(
    *,
    target_arc: str,
    target_path: str,
    seam_ids: list[str],
) -> str:
    digest = sha256_canonical_json(
        {
            "target_arc": target_arc,
            "target_path": target_path,
            "seam_ids": seam_ids,
        }
    )
    return f"constitutional_seam_register:{digest[:16]}"


def compute_constitutional_lane_drift_record_id(
    *,
    target_arc: str,
    target_path: str,
    prior_lane_ref: str,
    assumption_refs: list[str],
) -> str:
    digest = sha256_canonical_json(
        {
            "target_arc": target_arc,
            "target_path": target_path,
            "prior_lane_ref": prior_lane_ref,
            "assumption_refs": assumption_refs,
        }
    )
    return f"constitutional_lane_drift:{digest[:16]}"
