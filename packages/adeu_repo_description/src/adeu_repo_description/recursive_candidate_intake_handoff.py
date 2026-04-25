from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Literal

from pydantic import Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .arc_series_cartography import (
    _CartographyBase,
    _non_empty,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)
from .recursive_candidate_intake import (
    AdmissibleRole,
    CandidateOriginClass,
    CandidateSourcePresencePosture,
    EventualFamilyHint,
    ForbiddenRole,
    OdeuLane,
    PrimaryOdeuLane,
    RepoCandidateSourceRow,
    RequiredNextReviewSurface,
    _non_authority_note,
    _require_forbidden_roles,
)

REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA = (
    "repo_operator_ingress_candidate_binding@1"
)
REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA = (
    "repo_recursive_workflow_residue_intake_report@1"
)
REPO_CANDIDATE_INTAKE_PRE_V70_HANDOFF_SCHEMA = (
    "repo_candidate_intake_pre_v70_handoff@1"
)

RecursiveResidueKind = Literal[
    "self_evidencing_workflow_type_emergence",
    "support_schema_created_by_prior_reasoning",
    "operator_cognition_changed_by_artifact",
    "model_output_comparison_candidate",
    "product_projection_candidate",
    "tool_applicability_pressure",
]
PreV70HandoffTarget = Literal[
    "v70_evidence_classification",
    "v70_adversarial_review",
    "future_family_review",
    "deferred_no_review_selected",
]

_DEFAULT_INTAKE_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus191/"
    "repo_recursive_candidate_intake_v191_reference.json"
)
_DEFAULT_DERIVATION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus192/"
    "repo_candidate_intake_derivation_manifest_v192_reference.json"
)
_DEFAULT_GAP_SCAN_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus192/"
    "repo_candidate_intake_gap_scan_v192_reference.json"
)
_FORBIDDEN_HANDOFF_VERDICT_RE = re.compile(
    r"\b(?:true|proven|settled|validated|correct|useful|verdict)\b",
    re.IGNORECASE,
)


def _ensure_no_handoff_verdict(value: str, *, field_name: str) -> str:
    normalized = _non_authority_note(value, field_name=field_name)
    if _FORBIDDEN_HANDOFF_VERDICT_RE.search(normalized):
        raise ValueError(f"{field_name} may not contain evidence verdict language")
    return normalized


def _non_self_validation_guardrail(value: str, *, field_name: str) -> str:
    normalized = _non_authority_note(value, field_name=field_name)
    lower = normalized.lower()
    has_guardrail = "non-self-validation" in lower or "not self-validating" in lower
    if not has_guardrail:
        raise ValueError(f"{field_name} must carry a non-self-validation guardrail")
    if "self-validating" in lower and "not self-validating" not in lower:
        raise ValueError(f"{field_name} may not treat recursive residue as self-validation")
    return normalized


def _candidate_ref_set(values: list[str]) -> set[str]:
    return set(values)


class RepoOperatorIngressBindingRow(_CartographyBase):
    binding_ref: str
    operator_source_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    source_presence_posture: CandidateSourcePresencePosture
    origin_class: CandidateOriginClass
    primary_odeu_lane: PrimaryOdeuLane
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    admissible_roles: list[AdmissibleRole] = Field(min_length=1)
    forbidden_roles: list[ForbiddenRole] = Field(min_length=1)
    required_next_review_surface: RequiredNextReviewSurface
    eventual_family_hint: EventualFamilyHint
    non_adoption_guardrail: str
    binding_limitation_note: str

    @model_validator(mode="after")
    def _validate_binding_row(self) -> RepoOperatorIngressBindingRow:
        object.__setattr__(
            self,
            "binding_ref",
            _non_empty(self.binding_ref, field_name="binding_ref"),
        )
        object.__setattr__(
            self,
            "operator_source_ref",
            _repo_ref(self.operator_source_ref, field_name="operator_source_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "odeu_lanes",
            _sorted_unique(self.odeu_lanes, field_name="odeu_lanes"),
        )
        object.__setattr__(
            self,
            "admissible_roles",
            _sorted_unique(self.admissible_roles, field_name="admissible_roles"),
        )
        object.__setattr__(
            self,
            "forbidden_roles",
            _sorted_unique(self.forbidden_roles, field_name="forbidden_roles"),
        )
        object.__setattr__(
            self,
            "non_adoption_guardrail",
            _non_authority_note(self.non_adoption_guardrail, field_name="non_adoption_guardrail"),
        )
        object.__setattr__(
            self,
            "binding_limitation_note",
            _non_authority_note(
                self.binding_limitation_note, field_name="binding_limitation_note"
            ),
        )
        for ref in self.source_refs:
            _repo_ref(ref, field_name="binding source_refs")
        if self.operator_source_ref not in self.source_refs:
            raise ValueError("operator_source_ref must be present in source_refs")
        if self.origin_class != "operator_turn":
            raise ValueError("operator ingress binding rows must use origin_class operator_turn")
        if "operator_ingress_binding" not in set(self.admissible_roles):
            raise ValueError("operator ingress bindings require operator_ingress_binding role")
        _require_forbidden_roles(
            forbidden_roles=set(self.forbidden_roles),
            required_roles={
                "commit_release_authority",
                "dispatch_authority",
                "lock_authority",
                "transcript_truth",
            },
            context="operator ingress binding",
        )
        if self.primary_odeu_lane == "mixed" and len(self.odeu_lanes) < 2:
            raise ValueError("primary_odeu_lane=mixed requires at least two odeu_lanes")
        if self.primary_odeu_lane != "mixed" and self.primary_odeu_lane not in self.odeu_lanes:
            raise ValueError("primary_odeu_lane must be present in odeu_lanes")
        return self


class RepoOperatorIngressCandidateBinding(_CartographyBase):
    schema: Literal["repo_operator_ingress_candidate_binding@1"] = (
        REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA
    )
    binding_register_id: str
    intake_id: str
    snapshot_id: str
    candidate_refs: list[str] = Field(min_length=1)
    source_rows: list[RepoCandidateSourceRow] = Field(min_length=1)
    binding_rows: list[RepoOperatorIngressBindingRow] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_binding_register(self) -> RepoOperatorIngressCandidateBinding:
        object.__setattr__(
            self,
            "binding_register_id",
            _non_empty(self.binding_register_id, field_name="binding_register_id"),
        )
        object.__setattr__(self, "intake_id", _non_empty(self.intake_id, field_name="intake_id"))
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "candidate_refs",
            _sorted_unique(self.candidate_refs, field_name="candidate_refs"),
        )
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        object.__setattr__(
            self,
            "binding_rows",
            _sorted_unique_by_ref(
                self.binding_rows, attr="binding_ref", field_name="binding_rows"
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_authority_note(self.limitation_note, field_name="limitation_note"),
        )
        known_candidates = _candidate_ref_set(self.candidate_refs)
        source_rows_by_ref = {row.source_ref: row for row in self.source_rows}
        known_source_refs = set(source_rows_by_ref)
        for row in self.binding_rows:
            if row.candidate_ref not in known_candidates:
                raise ValueError("operator binding candidate_ref must reference known candidates")
            missing_sources = sorted(set(row.source_refs) - known_source_refs)
            if missing_sources:
                raise ValueError(
                    "operator binding source_refs must reference source register rows: "
                    f"{missing_sources}"
                )
            operator_source = source_rows_by_ref[row.operator_source_ref]
            if operator_source.source_kind not in {"operator_turn", "transcript_artifact"}:
                raise ValueError(
                    "operator_source_ref must resolve to operator or transcript source"
                )
            if operator_source.source_presence_posture != row.source_presence_posture:
                raise ValueError(
                    "operator binding source_presence_posture must match source register row"
                )
        return self


class RepoRecursiveWorkflowResidueRow(_CartographyBase):
    residue_ref: str
    workflow_source_refs: list[str] = Field(min_length=1)
    emergent_candidate_refs: list[str] = Field(min_length=1)
    residue_kind: RecursiveResidueKind
    self_evidencing_claim: str
    non_self_validation_guardrail: str
    required_next_review_surface: RequiredNextReviewSurface
    eventual_family_hint: EventualFamilyHint
    limitation_note: str

    @model_validator(mode="after")
    def _validate_residue_row(self) -> RepoRecursiveWorkflowResidueRow:
        object.__setattr__(
            self,
            "residue_ref",
            _non_empty(self.residue_ref, field_name="residue_ref"),
        )
        object.__setattr__(
            self,
            "workflow_source_refs",
            _sorted_unique(self.workflow_source_refs, field_name="workflow_source_refs"),
        )
        object.__setattr__(
            self,
            "emergent_candidate_refs",
            _sorted_unique(self.emergent_candidate_refs, field_name="emergent_candidate_refs"),
        )
        object.__setattr__(
            self,
            "self_evidencing_claim",
            _non_authority_note(self.self_evidencing_claim, field_name="self_evidencing_claim"),
        )
        object.__setattr__(
            self,
            "non_self_validation_guardrail",
            _non_self_validation_guardrail(
                self.non_self_validation_guardrail,
                field_name="non_self_validation_guardrail",
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_authority_note(self.limitation_note, field_name="limitation_note"),
        )
        for ref in self.workflow_source_refs:
            _repo_ref(ref, field_name="workflow_source_refs")
        return self


class RepoRecursiveWorkflowResidueIntakeReport(_CartographyBase):
    schema: Literal["repo_recursive_workflow_residue_intake_report@1"] = (
        REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA
    )
    residue_report_id: str
    intake_id: str
    derivation_manifest_id: str
    snapshot_id: str
    candidate_refs: list[str] = Field(min_length=1)
    workflow_source_refs: list[str] = Field(min_length=1)
    residue_rows: list[RepoRecursiveWorkflowResidueRow] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_residue_report(self) -> RepoRecursiveWorkflowResidueIntakeReport:
        object.__setattr__(
            self,
            "residue_report_id",
            _non_empty(self.residue_report_id, field_name="residue_report_id"),
        )
        object.__setattr__(self, "intake_id", _non_empty(self.intake_id, field_name="intake_id"))
        object.__setattr__(
            self,
            "derivation_manifest_id",
            _non_empty(self.derivation_manifest_id, field_name="derivation_manifest_id"),
        )
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "candidate_refs",
            _sorted_unique(self.candidate_refs, field_name="candidate_refs"),
        )
        object.__setattr__(
            self,
            "workflow_source_refs",
            _sorted_unique(self.workflow_source_refs, field_name="workflow_source_refs"),
        )
        object.__setattr__(
            self,
            "residue_rows",
            _sorted_unique_by_ref(self.residue_rows, attr="residue_ref", field_name="residue_rows"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_authority_note(self.limitation_note, field_name="limitation_note"),
        )
        known_candidates = set(self.candidate_refs)
        known_sources = set(self.workflow_source_refs)
        for ref in self.workflow_source_refs:
            _repo_ref(ref, field_name="workflow_source_refs")
        for row in self.residue_rows:
            missing_candidates = sorted(set(row.emergent_candidate_refs) - known_candidates)
            if missing_candidates:
                raise ValueError(
                    "residue emergent_candidate_refs must reference known candidates: "
                    f"{missing_candidates}"
                )
            missing_sources = sorted(set(row.workflow_source_refs) - known_sources)
            if missing_sources:
                raise ValueError(
                    "residue workflow_source_refs must reference known workflow sources: "
                    f"{missing_sources}"
                )
        return self


class RepoCandidateIntakePreV70HandoffRow(_CartographyBase):
    handoff_ref: str
    candidate_ref: str
    candidate_origin_class: CandidateOriginClass
    handoff_target: PreV70HandoffTarget
    eventual_family_hint: EventualFamilyHint
    handoff_reason: str
    evidence_needed: list[str] = Field(default_factory=list)
    adversarial_review_needed: bool
    non_authority_guardrail: str

    @model_validator(mode="after")
    def _validate_handoff_row(self) -> RepoCandidateIntakePreV70HandoffRow:
        object.__setattr__(
            self,
            "handoff_ref",
            _non_empty(self.handoff_ref, field_name="handoff_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "handoff_target",
            _non_empty(self.handoff_target, field_name="handoff_target"),
        )
        object.__setattr__(
            self,
            "handoff_reason",
            _ensure_no_handoff_verdict(self.handoff_reason, field_name="handoff_reason"),
        )
        object.__setattr__(
            self,
            "evidence_needed",
            _sorted_unique(
                [
                    _ensure_no_handoff_verdict(item, field_name="evidence_needed")
                    for item in self.evidence_needed
                ],
                field_name="evidence_needed",
            ),
        )
        object.__setattr__(
            self,
            "non_authority_guardrail",
            _ensure_no_handoff_verdict(
                self.non_authority_guardrail,
                field_name="non_authority_guardrail",
            ),
        )
        if self.handoff_target == "v70_evidence_classification" and not self.evidence_needed:
            raise ValueError("v70_evidence_classification handoff requires evidence_needed")
        if self.candidate_origin_class == "model_output" and not self.adversarial_review_needed:
            raise ValueError("model-output comparison candidates require adversarial review")
        if (
            self.eventual_family_hint == "v74_operator_projection_review"
            and self.handoff_target != "future_family_review"
        ):
            raise ValueError("product projection candidates require future_family_review handoff")
        return self


class RepoCandidateIntakePreV70Handoff(_CartographyBase):
    schema: Literal["repo_candidate_intake_pre_v70_handoff@1"] = (
        REPO_CANDIDATE_INTAKE_PRE_V70_HANDOFF_SCHEMA
    )
    handoff_register_id: str
    intake_id: str
    derivation_manifest_id: str
    snapshot_id: str
    candidate_refs: list[str] = Field(min_length=1)
    handoff_rows: list[RepoCandidateIntakePreV70HandoffRow] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_handoff_register(self) -> RepoCandidateIntakePreV70Handoff:
        object.__setattr__(
            self,
            "handoff_register_id",
            _non_empty(self.handoff_register_id, field_name="handoff_register_id"),
        )
        object.__setattr__(self, "intake_id", _non_empty(self.intake_id, field_name="intake_id"))
        object.__setattr__(
            self,
            "derivation_manifest_id",
            _non_empty(self.derivation_manifest_id, field_name="derivation_manifest_id"),
        )
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "candidate_refs",
            _sorted_unique(self.candidate_refs, field_name="candidate_refs"),
        )
        object.__setattr__(
            self,
            "handoff_rows",
            _sorted_unique_by_ref(
                self.handoff_rows, attr="handoff_ref", field_name="handoff_rows"
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _ensure_no_handoff_verdict(self.limitation_note, field_name="limitation_note"),
        )
        known_candidates = set(self.candidate_refs)
        for row in self.handoff_rows:
            if row.candidate_ref not in known_candidates:
                raise ValueError("handoff candidate_ref must reference known candidates")
        return self


def _surface_id(prefix: str, schema: str, payload_without_id: dict[str, Any], id_key: str) -> str:
    payload = dict(payload_without_id)
    payload.setdefault("schema", schema)
    payload.pop(id_key, None)
    digest = sha256_canonical_json(payload)
    return f"{prefix}_{digest[:24]}"


def _load_json(repo_root: Path, relative_path: str) -> dict[str, Any]:
    return json.loads((repo_root / relative_path).read_text(encoding="utf-8"))


def _reference_candidate_refs(intake_payload: dict[str, Any]) -> list[str]:
    return sorted(str(row["candidate_ref"]) for row in intake_payload["candidate_rows"])


def derive_v69c_repo_operator_ingress_candidate_binding(
    *,
    repo_root: Path,
) -> RepoOperatorIngressCandidateBinding:
    intake_payload = _load_json(repo_root, _DEFAULT_INTAKE_FIXTURE)
    source_row = RepoCandidateSourceRow(
        source_ref="operator_turn:v69_recursive_meta_conversation",
        source_kind="operator_turn",
        authority_layer="support",
        source_status="available_but_not_integrated",
        source_presence_posture="operator_turn_not_committed",
        integration_note="Operator turn tracked as source-bound candidate pressure only.",
    )
    binding_row = RepoOperatorIngressBindingRow(
        binding_ref="operator-binding:v69:self-evidencing-workflow-type-emergence",
        operator_source_ref=source_row.source_ref,
        candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
        source_refs=[source_row.source_ref],
        source_presence_posture="operator_turn_not_committed",
        origin_class="operator_turn",
        primary_odeu_lane="mixed",
        odeu_lanes=["deontic", "epistemic", "ontological"],
        admissible_roles=["operator_ingress_binding", "support_input"],
        forbidden_roles=[
            "commit_release_authority",
            "dispatch_authority",
            "lock_authority",
            "transcript_truth",
        ],
        required_next_review_surface="v70_evidence_classification",
        eventual_family_hint="v73_outcome_review",
        non_adoption_guardrail=(
            "Operator binding is candidate pressure only and carries no downstream authority."
        ),
        binding_limitation_note=(
            "Uncommitted operator turn is represented through explicit source posture."
        ),
    )
    payload = {
        "schema": REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA,
        "intake_id": str(intake_payload["intake_id"]),
        "snapshot_id": "vNext+193-prestart-on-main",
        "candidate_refs": _reference_candidate_refs(intake_payload),
        "source_rows": [source_row.model_dump(mode="json")],
        "binding_rows": [binding_row.model_dump(mode="json")],
        "limitation_note": "Operator ingress binding is descriptive support only.",
    }
    payload["binding_register_id"] = _surface_id(
        "repo_operator_ingress_candidate_binding",
        REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA,
        payload,
        "binding_register_id",
    )
    return RepoOperatorIngressCandidateBinding.model_validate(payload)


def derive_v69c_repo_recursive_workflow_residue_intake_report(
    *,
    repo_root: Path,
) -> RepoRecursiveWorkflowResidueIntakeReport:
    intake_payload = _load_json(repo_root, _DEFAULT_INTAKE_FIXTURE)
    derivation_payload = _load_json(repo_root, _DEFAULT_DERIVATION_FIXTURE)
    candidate_refs = _reference_candidate_refs(intake_payload)
    workflow_sources = [
        "docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md",
        "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.report.json",
        "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md",
        "docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md",
        "docs/support/arc_series_mapping/odeu_conceptual_diff_report.schema.json",
        "packages/adeu_repo_description/src/adeu_repo_description/recursive_candidate_intake_derivation.py",
    ]
    rows = [
        RepoRecursiveWorkflowResidueRow(
            residue_ref="residue:model-output-comparison-candidate",
            workflow_source_refs=[
                "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.report.json"
            ],
            emergent_candidate_refs=["candidate:internal:odeu_conceptual_diff_report@1"],
            residue_kind="model_output_comparison_candidate",
            self_evidencing_claim="Model-output comparison produced candidate pressure.",
            non_self_validation_guardrail=(
                "Model comparison is non-self-validation support and still requires review."
            ),
            required_next_review_surface="v70_adversarial_review",
            eventual_family_hint="none",
            limitation_note="Comparison residue remains candidate intake support only.",
        ),
        RepoRecursiveWorkflowResidueRow(
            residue_ref="residue:operator-cognition-changed-by-artifact",
            workflow_source_refs=[
                "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md"
            ],
            emergent_candidate_refs=["candidate:internal:self_evidencing_workflow_type_emergence"],
            residue_kind="operator_cognition_changed_by_artifact",
            self_evidencing_claim="Prior artifacts changed operator candidate pressure.",
            non_self_validation_guardrail=(
                "Operator cognition change is non-self-validation support only."
            ),
            required_next_review_surface="v70_evidence_classification",
            eventual_family_hint="v73_outcome_review",
            limitation_note="Operator cognition residue does not settle candidate value.",
        ),
        RepoRecursiveWorkflowResidueRow(
            residue_ref="residue:product-projection-candidate",
            workflow_source_refs=[
                "docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md"
            ],
            emergent_candidate_refs=["candidate:internal:typed_adjudication_product_wedge"],
            residue_kind="product_projection_candidate",
            self_evidencing_claim="Product-facing pressure emerged from the typed audit loop.",
            non_self_validation_guardrail=(
                "Product pressure is non-self-validation support and not product authority."
            ),
            required_next_review_surface="future_family_review",
            eventual_family_hint="v74_operator_projection_review",
            limitation_note="Product projection remains future-family candidate pressure.",
        ),
        RepoRecursiveWorkflowResidueRow(
            residue_ref="residue:self-evidencing-workflow-type-emergence",
            workflow_source_refs=[
                "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md",
                "docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md",
            ],
            emergent_candidate_refs=["candidate:internal:self_evidencing_workflow_type_emergence"],
            residue_kind="self_evidencing_workflow_type_emergence",
            self_evidencing_claim="Workflow residue exposed a missing workflow type.",
            non_self_validation_guardrail=(
                "Self-evidencing workflow emergence is non-self-validation support only."
            ),
            required_next_review_surface="v70_evidence_classification",
            eventual_family_hint="v73_outcome_review",
            limitation_note="Workflow emergence remains candidate pressure only.",
        ),
        RepoRecursiveWorkflowResidueRow(
            residue_ref="residue:support-schema-created-by-prior-reasoning",
            workflow_source_refs=[
                "docs/support/arc_series_mapping/odeu_conceptual_diff_report.schema.json"
            ],
            emergent_candidate_refs=["candidate:internal:odeu_conceptual_diff_schema_support"],
            residue_kind="support_schema_created_by_prior_reasoning",
            self_evidencing_claim="Prior reasoning produced a support-layer schema candidate.",
            non_self_validation_guardrail=(
                "Support schema creation is non-self-validation support only."
            ),
            required_next_review_surface="v70_evidence_classification",
            eventual_family_hint="none",
            limitation_note="Support schema remains unreleased candidate pressure.",
        ),
        RepoRecursiveWorkflowResidueRow(
            residue_ref="residue:tool-applicability-pressure",
            workflow_source_refs=[
                "packages/adeu_repo_description/src/adeu_repo_description/recursive_candidate_intake_derivation.py"
            ],
            emergent_candidate_refs=["candidate:evidence:V68_substrate_for_V69"],
            residue_kind="tool_applicability_pressure",
            self_evidencing_claim="Tool derivation exposed substrate applicability pressure.",
            non_self_validation_guardrail=(
                "Tool applicability pressure is non-self-validation support only."
            ),
            required_next_review_surface="v70_evidence_classification",
            eventual_family_hint="none",
            limitation_note="Tool pressure does not settle substrate sufficiency.",
        ),
    ]
    payload = {
        "schema": REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA,
        "intake_id": str(intake_payload["intake_id"]),
        "derivation_manifest_id": str(derivation_payload["derivation_manifest_id"]),
        "snapshot_id": "vNext+193-prestart-on-main",
        "candidate_refs": candidate_refs,
        "workflow_source_refs": sorted(workflow_sources),
        "residue_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.residue_ref)
        ],
        "limitation_note": "Recursive workflow residue is descriptive support only.",
    }
    payload["residue_report_id"] = _surface_id(
        "repo_recursive_workflow_residue_intake_report",
        REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA,
        payload,
        "residue_report_id",
    )
    return RepoRecursiveWorkflowResidueIntakeReport.model_validate(payload)


def derive_v69c_repo_candidate_intake_pre_v70_handoff(
    *,
    repo_root: Path,
) -> RepoCandidateIntakePreV70Handoff:
    intake_payload = _load_json(repo_root, _DEFAULT_INTAKE_FIXTURE)
    derivation_payload = _load_json(repo_root, _DEFAULT_DERIVATION_FIXTURE)
    candidate_refs = _reference_candidate_refs(intake_payload)
    rows = [
        RepoCandidateIntakePreV70HandoffRow(
            handoff_ref="handoff:candidate:internal:odeu_conceptual_diff_report@1",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            candidate_origin_class="model_output",
            handoff_target="v70_adversarial_review",
            eventual_family_hint="none",
            handoff_reason="Model-output comparison pressure requires adversarial review.",
            evidence_needed=[
                "comparison axes and source refs",
                "variant provenance",
            ],
            adversarial_review_needed=True,
            non_authority_guardrail="Handoff requests review only and carries no authority.",
        ),
        RepoCandidateIntakePreV70HandoffRow(
            handoff_ref="handoff:candidate:internal:self_evidencing_workflow_type_emergence",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            candidate_origin_class="internal_reasoning_residue",
            handoff_target="v70_evidence_classification",
            eventual_family_hint="v73_outcome_review",
            handoff_reason="Recursive residue pressure requires evidence review.",
            evidence_needed=[
                "non-self-validation guardrail",
                "workflow source refs",
            ],
            adversarial_review_needed=False,
            non_authority_guardrail="Handoff requests review only and carries no authority.",
        ),
        RepoCandidateIntakePreV70HandoffRow(
            handoff_ref="handoff:candidate:internal:typed_adjudication_product_wedge",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            candidate_origin_class="internal_reasoning_residue",
            handoff_target="future_family_review",
            eventual_family_hint="v74_operator_projection_review",
            handoff_reason="Product-facing pressure requires future-family review.",
            evidence_needed=[
                "operator projection boundary",
                "product non-authorization guardrail",
            ],
            adversarial_review_needed=False,
            non_authority_guardrail="Handoff requests review only and carries no authority.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_INTAKE_PRE_V70_HANDOFF_SCHEMA,
        "intake_id": str(intake_payload["intake_id"]),
        "derivation_manifest_id": str(derivation_payload["derivation_manifest_id"]),
        "snapshot_id": "vNext+193-prestart-on-main",
        "candidate_refs": candidate_refs,
        "handoff_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.handoff_ref)
        ],
        "limitation_note": "Pre-V70 handoff requests review only and carries no authority.",
    }
    payload["handoff_register_id"] = _surface_id(
        "repo_candidate_intake_pre_v70_handoff",
        REPO_CANDIDATE_INTAKE_PRE_V70_HANDOFF_SCHEMA,
        payload,
        "handoff_register_id",
    )
    return RepoCandidateIntakePreV70Handoff.model_validate(payload)


def derive_v69c_repo_candidate_intake_handoff_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoOperatorIngressCandidateBinding,
    RepoRecursiveWorkflowResidueIntakeReport,
    RepoCandidateIntakePreV70Handoff,
]:
    return (
        derive_v69c_repo_operator_ingress_candidate_binding(repo_root=repo_root),
        derive_v69c_repo_recursive_workflow_residue_intake_report(repo_root=repo_root),
        derive_v69c_repo_candidate_intake_pre_v70_handoff(repo_root=repo_root),
    )
