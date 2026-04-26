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
    CandidateAuthorityLayer,
    CandidateOriginClass,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
    _non_authority_note,
)

REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA = (
    "repo_candidate_evidence_classification_record@1"
)
REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA = "repo_candidate_evidence_source_index@1"
REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA = (
    "repo_candidate_review_boundary_guardrail@1"
)

ReviewEvidenceKind = Literal[
    "candidate_handoff_fixture",
    "closeout_evidence",
    "support_dogfood",
    "support_review",
    "schema_file",
    "fixture_file",
    "limitation_or_absence_note",
]
ReviewClaimHorizon = Literal[
    "source_existence",
    "candidate_well_formedness",
    "evidence_support",
    "authority_boundary",
    "adversarial_review_need",
    "conflict_presence",
    "pre_ratification_readiness",
    "utility_projection",
]
EvidenceClassification = Literal[
    "source_bound_for_review",
    "supports_review_claim",
    "contradicts_review_claim",
    "insufficient_evidence",
    "not_evidence_for_claim",
    "requires_adversarial_review",
    "authority_boundary_blocked",
    "tool_applicability_unknown",
    "source_missing_or_stale",
]
AdversarialReviewPosture = Literal[
    "not_required_for_this_claim",
    "required_not_started",
    "required_present",
    "required_inconclusive",
    "conflict_detected",
    "blocked_missing_counterevidence",
    "deferred_to_future_family_review",
]
ForbiddenReviewRole = Literal[
    "truth_verdict",
    "ratified_decision",
    "candidate_adoption",
    "implementation_task",
    "commit_release_authority",
    "product_authorization",
    "dispatch_authority",
    "self_validation",
]
AllowedNextReviewSurface = Literal[
    "v70_adversarial_review",
    "future_family_review",
    "deferred_no_selection",
]

_FORBIDDEN_CLASSIFICATION_AUTHORITY_RE = re.compile(
    r"\b(?:true|truth|adopted|adoption|ratified|ratification|implemented|"
    r"implementation-ready|released|selected|authorized|dispatch(?:ed)?)\b",
    re.IGNORECASE,
)
_ADVERSARIAL_REQUIRED_POSTURES = {
    "required_not_started",
    "required_present",
    "required_inconclusive",
    "conflict_detected",
    "blocked_missing_counterevidence",
}


def _review_note(value: str, *, field_name: str) -> str:
    normalized = _non_authority_note(value, field_name=field_name)
    if _FORBIDDEN_CLASSIFICATION_AUTHORITY_RE.search(normalized):
        raise ValueError(f"{field_name} may not carry review settlement or authority")
    return normalized


def _surface_id(prefix: str, schema: str, payload_without_id: dict[str, Any], id_key: str) -> str:
    payload = dict(payload_without_id)
    payload.setdefault("schema", schema)
    payload.pop(id_key, None)
    digest = sha256_canonical_json(payload)
    return f"{prefix}_{digest[:24]}"


def _load_json(repo_root: Path, relative_path: str) -> dict[str, Any]:
    return json.loads((repo_root / relative_path).read_text(encoding="utf-8"))


def _known_candidate_refs(handoff_payload: dict[str, Any]) -> list[str]:
    return sorted(str(ref) for ref in handoff_payload["candidate_refs"])


class RepoCandidateEvidenceSourceRow(_CartographyBase):
    evidence_source_ref: str
    candidate_ref: str
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_presence_posture: CandidateSourcePresencePosture
    evidence_kind: ReviewEvidenceKind
    claim_horizon: ReviewClaimHorizon
    limitation_note: str

    @model_validator(mode="after")
    def _validate_evidence_source(self) -> RepoCandidateEvidenceSourceRow:
        object.__setattr__(
            self,
            "evidence_source_ref",
            _non_empty(self.evidence_source_ref, field_name="evidence_source_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self,
            "limitation_note",
            _review_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.source_kind in {"support_doc", "review_input"} and self.authority_layer == "lock":
            raise ValueError("support and review sources cannot be lock authority")
        if self.source_ref.startswith("docs/support/") and self.authority_layer == "lock":
            raise ValueError("support-layer source cannot be lock authority")
        if (
            self.source_presence_posture != "present"
            and self.evidence_kind != "limitation_or_absence_note"
        ):
            raise ValueError("missing source evidence rows must use limitation_or_absence_note")
        return self


class RepoCandidateClaimRow(_CartographyBase):
    claim_ref: str
    candidate_ref: str
    candidate_origin_class: CandidateOriginClass
    claim_horizon: ReviewClaimHorizon
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    claim_label: str
    claim_source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_claim(self) -> RepoCandidateClaimRow:
        object.__setattr__(self, "claim_ref", _non_empty(self.claim_ref, field_name="claim_ref"))
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "odeu_lanes",
            _sorted_unique(self.odeu_lanes, field_name="odeu_lanes"),
        )
        object.__setattr__(
            self,
            "claim_label",
            _review_note(self.claim_label, field_name="claim_label"),
        )
        object.__setattr__(
            self,
            "claim_source_refs",
            _sorted_unique(
                [_repo_ref(ref, field_name="claim_source_refs") for ref in self.claim_source_refs],
                field_name="claim_source_refs",
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _review_note(self.limitation_note, field_name="limitation_note"),
        )
        return self


class RepoCandidateClaimClassificationRow(_CartographyBase):
    classification_ref: str
    candidate_ref: str
    claim_ref: str
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    claim_horizon: ReviewClaimHorizon
    evidence_classification: EvidenceClassification
    evidence_source_refs: list[str] = Field(min_length=1)
    adversarial_review_posture: AdversarialReviewPosture
    classification_note: str

    @model_validator(mode="after")
    def _validate_classification(self) -> RepoCandidateClaimClassificationRow:
        object.__setattr__(
            self,
            "classification_ref",
            _non_empty(self.classification_ref, field_name="classification_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(self, "claim_ref", _non_empty(self.claim_ref, field_name="claim_ref"))
        object.__setattr__(
            self,
            "odeu_lanes",
            _sorted_unique(self.odeu_lanes, field_name="odeu_lanes"),
        )
        object.__setattr__(
            self,
            "evidence_source_refs",
            _sorted_unique(self.evidence_source_refs, field_name="evidence_source_refs"),
        )
        object.__setattr__(
            self,
            "classification_note",
            _review_note(self.classification_note, field_name="classification_note"),
        )
        if (
            self.evidence_classification == "requires_adversarial_review"
            and self.adversarial_review_posture == "not_required_for_this_claim"
        ):
            raise ValueError(
                "requires_adversarial_review cannot be marked not_required_for_this_claim"
            )
        return self


class RepoCandidateReviewBoundaryGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    classification_refs: list[str] = Field(min_length=1)
    forbidden_review_roles: list[ForbiddenReviewRole] = Field(min_length=1)
    allowed_next_review_surfaces: list[AllowedNextReviewSurface] = Field(min_length=1)
    non_ratification_guardrail: str

    @model_validator(mode="after")
    def _validate_boundary_guardrail(self) -> RepoCandidateReviewBoundaryGuardrailRow:
        object.__setattr__(
            self,
            "guardrail_ref",
            _non_empty(self.guardrail_ref, field_name="guardrail_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "classification_refs",
            _sorted_unique(self.classification_refs, field_name="classification_refs"),
        )
        object.__setattr__(
            self,
            "forbidden_review_roles",
            _sorted_unique(self.forbidden_review_roles, field_name="forbidden_review_roles"),
        )
        object.__setattr__(
            self,
            "allowed_next_review_surfaces",
            _sorted_unique(
                self.allowed_next_review_surfaces, field_name="allowed_next_review_surfaces"
            ),
        )
        object.__setattr__(
            self,
            "non_ratification_guardrail",
            _review_note(self.non_ratification_guardrail, field_name="non_ratification_guardrail"),
        )
        required_roles = {
            "candidate_adoption",
            "commit_release_authority",
            "dispatch_authority",
            "implementation_task",
            "ratified_decision",
            "truth_verdict",
        }
        missing = sorted(required_roles - set(self.forbidden_review_roles))
        if missing:
            raise ValueError(f"boundary guardrails must forbid review roles: {missing}")
        return self


class RepoCandidateEvidenceSourceIndex(_CartographyBase):
    schema: Literal["repo_candidate_evidence_source_index@1"] = (
        REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA
    )
    source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    evidence_source_rows: list[RepoCandidateEvidenceSourceRow] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_index(self) -> RepoCandidateEvidenceSourceIndex:
        object.__setattr__(
            self,
            "source_index_id",
            _non_empty(self.source_index_id, field_name="source_index_id"),
        )
        object.__setattr__(self, "review_id", _non_empty(self.review_id, field_name="review_id"))
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "source_set_id",
            _non_empty(self.source_set_id, field_name="source_set_id"),
        )
        object.__setattr__(
            self,
            "evidence_source_rows",
            _sorted_unique_by_ref(
                self.evidence_source_rows,
                attr="evidence_source_ref",
                field_name="evidence_source_rows",
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _review_note(self.limitation_note, field_name="limitation_note"),
        )
        return self


class RepoCandidateEvidenceClassificationRecord(_CartographyBase):
    schema: Literal["repo_candidate_evidence_classification_record@1"] = (
        REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA
    )
    classification_record_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    candidate_input_refs: list[str] = Field(min_length=1)
    evidence_source_refs: list[str] = Field(min_length=1)
    claim_rows: list[RepoCandidateClaimRow] = Field(min_length=1)
    claim_classification_rows: list[RepoCandidateClaimClassificationRow] = Field(min_length=1)
    non_ratification_summary: str

    @model_validator(mode="after")
    def _validate_classification_record(self) -> RepoCandidateEvidenceClassificationRecord:
        object.__setattr__(
            self,
            "classification_record_id",
            _non_empty(self.classification_record_id, field_name="classification_record_id"),
        )
        object.__setattr__(self, "review_id", _non_empty(self.review_id, field_name="review_id"))
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "source_set_id",
            _non_empty(self.source_set_id, field_name="source_set_id"),
        )
        object.__setattr__(
            self,
            "candidate_input_refs",
            _sorted_unique(self.candidate_input_refs, field_name="candidate_input_refs"),
        )
        object.__setattr__(
            self,
            "evidence_source_refs",
            _sorted_unique(self.evidence_source_refs, field_name="evidence_source_refs"),
        )
        object.__setattr__(
            self,
            "claim_rows",
            _sorted_unique_by_ref(self.claim_rows, attr="claim_ref", field_name="claim_rows"),
        )
        object.__setattr__(
            self,
            "claim_classification_rows",
            _sorted_unique_by_ref(
                self.claim_classification_rows,
                attr="classification_ref",
                field_name="claim_classification_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_ratification_summary",
            _review_note(self.non_ratification_summary, field_name="non_ratification_summary"),
        )
        candidate_refs = set(self.candidate_input_refs)
        source_refs = set(self.evidence_source_refs)
        claim_rows_by_ref = {row.claim_ref: row for row in self.claim_rows}
        for row in self.claim_rows:
            if row.candidate_ref not in candidate_refs:
                raise ValueError("claim rows must reference known candidate_input_refs")
        for row in self.claim_classification_rows:
            if row.candidate_ref not in candidate_refs:
                raise ValueError("classification rows must reference known candidate_input_refs")
            claim_row = claim_rows_by_ref.get(row.claim_ref)
            if claim_row is None:
                raise ValueError("classification rows must reference known claim rows")
            if claim_row.candidate_ref != row.candidate_ref:
                raise ValueError("classification candidate_ref must match referenced claim")
            if claim_row.claim_horizon != row.claim_horizon:
                raise ValueError("classification claim_horizon must match referenced claim")
            if claim_row.odeu_lanes != row.odeu_lanes:
                raise ValueError("classification odeu_lanes must match referenced claim")
            missing_sources = sorted(set(row.evidence_source_refs) - source_refs)
            if missing_sources:
                raise ValueError(
                    "classification evidence_source_refs must reference known evidence sources: "
                    f"{missing_sources}"
                )
            if (
                claim_row.candidate_origin_class == "model_output"
                and row.adversarial_review_posture not in _ADVERSARIAL_REQUIRED_POSTURES
            ):
                raise ValueError("model-output comparison candidates require adversarial review")
        return self


class RepoCandidateReviewBoundaryGuardrail(_CartographyBase):
    schema: Literal["repo_candidate_review_boundary_guardrail@1"] = (
        REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA
    )
    boundary_guardrail_id: str
    review_id: str
    snapshot_id: str
    candidate_input_refs: list[str] = Field(min_length=1)
    classification_refs: list[str] = Field(min_length=1)
    boundary_guardrail_rows: list[RepoCandidateReviewBoundaryGuardrailRow] = Field(min_length=1)
    non_ratification_summary: str

    @model_validator(mode="after")
    def _validate_boundary_guardrail_register(self) -> RepoCandidateReviewBoundaryGuardrail:
        object.__setattr__(
            self,
            "boundary_guardrail_id",
            _non_empty(self.boundary_guardrail_id, field_name="boundary_guardrail_id"),
        )
        object.__setattr__(self, "review_id", _non_empty(self.review_id, field_name="review_id"))
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "candidate_input_refs",
            _sorted_unique(self.candidate_input_refs, field_name="candidate_input_refs"),
        )
        object.__setattr__(
            self,
            "classification_refs",
            _sorted_unique(self.classification_refs, field_name="classification_refs"),
        )
        object.__setattr__(
            self,
            "boundary_guardrail_rows",
            _sorted_unique_by_ref(
                self.boundary_guardrail_rows,
                attr="guardrail_ref",
                field_name="boundary_guardrail_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_ratification_summary",
            _review_note(self.non_ratification_summary, field_name="non_ratification_summary"),
        )
        known_candidates = set(self.candidate_input_refs)
        known_classifications = set(self.classification_refs)
        for row in self.boundary_guardrail_rows:
            if row.candidate_ref not in known_candidates:
                raise ValueError("boundary guardrail rows must reference known candidates")
            missing_classifications = sorted(set(row.classification_refs) - known_classifications)
            if missing_classifications:
                raise ValueError(
                    "boundary guardrail rows must reference known classifications: "
                    f"{missing_classifications}"
                )
        return self


def validate_v70a_review_classification_bundle(
    *,
    source_index: RepoCandidateEvidenceSourceIndex,
    classification_record: RepoCandidateEvidenceClassificationRecord,
    boundary_guardrail: RepoCandidateReviewBoundaryGuardrail,
) -> None:
    if source_index.review_id != classification_record.review_id:
        raise ValueError("source index and classification record review_id must match")
    if source_index.review_id != boundary_guardrail.review_id:
        raise ValueError("source index and boundary guardrail review_id must match")
    evidence_source_rows_by_ref = {
        row.evidence_source_ref: row for row in source_index.evidence_source_rows
    }
    known_sources = set(evidence_source_rows_by_ref)
    if set(classification_record.evidence_source_refs) - known_sources:
        raise ValueError("classification record evidence_source_refs must come from source index")
    if set(boundary_guardrail.classification_refs) != {
        row.classification_ref for row in classification_record.claim_classification_rows
    }:
        raise ValueError("boundary guardrail classification_refs must match classifications")
    for row in classification_record.claim_classification_rows:
        referenced_sources = [evidence_source_rows_by_ref[ref] for ref in row.evidence_source_refs]
        if row.evidence_classification == "supports_review_claim" and not referenced_sources:
            raise ValueError("supports_review_claim requires evidence source refs")
        if row.evidence_classification == "source_missing_or_stale" and not any(
            source.source_presence_posture != "present" for source in referenced_sources
        ):
            raise ValueError(
                "source_missing_or_stale requires explicit absence-posture evidence source"
            )
        if row.evidence_classification == "insufficient_evidence" and not any(
            source.evidence_kind == "limitation_or_absence_note"
            or source.source_presence_posture != "present"
            for source in referenced_sources
        ):
            raise ValueError("insufficient_evidence requires limitation evidence source")
    classification_refs_by_candidate: dict[str, set[str]] = {}
    for row in classification_record.claim_classification_rows:
        classification_refs_by_candidate.setdefault(row.candidate_ref, set()).add(
            row.classification_ref
        )
    guardrail_candidates = {
        row.candidate_ref for row in boundary_guardrail.boundary_guardrail_rows
    }
    missing_guardrail_candidates = sorted(
        set(classification_refs_by_candidate) - guardrail_candidates
    )
    if missing_guardrail_candidates:
        raise ValueError(
            "boundary guardrail rows must cover every classified candidate: "
            f"{missing_guardrail_candidates}"
        )
    for row in boundary_guardrail.boundary_guardrail_rows:
        expected_refs = classification_refs_by_candidate.get(row.candidate_ref, set())
        if not expected_refs.issubset(set(row.classification_refs)):
            raise ValueError("boundary guardrails must cover candidate classifications")


_DEFAULT_HANDOFF_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus193/"
    "repo_candidate_intake_pre_v70_handoff_v193_reference.json"
)


def derive_v70a_repo_candidate_evidence_source_index(
    *,
    repo_root: Path,
) -> RepoCandidateEvidenceSourceIndex:
    _load_json(repo_root, _DEFAULT_HANDOFF_FIXTURE)
    rows = [
        RepoCandidateEvidenceSourceRow(
            evidence_source_ref="evidence-source:v70a:gptpro-review",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            source_ref=(
                "docs/support/arc_series_mapping/"
                "REVIEW_GPTPRO_CANDIDATE_REVIEW_CLASSIFICATION_V70_PLANNING_v0.md"
            ),
            source_kind="review_input",
            authority_layer="support",
            source_presence_posture="present",
            evidence_kind="support_review",
            claim_horizon="authority_boundary",
            limitation_note="Support review source is review material only.",
        ),
        RepoCandidateEvidenceSourceRow(
            evidence_source_ref="evidence-source:v70a:v69-closeout",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            source_ref="docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md",
            source_kind="closeout_doc",
            authority_layer="closeout_evidence",
            source_presence_posture="present",
            evidence_kind="closeout_evidence",
            claim_horizon="source_existence",
            limitation_note="Closeout source supports review binding only.",
        ),
        RepoCandidateEvidenceSourceRow(
            evidence_source_ref="evidence-source:v70a:v69c-handoff-fixture",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            source_ref=(
                "apps/api/fixtures/repo_description/vnext_plus193/"
                "repo_candidate_intake_pre_v70_handoff_v193_reference.json"
            ),
            source_kind="fixture_file",
            authority_layer="fixture",
            source_presence_posture="present",
            evidence_kind="candidate_handoff_fixture",
            claim_horizon="adversarial_review_need",
            limitation_note="Fixture source binds review need without settling it.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA,
        "review_id": "review:v70a:candidate-evidence-classification",
        "snapshot_id": "vNext+194-prestart-on-main",
        "source_set_id": "source-set:v70a:released-v69c-handoff",
        "evidence_source_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.evidence_source_ref)
        ],
        "limitation_note": "V70-A source index is review classification support only.",
    }
    payload["source_index_id"] = _surface_id(
        "repo_candidate_evidence_source_index",
        REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA,
        payload,
        "source_index_id",
    )
    return RepoCandidateEvidenceSourceIndex.model_validate(payload)


def derive_v70a_repo_candidate_evidence_classification_record(
    *,
    repo_root: Path,
) -> RepoCandidateEvidenceClassificationRecord:
    handoff_payload = _load_json(repo_root, _DEFAULT_HANDOFF_FIXTURE)
    candidate_refs = _known_candidate_refs(handoff_payload)
    claim_rows = [
        RepoCandidateClaimRow(
            claim_ref="claim:v70a:odeu-diff:adversarial-review-need",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            candidate_origin_class="model_output",
            claim_horizon="adversarial_review_need",
            odeu_lanes=["epistemic"],
            claim_label="Model-output comparison requires adversarial review.",
            claim_source_refs=[
                "apps/api/fixtures/repo_description/vnext_plus193/"
                "repo_candidate_intake_pre_v70_handoff_v193_reference.json"
            ],
            limitation_note="Claim is review pressure only.",
        ),
        RepoCandidateClaimRow(
            claim_ref="claim:v70a:product-wedge:authority-boundary",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            candidate_origin_class="internal_reasoning_residue",
            claim_horizon="authority_boundary",
            odeu_lanes=["deontic", "utility"],
            claim_label="Product wedge requires authority-boundary review.",
            claim_source_refs=[
                "docs/support/arc_series_mapping/"
                "REVIEW_GPTPRO_CANDIDATE_REVIEW_CLASSIFICATION_V70_PLANNING_v0.md"
            ],
            limitation_note="Product pressure is not product permission.",
        ),
        RepoCandidateClaimRow(
            claim_ref="claim:v70a:self-evidencing:source-bound",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            candidate_origin_class="internal_reasoning_residue",
            claim_horizon="source_existence",
            odeu_lanes=["deontic", "epistemic", "ontological"],
            claim_label="Self-evidencing workflow pressure is source-bound for review.",
            claim_source_refs=[
                "docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md"
            ],
            limitation_note="Source binding does not validate the workflow type.",
        ),
    ]
    classification_rows = [
        RepoCandidateClaimClassificationRow(
            classification_ref="classification:v70a:odeu-diff:requires-adversarial-review",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            claim_ref="claim:v70a:odeu-diff:adversarial-review-need",
            odeu_lanes=["epistemic"],
            claim_horizon="adversarial_review_need",
            evidence_classification="requires_adversarial_review",
            evidence_source_refs=["evidence-source:v70a:v69c-handoff-fixture"],
            adversarial_review_posture="required_not_started",
            classification_note="Classification records review need only.",
        ),
        RepoCandidateClaimClassificationRow(
            classification_ref="classification:v70a:product-wedge:authority-boundary",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            claim_ref="claim:v70a:product-wedge:authority-boundary",
            odeu_lanes=["deontic", "utility"],
            claim_horizon="authority_boundary",
            evidence_classification="authority_boundary_blocked",
            evidence_source_refs=["evidence-source:v70a:gptpro-review"],
            adversarial_review_posture="deferred_to_future_family_review",
            classification_note="Classification preserves product non-permission.",
        ),
        RepoCandidateClaimClassificationRow(
            classification_ref="classification:v70a:self-evidencing:source-bound",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            claim_ref="claim:v70a:self-evidencing:source-bound",
            odeu_lanes=["deontic", "epistemic", "ontological"],
            claim_horizon="source_existence",
            evidence_classification="source_bound_for_review",
            evidence_source_refs=["evidence-source:v70a:v69-closeout"],
            adversarial_review_posture="not_required_for_this_claim",
            classification_note="Classification records source binding only.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA,
        "review_id": "review:v70a:candidate-evidence-classification",
        "snapshot_id": "vNext+194-prestart-on-main",
        "source_set_id": "source-set:v70a:released-v69c-handoff",
        "candidate_input_refs": candidate_refs,
        "evidence_source_refs": [
            "evidence-source:v70a:gptpro-review",
            "evidence-source:v70a:v69-closeout",
            "evidence-source:v70a:v69c-handoff-fixture",
        ],
        "claim_rows": [
            row.model_dump(mode="json") for row in sorted(claim_rows, key=lambda row: row.claim_ref)
        ],
        "claim_classification_rows": [
            row.model_dump(mode="json")
            for row in sorted(classification_rows, key=lambda row: row.classification_ref)
        ],
        "non_ratification_summary": "V70-A classification rows are review support only.",
    }
    payload["classification_record_id"] = _surface_id(
        "repo_candidate_evidence_classification_record",
        REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA,
        payload,
        "classification_record_id",
    )
    return RepoCandidateEvidenceClassificationRecord.model_validate(payload)


def derive_v70a_repo_candidate_review_boundary_guardrail(
    *,
    repo_root: Path,
) -> RepoCandidateReviewBoundaryGuardrail:
    classification = derive_v70a_repo_candidate_evidence_classification_record(repo_root=repo_root)
    candidate_refs = classification.candidate_input_refs
    classification_refs = [
        row.classification_ref for row in classification.claim_classification_rows
    ]
    forbidden_roles: list[ForbiddenReviewRole] = [
        "candidate_adoption",
        "commit_release_authority",
        "dispatch_authority",
        "implementation_task",
        "product_authorization",
        "ratified_decision",
        "self_validation",
        "truth_verdict",
    ]
    rows = [
        RepoCandidateReviewBoundaryGuardrailRow(
            guardrail_ref="guardrail:v70a:odeu-diff",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            classification_refs=[
                "classification:v70a:odeu-diff:requires-adversarial-review"
            ],
            forbidden_review_roles=forbidden_roles,
            allowed_next_review_surfaces=["v70_adversarial_review"],
            non_ratification_guardrail="Review classification carries no settlement power.",
        ),
        RepoCandidateReviewBoundaryGuardrailRow(
            guardrail_ref="guardrail:v70a:product-wedge",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            classification_refs=["classification:v70a:product-wedge:authority-boundary"],
            forbidden_review_roles=forbidden_roles,
            allowed_next_review_surfaces=["future_family_review"],
            non_ratification_guardrail="Product pressure remains review material only.",
        ),
        RepoCandidateReviewBoundaryGuardrailRow(
            guardrail_ref="guardrail:v70a:self-evidencing",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            classification_refs=["classification:v70a:self-evidencing:source-bound"],
            forbidden_review_roles=forbidden_roles,
            allowed_next_review_surfaces=["future_family_review", "v70_adversarial_review"],
            non_ratification_guardrail="Source-bound review remains non-ratifying.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
        "review_id": "review:v70a:candidate-evidence-classification",
        "snapshot_id": "vNext+194-prestart-on-main",
        "candidate_input_refs": candidate_refs,
        "classification_refs": classification_refs,
        "boundary_guardrail_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.guardrail_ref)
        ],
        "non_ratification_summary": "Boundary guardrails prevent review classification overreach.",
    }
    payload["boundary_guardrail_id"] = _surface_id(
        "repo_candidate_review_boundary_guardrail",
        REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
        payload,
        "boundary_guardrail_id",
    )
    return RepoCandidateReviewBoundaryGuardrail.model_validate(payload)


def derive_v70a_repo_candidate_review_classification_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoCandidateEvidenceSourceIndex,
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateReviewBoundaryGuardrail,
]:
    source_index = derive_v70a_repo_candidate_evidence_source_index(repo_root=repo_root)
    classification = derive_v70a_repo_candidate_evidence_classification_record(
        repo_root=repo_root
    )
    boundary = derive_v70a_repo_candidate_review_boundary_guardrail(repo_root=repo_root)
    validate_v70a_review_classification_bundle(
        source_index=source_index,
        classification_record=classification,
        boundary_guardrail=boundary,
    )
    return source_index, classification, boundary
