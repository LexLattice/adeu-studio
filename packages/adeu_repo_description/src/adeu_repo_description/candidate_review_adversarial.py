from __future__ import annotations

from pathlib import Path
from typing import Literal

from pydantic import Field, model_validator

from .arc_series_cartography import (
    _CartographyBase,
    _non_empty,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)
from .candidate_review_classification import (
    AdversarialReviewPosture,
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateEvidenceSourceIndex,
    _load_json,
    _review_note,
    _surface_id,
)
from .recursive_candidate_intake import OdeuLane

REPO_CANDIDATE_ADVERSARIAL_REVIEW_MATRIX_SCHEMA = (
    "repo_candidate_adversarial_review_matrix@1"
)
REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA = (
    "repo_candidate_review_conflict_register@1"
)
REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA = "repo_candidate_review_gap_scan@1"

ReviewPerspective = Literal[
    "supporting_review",
    "opposing_review",
    "authority_boundary_review",
    "negative_control_review",
    "model_output_comparison_review",
    "operator_pressure_review",
    "tool_applicability_review",
]
ReviewRelationKind = Literal[
    "conflict",
    "complementarity",
    "orthogonal",
    "duplicate",
    "unclear_relation",
]
ReviewConflictKind = Literal[
    "evidence_conflict",
    "authority_boundary_conflict",
    "source_integrity_conflict",
    "model_output_divergence",
    "utility_tradeoff_conflict",
    "operator_pressure_conflict",
    "tool_applicability_conflict",
]
ReviewConflictPosture = Literal[
    "blocking_for_v71",
    "non_blocking_but_carry_forward",
    "requires_more_evidence",
    "requires_human_review",
    "deferred_to_future_family",
]
ReviewGapKind = Literal[
    "missing_adversarial_review",
    "missing_counterevidence",
    "single_source_overclaim",
    "stale_or_missing_source",
    "authority_boundary_unclassified",
    "model_output_without_negative_control",
    "product_wedge_without_v74_boundary",
    "v69_handoff_unclassified",
    "v70a_claim_unreviewed_by_adversarial_matrix",
]
ReviewGapSeverity = Literal["info", "warning", "blocking"]
V70BNextReviewSurface = Literal[
    "v70_adversarial_review",
    "v70c_classification_summary",
    "future_family_review",
    "none_deferred",
]

_V70A_SOURCE_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus194/"
    "repo_candidate_evidence_source_index_v194_reference.json"
)
_V70A_CLASSIFICATION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus194/"
    "repo_candidate_evidence_classification_v194_reference.json"
)


def _v70b_note(value: str, *, field_name: str) -> str:
    normalized = _review_note(value, field_name=field_name)
    lowered = normalized.lower()
    forbidden = ("resolved", "settled", "priority", "ticket")
    if any(token in lowered for token in forbidden):
        raise ValueError(f"{field_name} may not carry settlement or implementation priority")
    return normalized


class RepoCandidateAdversarialReviewRow(_CartographyBase):
    review_ref: str
    candidate_ref: str
    claim_ref: str
    classification_refs: list[str] = Field(min_length=1)
    review_perspective: ReviewPerspective
    review_source_refs: list[str] = Field(min_length=1)
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    adversarial_review_posture: AdversarialReviewPosture
    review_limitation_note: str

    @model_validator(mode="after")
    def _validate_review_row(self) -> RepoCandidateAdversarialReviewRow:
        object.__setattr__(self, "review_ref", _non_empty(self.review_ref, field_name="review_ref"))
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(self, "claim_ref", _non_empty(self.claim_ref, field_name="claim_ref"))
        object.__setattr__(
            self,
            "classification_refs",
            _sorted_unique(self.classification_refs, field_name="classification_refs"),
        )
        object.__setattr__(
            self,
            "review_source_refs",
            _sorted_unique(self.review_source_refs, field_name="review_source_refs"),
        )
        object.__setattr__(
            self,
            "odeu_lanes",
            _sorted_unique(self.odeu_lanes, field_name="odeu_lanes"),
        )
        object.__setattr__(
            self,
            "review_limitation_note",
            _v70b_note(self.review_limitation_note, field_name="review_limitation_note"),
        )
        return self


class RepoCandidateAdversarialReviewMatrix(_CartographyBase):
    schema: Literal["repo_candidate_adversarial_review_matrix@1"] = (
        REPO_CANDIDATE_ADVERSARIAL_REVIEW_MATRIX_SCHEMA
    )
    review_matrix_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    classification_record_id: str
    classification_refs: list[str] = Field(min_length=1)
    adversarial_review_rows: list[RepoCandidateAdversarialReviewRow] = Field(min_length=1)
    non_settlement_summary: str

    @model_validator(mode="after")
    def _validate_review_matrix(self) -> RepoCandidateAdversarialReviewMatrix:
        object.__setattr__(
            self,
            "review_matrix_id",
            _non_empty(self.review_matrix_id, field_name="review_matrix_id"),
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
            "classification_record_id",
            _non_empty(self.classification_record_id, field_name="classification_record_id"),
        )
        object.__setattr__(
            self,
            "classification_refs",
            _sorted_unique(self.classification_refs, field_name="classification_refs"),
        )
        object.__setattr__(
            self,
            "adversarial_review_rows",
            _sorted_unique_by_ref(
                self.adversarial_review_rows,
                attr="review_ref",
                field_name="adversarial_review_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_settlement_summary",
            _v70b_note(self.non_settlement_summary, field_name="non_settlement_summary"),
        )
        known_classification_refs = set(self.classification_refs)
        for row in self.adversarial_review_rows:
            missing_refs = sorted(set(row.classification_refs) - known_classification_refs)
            if missing_refs:
                raise ValueError(
                    "adversarial review rows must reference known classification_refs: "
                    f"{missing_refs}"
                )
        return self


class RepoCandidateReviewRelationRow(_CartographyBase):
    relation_ref: str
    candidate_ref: str
    claim_refs: list[str] = Field(min_length=1)
    review_refs: list[str] = Field(min_length=1)
    review_relation_kind: ReviewRelationKind
    conflict_kind: ReviewConflictKind | None = None
    conflict_posture: ReviewConflictPosture | None = None
    blocking_for_handoff: bool
    required_resolution_surface: V70BNextReviewSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_relation_row(self) -> RepoCandidateReviewRelationRow:
        object.__setattr__(
            self,
            "relation_ref",
            _non_empty(self.relation_ref, field_name="relation_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "claim_refs",
            _sorted_unique(self.claim_refs, field_name="claim_refs"),
        )
        object.__setattr__(
            self,
            "review_refs",
            _sorted_unique(self.review_refs, field_name="review_refs"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v70b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.review_relation_kind == "conflict":
            if self.conflict_kind is None or self.conflict_posture is None:
                raise ValueError("conflict relation rows require conflict kind and posture")
            return self
        if self.conflict_kind is not None or self.conflict_posture is not None:
            raise ValueError("non-conflict relation rows cannot carry conflict posture")
        if self.blocking_for_handoff:
            raise ValueError("non-conflict relation rows cannot block handoff")
        return self


class RepoCandidateReviewConflictRegister(_CartographyBase):
    schema: Literal["repo_candidate_review_conflict_register@1"] = (
        REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA
    )
    conflict_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    review_matrix_id: str
    review_refs: list[str] = Field(min_length=1)
    relation_rows: list[RepoCandidateReviewRelationRow] = Field(min_length=1)
    non_settlement_summary: str

    @model_validator(mode="after")
    def _validate_conflict_register(self) -> RepoCandidateReviewConflictRegister:
        object.__setattr__(
            self,
            "conflict_register_id",
            _non_empty(self.conflict_register_id, field_name="conflict_register_id"),
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
            "review_matrix_id",
            _non_empty(self.review_matrix_id, field_name="review_matrix_id"),
        )
        object.__setattr__(
            self,
            "review_refs",
            _sorted_unique(self.review_refs, field_name="review_refs"),
        )
        object.__setattr__(
            self,
            "relation_rows",
            _sorted_unique_by_ref(
                self.relation_rows,
                attr="relation_ref",
                field_name="relation_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_settlement_summary",
            _v70b_note(self.non_settlement_summary, field_name="non_settlement_summary"),
        )
        known_review_refs = set(self.review_refs)
        for row in self.relation_rows:
            missing_refs = sorted(set(row.review_refs) - known_review_refs)
            if missing_refs:
                raise ValueError(f"relation rows must reference known review_refs: {missing_refs}")
        return self


class RepoCandidateReviewGapRow(_CartographyBase):
    gap_ref: str
    candidate_ref: str
    classification_refs: list[str] = Field(min_length=1)
    gap_kind: ReviewGapKind
    source_refs: list[str] = Field(min_length=1)
    severity: ReviewGapSeverity
    recommended_next_surface: V70BNextReviewSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_gap_row(self) -> RepoCandidateReviewGapRow:
        object.__setattr__(self, "gap_ref", _non_empty(self.gap_ref, field_name="gap_ref"))
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
            "source_refs",
            _sorted_unique(
                [_repo_ref(ref, field_name="source_refs") for ref in self.source_refs],
                field_name="source_refs",
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v70b_note(self.limitation_note, field_name="limitation_note"),
        )
        return self


class RepoCandidateReviewGapScan(_CartographyBase):
    schema: Literal["repo_candidate_review_gap_scan@1"] = (
        REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA
    )
    gap_scan_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    classification_record_id: str
    classification_refs: list[str] = Field(min_length=1)
    gap_rows: list[RepoCandidateReviewGapRow] = Field(min_length=1)
    non_settlement_summary: str

    @model_validator(mode="after")
    def _validate_gap_scan(self) -> RepoCandidateReviewGapScan:
        object.__setattr__(
            self,
            "gap_scan_id",
            _non_empty(self.gap_scan_id, field_name="gap_scan_id"),
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
            "classification_record_id",
            _non_empty(self.classification_record_id, field_name="classification_record_id"),
        )
        object.__setattr__(
            self,
            "classification_refs",
            _sorted_unique(self.classification_refs, field_name="classification_refs"),
        )
        object.__setattr__(
            self,
            "gap_rows",
            _sorted_unique_by_ref(self.gap_rows, attr="gap_ref", field_name="gap_rows"),
        )
        object.__setattr__(
            self,
            "non_settlement_summary",
            _v70b_note(self.non_settlement_summary, field_name="non_settlement_summary"),
        )
        known_classification_refs = set(self.classification_refs)
        for row in self.gap_rows:
            missing_refs = sorted(set(row.classification_refs) - known_classification_refs)
            if missing_refs:
                raise ValueError(
                    f"gap rows must reference known classification_refs: {missing_refs}"
                )
        return self


def validate_v70b_candidate_review_bundle(
    *,
    source_index: RepoCandidateEvidenceSourceIndex,
    classification_record: RepoCandidateEvidenceClassificationRecord,
    adversarial_review_matrix: RepoCandidateAdversarialReviewMatrix,
    conflict_register: RepoCandidateReviewConflictRegister,
    gap_scan: RepoCandidateReviewGapScan,
) -> None:
    if classification_record.snapshot_id != source_index.snapshot_id:
        raise ValueError("V70-A source and classification snapshot_id must match")
    if adversarial_review_matrix.source_set_id != classification_record.source_set_id:
        raise ValueError("adversarial review matrix source_set_id must match V70-A")
    if conflict_register.source_set_id != adversarial_review_matrix.source_set_id:
        raise ValueError("conflict register source_set_id must match adversarial review matrix")
    if gap_scan.source_set_id != adversarial_review_matrix.source_set_id:
        raise ValueError("gap scan source_set_id must match adversarial review matrix")
    if conflict_register.review_matrix_id != adversarial_review_matrix.review_matrix_id:
        raise ValueError("conflict register must reference adversarial review matrix")

    classification_rows = {
        row.classification_ref: row for row in classification_record.claim_classification_rows
    }
    claim_rows = {row.claim_ref: row for row in classification_record.claim_rows}
    known_classification_refs = set(classification_rows)
    if set(adversarial_review_matrix.classification_refs) != known_classification_refs:
        raise ValueError("adversarial review matrix classification_refs must match V70-A")
    if set(gap_scan.classification_refs) != known_classification_refs:
        raise ValueError("gap scan classification_refs must match V70-A")

    source_refs = {row.evidence_source_ref for row in source_index.evidence_source_rows}
    review_rows_by_classification: dict[str, list[RepoCandidateAdversarialReviewRow]] = {
        ref: [] for ref in known_classification_refs
    }
    for row in adversarial_review_matrix.adversarial_review_rows:
        for classification_ref in row.classification_refs:
            classification = classification_rows.get(classification_ref)
            if classification is None:
                raise ValueError("adversarial review rows must reference known classifications")
            if row.candidate_ref != classification.candidate_ref:
                raise ValueError("adversarial review row candidate_ref must match classification")
            if row.claim_ref != classification.claim_ref:
                raise ValueError("adversarial review row claim_ref must match classification")
            if row.odeu_lanes != classification.odeu_lanes:
                raise ValueError("adversarial review row odeu_lanes must match classification")
            missing_source_refs = sorted(set(row.review_source_refs) - source_refs)
            if missing_source_refs:
                raise ValueError(
                    f"adversarial review rows must reference known sources: {missing_source_refs}"
                )
            review_rows_by_classification[classification_ref].append(row)

    uncovered = sorted(
        ref
        for ref, classification in classification_rows.items()
        if not review_rows_by_classification[ref]
        and classification.adversarial_review_posture != "not_required_for_this_claim"
    )
    if uncovered:
        raise ValueError(f"V70-A classifications need adversarial review rows: {uncovered}")

    for classification_ref, classification in classification_rows.items():
        claim = claim_rows[classification.claim_ref]
        if claim.candidate_origin_class != "model_output":
            continue
        review_perspectives = {
            row.review_perspective for row in review_rows_by_classification[classification_ref]
        }
        if not review_perspectives.intersection({"opposing_review", "negative_control_review"}):
            raise ValueError("model-output comparison review requires opposing or negative control")

    review_refs = {row.review_ref for row in adversarial_review_matrix.adversarial_review_rows}
    if set(conflict_register.review_refs) != review_refs:
        raise ValueError("conflict register review_refs must match adversarial review rows")

    gap_kinds = {row.gap_kind for row in gap_scan.gap_rows}
    if "single_source_overclaim" not in gap_kinds:
        raise ValueError("gap scan must preserve single_source_overclaim")
    if "product_wedge_without_v74_boundary" not in gap_kinds:
        raise ValueError("gap scan must preserve product_wedge_without_v74_boundary")

    product_boundary_refs = {
        row.classification_ref
        for row in classification_record.claim_classification_rows
        if row.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
    }
    if product_boundary_refs and not any(
        row.gap_kind == "product_wedge_without_v74_boundary"
        and product_boundary_refs.intersection(row.classification_refs)
        for row in gap_scan.gap_rows
    ):
        raise ValueError("product wedge review requires explicit V74 boundary gap")


def derive_v70b_repo_candidate_adversarial_review_matrix(
    *,
    repo_root: Path,
) -> RepoCandidateAdversarialReviewMatrix:
    classification = RepoCandidateEvidenceClassificationRecord.model_validate(
        _load_json(repo_root, _V70A_CLASSIFICATION_FIXTURE)
    )
    rows = [
        RepoCandidateAdversarialReviewRow(
            review_ref="review-row:v70b:odeu-diff:negative-control",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            claim_ref="claim:v70a:odeu-diff:adversarial-review-need",
            classification_refs=[
                "classification:v70a:odeu-diff:requires-adversarial-review"
            ],
            review_perspective="negative_control_review",
            review_source_refs=["evidence-source:v70a:v69c-handoff-fixture"],
            odeu_lanes=["epistemic"],
            adversarial_review_posture="required_present",
            review_limitation_note=(
                "Negative-control review is recorded as classification support only."
            ),
        ),
        RepoCandidateAdversarialReviewRow(
            review_ref="review-row:v70b:product-wedge:authority-boundary",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            claim_ref="claim:v70a:product-wedge:authority-boundary",
            classification_refs=["classification:v70a:product-wedge:authority-boundary"],
            review_perspective="authority_boundary_review",
            review_source_refs=["evidence-source:v70a:gptpro-review"],
            odeu_lanes=["deontic", "utility"],
            adversarial_review_posture="deferred_to_future_family_review",
            review_limitation_note="Product pressure remains bounded review material only.",
        ),
        RepoCandidateAdversarialReviewRow(
            review_ref="review-row:v70b:self-evidencing:supporting",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            claim_ref="claim:v70a:self-evidencing:source-bound",
            classification_refs=["classification:v70a:self-evidencing:source-bound"],
            review_perspective="supporting_review",
            review_source_refs=["evidence-source:v70a:v69-closeout"],
            odeu_lanes=["deontic", "epistemic", "ontological"],
            adversarial_review_posture="not_required_for_this_claim",
            review_limitation_note="Supporting review records source binding only.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_ADVERSARIAL_REVIEW_MATRIX_SCHEMA,
        "review_id": "review:v70b:adversarial-review-gap-scan",
        "snapshot_id": "vNext+195-prestart-on-main",
        "source_set_id": classification.source_set_id,
        "classification_record_id": classification.classification_record_id,
        "classification_refs": [
            row.classification_ref for row in classification.claim_classification_rows
        ],
        "adversarial_review_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.review_ref)
        ],
        "non_settlement_summary": "V70-B adversarial review rows are classification support only.",
    }
    payload["review_matrix_id"] = _surface_id(
        "repo_candidate_adversarial_review_matrix",
        REPO_CANDIDATE_ADVERSARIAL_REVIEW_MATRIX_SCHEMA,
        payload,
        "review_matrix_id",
    )
    return RepoCandidateAdversarialReviewMatrix.model_validate(payload)


def derive_v70b_repo_candidate_review_conflict_register(
    *,
    repo_root: Path,
) -> RepoCandidateReviewConflictRegister:
    matrix = derive_v70b_repo_candidate_adversarial_review_matrix(repo_root=repo_root)
    rows = [
        RepoCandidateReviewRelationRow(
            relation_ref="relation:v70b:odeu-diff:model-output-divergence",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            claim_refs=["claim:v70a:odeu-diff:adversarial-review-need"],
            review_refs=["review-row:v70b:odeu-diff:negative-control"],
            review_relation_kind="conflict",
            conflict_kind="model_output_divergence",
            conflict_posture="requires_more_evidence",
            blocking_for_handoff=True,
            required_resolution_surface="v70c_classification_summary",
            limitation_note="Divergence remains open review pressure.",
        ),
        RepoCandidateReviewRelationRow(
            relation_ref="relation:v70b:product-wedge:authority-boundary",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            claim_refs=["claim:v70a:product-wedge:authority-boundary"],
            review_refs=["review-row:v70b:product-wedge:authority-boundary"],
            review_relation_kind="conflict",
            conflict_kind="authority_boundary_conflict",
            conflict_posture="deferred_to_future_family",
            blocking_for_handoff=True,
            required_resolution_surface="future_family_review",
            limitation_note="Product boundary pressure stays deferred to future review.",
        ),
        RepoCandidateReviewRelationRow(
            relation_ref="relation:v70b:self-evidencing:complementarity",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            claim_refs=["claim:v70a:self-evidencing:source-bound"],
            review_refs=["review-row:v70b:self-evidencing:supporting"],
            review_relation_kind="complementarity",
            blocking_for_handoff=False,
            required_resolution_surface="v70c_classification_summary",
            limitation_note="Complementary source-binding review carries forward.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA,
        "review_id": "review:v70b:adversarial-review-gap-scan",
        "snapshot_id": "vNext+195-prestart-on-main",
        "source_set_id": matrix.source_set_id,
        "review_matrix_id": matrix.review_matrix_id,
        "review_refs": [row.review_ref for row in matrix.adversarial_review_rows],
        "relation_rows": [
            row.model_dump(mode="json", exclude_none=True)
            for row in sorted(rows, key=lambda row: row.relation_ref)
        ],
        "non_settlement_summary": "V70-B relation rows expose posture without settlement.",
    }
    payload["conflict_register_id"] = _surface_id(
        "repo_candidate_review_conflict_register",
        REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA,
        payload,
        "conflict_register_id",
    )
    return RepoCandidateReviewConflictRegister.model_validate(payload)


def derive_v70b_repo_candidate_review_gap_scan(
    *,
    repo_root: Path,
) -> RepoCandidateReviewGapScan:
    classification = RepoCandidateEvidenceClassificationRecord.model_validate(
        _load_json(repo_root, _V70A_CLASSIFICATION_FIXTURE)
    )
    rows = [
        RepoCandidateReviewGapRow(
            gap_ref="gap:v70b:odeu-diff:missing-counterevidence",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            classification_refs=[
                "classification:v70a:odeu-diff:requires-adversarial-review"
            ],
            gap_kind="missing_counterevidence",
            source_refs=["evidence-source:v70a:v69c-handoff-fixture"],
            severity="blocking",
            recommended_next_surface="v70_adversarial_review",
            limitation_note="Counterevidence remains needed before summary.",
        ),
        RepoCandidateReviewGapRow(
            gap_ref="gap:v70b:product-wedge:single-source-overclaim",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            classification_refs=["classification:v70a:product-wedge:authority-boundary"],
            gap_kind="single_source_overclaim",
            source_refs=["evidence-source:v70a:gptpro-review"],
            severity="warning",
            recommended_next_surface="future_family_review",
            limitation_note="Product wedge currently rests on one review source.",
        ),
        RepoCandidateReviewGapRow(
            gap_ref="gap:v70b:product-wedge:v74-boundary",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            classification_refs=["classification:v70a:product-wedge:authority-boundary"],
            gap_kind="product_wedge_without_v74_boundary",
            source_refs=["evidence-source:v70a:gptpro-review"],
            severity="blocking",
            recommended_next_surface="future_family_review",
            limitation_note="Product projection requires a later boundary review.",
        ),
        RepoCandidateReviewGapRow(
            gap_ref="gap:v70b:self-evidencing:carry-forward-review",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            classification_refs=["classification:v70a:self-evidencing:source-bound"],
            gap_kind="authority_boundary_unclassified",
            source_refs=["evidence-source:v70a:v69-closeout"],
            severity="info",
            recommended_next_surface="v70c_classification_summary",
            limitation_note="Carry-forward boundary note remains for summary.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA,
        "review_id": "review:v70b:adversarial-review-gap-scan",
        "snapshot_id": "vNext+195-prestart-on-main",
        "source_set_id": classification.source_set_id,
        "classification_record_id": classification.classification_record_id,
        "classification_refs": [
            row.classification_ref for row in classification.claim_classification_rows
        ],
        "gap_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.gap_ref)
        ],
        "non_settlement_summary": "V70-B gap rows recommend review surfaces only.",
    }
    payload["gap_scan_id"] = _surface_id(
        "repo_candidate_review_gap_scan",
        REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA,
        payload,
        "gap_scan_id",
    )
    return RepoCandidateReviewGapScan.model_validate(payload)


def derive_v70b_repo_candidate_review_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoCandidateEvidenceSourceIndex,
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateAdversarialReviewMatrix,
    RepoCandidateReviewConflictRegister,
    RepoCandidateReviewGapScan,
]:
    source_index = RepoCandidateEvidenceSourceIndex.model_validate(
        _load_json(repo_root, _V70A_SOURCE_FIXTURE)
    )
    classification = RepoCandidateEvidenceClassificationRecord.model_validate(
        _load_json(repo_root, _V70A_CLASSIFICATION_FIXTURE)
    )
    matrix = derive_v70b_repo_candidate_adversarial_review_matrix(repo_root=repo_root)
    conflict_register = derive_v70b_repo_candidate_review_conflict_register(repo_root=repo_root)
    gap_scan = derive_v70b_repo_candidate_review_gap_scan(repo_root=repo_root)
    validate_v70b_candidate_review_bundle(
        source_index=source_index,
        classification_record=classification,
        adversarial_review_matrix=matrix,
        conflict_register=conflict_register,
        gap_scan=gap_scan,
    )
    return source_index, classification, matrix, conflict_register, gap_scan
