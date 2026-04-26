from __future__ import annotations

from pathlib import Path
from typing import Literal

from pydantic import Field, model_validator

from .arc_series_cartography import (
    _CartographyBase,
    _non_empty,
    _sorted_unique,
    _sorted_unique_by_ref,
)
from .candidate_review_adversarial import (
    RepoCandidateAdversarialReviewMatrix,
    RepoCandidateReviewConflictRegister,
    RepoCandidateReviewGapScan,
    validate_v70b_candidate_review_bundle,
)
from .candidate_review_classification import (
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateEvidenceSourceIndex,
    _load_json,
    _surface_id,
)
from .recursive_candidate_intake import _non_authority_note

REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA = (
    "repo_candidate_review_classification_summary@1"
)
REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA = "repo_candidate_pre_ratification_handoff@1"

SummaryPosture = Literal[
    "classified_ready_for_later_review",
    "classified_needs_more_evidence",
    "classified_blocked_by_conflict",
    "classified_blocked_by_authority_boundary",
    "classified_deferred_to_future_family",
    "classified_rejected_out_of_scope",
]
HandoffReadiness = Literal[
    "ready_for_later_review",
    "blocked_by_conflict",
    "blocked_by_evidence_gap",
    "blocked_by_authority_boundary",
    "deferred_to_future_family",
    "rejected_out_of_scope",
]
HandoffTarget = Literal[
    "v71_ratification_review",
    "future_family_review",
    "deferred_no_selection",
]
HandoffPosture = Literal[
    "ready_for_v71_review",
    "request_settlement_not_ratification",
    "blocked_by_conflict",
    "blocked_by_evidence_gap",
    "blocked_by_authority_boundary",
    "deferred_to_future_family",
    "rejected_out_of_scope",
]
RequiredResolutionSurface = Literal[
    "v70c_classification_summary",
    "v71_ratification_review",
    "future_family_review",
    "deferred_no_selection",
]

_V70A_SOURCE_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus194/"
    "repo_candidate_evidence_source_index_v194_reference.json"
)
_V70A_CLASSIFICATION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus194/"
    "repo_candidate_evidence_classification_v194_reference.json"
)
_V70B_MATRIX_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus195/"
    "repo_candidate_adversarial_review_matrix_v195_reference.json"
)
_V70B_CONFLICT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus195/"
    "repo_candidate_review_conflict_register_v195_reference.json"
)
_V70B_GAP_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus195/"
    "repo_candidate_review_gap_scan_v195_reference.json"
)


def _v70c_note(value: str, *, field_name: str) -> str:
    normalized = _non_authority_note(value, field_name=field_name)
    lowered = normalized.lower()
    forbidden = (
        "adoption",
        "authorization",
        "authorized",
        "dispatch",
        "implementation ticket",
        "product authorization",
        "release authority",
        "truth verdict",
    )
    if any(token in lowered for token in forbidden):
        raise ValueError(f"{field_name} may not carry downstream authority")
    return normalized


class RepoCandidateReviewClassificationSummaryRow(_CartographyBase):
    summary_ref: str
    candidate_ref: str
    classification_refs: list[str] = Field(min_length=1)
    adversarial_review_refs: list[str] = Field(default_factory=list)
    conflict_refs: list[str] = Field(default_factory=list)
    gap_refs: list[str] = Field(default_factory=list)
    summary_posture: SummaryPosture
    handoff_readiness: HandoffReadiness
    non_authority_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_summary_row(self) -> RepoCandidateReviewClassificationSummaryRow:
        object.__setattr__(
            self, "summary_ref", _non_empty(self.summary_ref, field_name="summary_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        object.__setattr__(
            self,
            "classification_refs",
            _sorted_unique(self.classification_refs, field_name="classification_refs"),
        )
        object.__setattr__(
            self,
            "adversarial_review_refs",
            _sorted_unique(self.adversarial_review_refs, field_name="adversarial_review_refs"),
        )
        object.__setattr__(
            self, "conflict_refs", _sorted_unique(self.conflict_refs, field_name="conflict_refs")
        )
        object.__setattr__(self, "gap_refs", _sorted_unique(self.gap_refs, field_name="gap_refs"))
        object.__setattr__(
            self,
            "non_authority_guardrail",
            _v70c_note(self.non_authority_guardrail, field_name="non_authority_guardrail"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v70c_note(self.limitation_note, field_name="limitation_note"),
        )
        if (
            self.summary_posture == "classified_ready_for_later_review"
            and self.handoff_readiness != "ready_for_later_review"
        ):
            raise ValueError("ready summary posture requires ready handoff readiness")
        if (
            self.summary_posture != "classified_ready_for_later_review"
            and self.handoff_readiness == "ready_for_later_review"
        ):
            raise ValueError("ready handoff readiness requires ready summary posture")
        return self


class RepoCandidateReviewClassificationSummary(_CartographyBase):
    schema: Literal["repo_candidate_review_classification_summary@1"] = (
        REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA
    )
    summary_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    classification_record_id: str
    review_matrix_id: str
    conflict_register_id: str
    gap_scan_id: str
    classification_refs: list[str] = Field(min_length=1)
    adversarial_review_refs: list[str] = Field(min_length=1)
    conflict_refs: list[str] = Field(default_factory=list)
    gap_refs: list[str] = Field(default_factory=list)
    summary_rows: list[RepoCandidateReviewClassificationSummaryRow] = Field(min_length=1)
    non_ratification_summary: str

    @model_validator(mode="after")
    def _validate_summary_register(self) -> RepoCandidateReviewClassificationSummary:
        object.__setattr__(
            self,
            "summary_register_id",
            _non_empty(self.summary_register_id, field_name="summary_register_id"),
        )
        object.__setattr__(self, "review_id", _non_empty(self.review_id, field_name="review_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self, "source_set_id", _non_empty(self.source_set_id, field_name="source_set_id")
        )
        object.__setattr__(
            self,
            "classification_record_id",
            _non_empty(self.classification_record_id, field_name="classification_record_id"),
        )
        object.__setattr__(
            self,
            "review_matrix_id",
            _non_empty(self.review_matrix_id, field_name="review_matrix_id"),
        )
        object.__setattr__(
            self,
            "conflict_register_id",
            _non_empty(self.conflict_register_id, field_name="conflict_register_id"),
        )
        object.__setattr__(
            self, "gap_scan_id", _non_empty(self.gap_scan_id, field_name="gap_scan_id")
        )
        object.__setattr__(
            self,
            "classification_refs",
            _sorted_unique(self.classification_refs, field_name="classification_refs"),
        )
        object.__setattr__(
            self,
            "adversarial_review_refs",
            _sorted_unique(self.adversarial_review_refs, field_name="adversarial_review_refs"),
        )
        object.__setattr__(
            self, "conflict_refs", _sorted_unique(self.conflict_refs, field_name="conflict_refs")
        )
        object.__setattr__(self, "gap_refs", _sorted_unique(self.gap_refs, field_name="gap_refs"))
        object.__setattr__(
            self,
            "summary_rows",
            _sorted_unique_by_ref(self.summary_rows, attr="summary_ref", field_name="summary_rows"),
        )
        object.__setattr__(
            self,
            "non_ratification_summary",
            _v70c_note(self.non_ratification_summary, field_name="non_ratification_summary"),
        )
        known_classification_refs = set(self.classification_refs)
        known_review_refs = set(self.adversarial_review_refs)
        known_conflict_refs = set(self.conflict_refs)
        known_gap_refs = set(self.gap_refs)
        for row in self.summary_rows:
            missing_classifications = sorted(
                set(row.classification_refs) - known_classification_refs
            )
            if missing_classifications:
                raise ValueError(
                    "summary rows must reference known classification_refs: "
                    f"{missing_classifications}"
                )
            missing_reviews = sorted(set(row.adversarial_review_refs) - known_review_refs)
            if missing_reviews:
                raise ValueError(
                    f"summary rows must reference known adversarial_review_refs: {missing_reviews}"
                )
            missing_conflicts = sorted(set(row.conflict_refs) - known_conflict_refs)
            if missing_conflicts:
                raise ValueError(
                    f"summary rows must reference known conflict_refs: {missing_conflicts}"
                )
            missing_gaps = sorted(set(row.gap_refs) - known_gap_refs)
            if missing_gaps:
                raise ValueError(f"summary rows must reference known gap_refs: {missing_gaps}")
        expected_id = _surface_id(
            "repo_candidate_review_classification_summary",
            REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA,
            self.model_dump(mode="json"),
            "summary_register_id",
        )
        if self.summary_register_id != expected_id:
            raise ValueError("summary_register_id must match canonical full payload hash identity")
        return self


class RepoCandidatePreRatificationHandoffRow(_CartographyBase):
    handoff_ref: str
    summary_ref: str
    candidate_ref: str
    handoff_target: HandoffTarget
    handoff_posture: HandoffPosture
    classification_refs: list[str] = Field(min_length=1)
    adversarial_review_refs: list[str] = Field(default_factory=list)
    unresolved_gap_refs: list[str] = Field(default_factory=list)
    blocking_conflict_refs: list[str] = Field(default_factory=list)
    required_resolution_surface: RequiredResolutionSurface
    non_authority_guardrail: str

    @model_validator(mode="after")
    def _validate_handoff_row(self) -> RepoCandidatePreRatificationHandoffRow:
        object.__setattr__(
            self, "handoff_ref", _non_empty(self.handoff_ref, field_name="handoff_ref")
        )
        object.__setattr__(
            self, "summary_ref", _non_empty(self.summary_ref, field_name="summary_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        object.__setattr__(
            self,
            "classification_refs",
            _sorted_unique(self.classification_refs, field_name="classification_refs"),
        )
        object.__setattr__(
            self,
            "adversarial_review_refs",
            _sorted_unique(self.adversarial_review_refs, field_name="adversarial_review_refs"),
        )
        object.__setattr__(
            self,
            "unresolved_gap_refs",
            _sorted_unique(self.unresolved_gap_refs, field_name="unresolved_gap_refs"),
        )
        object.__setattr__(
            self,
            "blocking_conflict_refs",
            _sorted_unique(self.blocking_conflict_refs, field_name="blocking_conflict_refs"),
        )
        object.__setattr__(
            self,
            "non_authority_guardrail",
            _v70c_note(self.non_authority_guardrail, field_name="non_authority_guardrail"),
        )
        if self.handoff_posture == "ready_for_v71_review" and (
            self.unresolved_gap_refs or self.blocking_conflict_refs
        ):
            raise ValueError("ready_for_v71_review cannot carry unresolved blockers")
        if self.handoff_target == "v71_ratification_review":
            guardrail = self.non_authority_guardrail.lower()
            if "later review" not in guardrail or "not a decision" not in guardrail:
                raise ValueError("v71 handoff requires an explicit non-authority guardrail")
        if (
            self.handoff_posture == "ready_for_v71_review"
            and self.handoff_target != "v71_ratification_review"
        ):
            raise ValueError("ready_for_v71_review requires v71 handoff target")
        return self


class RepoCandidatePreRatificationHandoff(_CartographyBase):
    schema: Literal["repo_candidate_pre_ratification_handoff@1"] = (
        REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA
    )
    handoff_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    summary_register_id: str
    handoff_rows: list[RepoCandidatePreRatificationHandoffRow] = Field(min_length=1)
    non_ratification_summary: str

    @model_validator(mode="after")
    def _validate_handoff_register(self) -> RepoCandidatePreRatificationHandoff:
        object.__setattr__(
            self,
            "handoff_register_id",
            _non_empty(self.handoff_register_id, field_name="handoff_register_id"),
        )
        object.__setattr__(self, "review_id", _non_empty(self.review_id, field_name="review_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self, "source_set_id", _non_empty(self.source_set_id, field_name="source_set_id")
        )
        object.__setattr__(
            self,
            "summary_register_id",
            _non_empty(self.summary_register_id, field_name="summary_register_id"),
        )
        object.__setattr__(
            self,
            "handoff_rows",
            _sorted_unique_by_ref(self.handoff_rows, attr="handoff_ref", field_name="handoff_rows"),
        )
        object.__setattr__(
            self,
            "non_ratification_summary",
            _v70c_note(self.non_ratification_summary, field_name="non_ratification_summary"),
        )
        expected_id = _surface_id(
            "repo_candidate_pre_ratification_handoff",
            REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA,
            self.model_dump(mode="json"),
            "handoff_register_id",
        )
        if self.handoff_register_id != expected_id:
            raise ValueError("handoff_register_id must match canonical full payload hash identity")
        return self


def validate_v70c_candidate_review_summary_bundle(
    *,
    source_index: RepoCandidateEvidenceSourceIndex,
    classification_record: RepoCandidateEvidenceClassificationRecord,
    adversarial_review_matrix: RepoCandidateAdversarialReviewMatrix,
    conflict_register: RepoCandidateReviewConflictRegister,
    gap_scan: RepoCandidateReviewGapScan,
    classification_summary: RepoCandidateReviewClassificationSummary,
    pre_ratification_handoff: RepoCandidatePreRatificationHandoff,
) -> None:
    validate_v70b_candidate_review_bundle(
        source_index=source_index,
        classification_record=classification_record,
        adversarial_review_matrix=adversarial_review_matrix,
        conflict_register=conflict_register,
        gap_scan=gap_scan,
    )
    if pre_ratification_handoff.review_id != classification_summary.review_id:
        raise ValueError("V70-C review_id must match across summary and handoff")
    if pre_ratification_handoff.snapshot_id != classification_summary.snapshot_id:
        raise ValueError("V70-C snapshot_id must match across summary and handoff")
    if pre_ratification_handoff.source_set_id != classification_summary.source_set_id:
        raise ValueError("V70-C source_set_id must match across summary and handoff")
    if pre_ratification_handoff.summary_register_id != classification_summary.summary_register_id:
        raise ValueError("handoff must reference classification summary")
    if classification_summary.source_set_id != classification_record.source_set_id:
        raise ValueError("classification summary source_set_id must match V70-A")
    if (
        classification_summary.classification_record_id
        != classification_record.classification_record_id
    ):
        raise ValueError("classification summary classification_record_id must match V70-A")
    if classification_summary.review_matrix_id != adversarial_review_matrix.review_matrix_id:
        raise ValueError("classification summary review_matrix_id must match V70-B")
    if classification_summary.conflict_register_id != conflict_register.conflict_register_id:
        raise ValueError("classification summary conflict_register_id must match V70-B")
    if classification_summary.gap_scan_id != gap_scan.gap_scan_id:
        raise ValueError("classification summary gap_scan_id must match V70-B")

    classification_rows = {
        row.classification_ref: row for row in classification_record.claim_classification_rows
    }
    review_rows = {row.review_ref: row for row in adversarial_review_matrix.adversarial_review_rows}
    conflict_rows = {row.relation_ref: row for row in conflict_register.relation_rows}
    gap_rows = {row.gap_ref: row for row in gap_scan.gap_rows}
    summary_rows = {row.summary_ref: row for row in classification_summary.summary_rows}
    if set(classification_summary.classification_refs) != set(classification_rows):
        raise ValueError("classification summary classification_refs must match V70-A")
    if set(classification_summary.adversarial_review_refs) != set(review_rows):
        raise ValueError("classification summary adversarial_review_refs must match V70-B")
    if set(classification_summary.conflict_refs) != set(conflict_rows):
        raise ValueError("classification summary conflict_refs must match V70-B relation rows")
    if set(classification_summary.gap_refs) != set(gap_rows):
        raise ValueError("classification summary gap_refs must match V70-B gap rows")

    blocking_conflicts_by_candidate: dict[str, set[str]] = {}
    relation_refs_by_candidate: dict[str, set[str]] = {}
    for conflict_ref, relation in conflict_rows.items():
        relation_refs_by_candidate.setdefault(relation.candidate_ref, set()).add(conflict_ref)
        for review_ref in relation.review_refs:
            if review_rows[review_ref].candidate_ref != relation.candidate_ref:
                raise ValueError("relation candidate_ref must match referenced review rows")
        if relation.blocking_for_handoff:
            blocking_conflicts_by_candidate.setdefault(relation.candidate_ref, set()).add(
                conflict_ref
            )
    blocking_gaps_by_candidate: dict[str, set[str]] = {}
    gaps_by_candidate: dict[str, set[str]] = {}
    for gap_ref, gap in gap_rows.items():
        gaps_by_candidate.setdefault(gap.candidate_ref, set()).add(gap_ref)
        if gap.severity == "blocking":
            blocking_gaps_by_candidate.setdefault(gap.candidate_ref, set()).add(gap_ref)

    covered_candidates: set[str] = set()
    for summary in classification_summary.summary_rows:
        covered_candidates.add(summary.candidate_ref)
        for classification_ref in summary.classification_refs:
            if classification_rows[classification_ref].candidate_ref != summary.candidate_ref:
                raise ValueError("summary candidate_ref must match referenced classifications")
        for review_ref in summary.adversarial_review_refs:
            if review_rows[review_ref].candidate_ref != summary.candidate_ref:
                raise ValueError("summary candidate_ref must match referenced review rows")
        for conflict_ref in summary.conflict_refs:
            if conflict_rows[conflict_ref].candidate_ref != summary.candidate_ref:
                raise ValueError("summary candidate_ref must match referenced conflict rows")
        for gap_ref in summary.gap_refs:
            if gap_rows[gap_ref].candidate_ref != summary.candidate_ref:
                raise ValueError("summary candidate_ref must match referenced gap rows")
        expected_relations = sorted(relation_refs_by_candidate.get(summary.candidate_ref, set()))
        if summary.conflict_refs != expected_relations:
            raise ValueError(
                "summary conflict_refs must exactly match and be lexicographically sorted: "
                f"{expected_relations}"
            )
        expected_gaps = sorted(gaps_by_candidate.get(summary.candidate_ref, set()))
        if summary.gap_refs != expected_gaps:
            raise ValueError(
                "summary gap_refs must exactly match and be lexicographically sorted: "
                f"{expected_gaps}"
            )
        has_blockers = bool(
            blocking_conflicts_by_candidate.get(summary.candidate_ref)
            or blocking_gaps_by_candidate.get(summary.candidate_ref)
        )
        if has_blockers and summary.summary_posture == "classified_ready_for_later_review":
            raise ValueError("summary cannot be ready with unresolved blockers")
        if (
            summary.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
            and summary.summary_posture == "classified_ready_for_later_review"
        ):
            raise ValueError("product wedge summary cannot be product authorization")

    classified_candidates = {
        row.candidate_ref for row in classification_record.claim_classification_rows
    }
    if covered_candidates != classified_candidates:
        raise ValueError("classification summaries must cover every classified candidate")

    covered_summary_refs: set[str] = set()
    for handoff in pre_ratification_handoff.handoff_rows:
        if handoff.summary_ref in covered_summary_refs:
            raise ValueError("handoff rows must reference each summary at most once")
        covered_summary_refs.add(handoff.summary_ref)
        summary = summary_rows.get(handoff.summary_ref)
        if summary is None:
            raise ValueError("handoff rows must reference known summary rows")
        if handoff.candidate_ref != summary.candidate_ref:
            raise ValueError("handoff candidate_ref must match referenced summary")
        if set(handoff.classification_refs) != set(summary.classification_refs):
            raise ValueError("handoff classification_refs must match summary")
        missing_reviews = sorted(
            set(handoff.adversarial_review_refs) - set(summary.adversarial_review_refs)
        )
        if missing_reviews:
            raise ValueError(
                f"handoff adversarial_review_refs must come from summary: {missing_reviews}"
            )
        expected_blocking_conflicts = sorted(
            blocking_conflicts_by_candidate.get(handoff.candidate_ref, set())
        )
        if handoff.blocking_conflict_refs != expected_blocking_conflicts:
            raise ValueError(
                "handoff blocking_conflict_refs must exactly match and be lexicographically sorted"
            )
        expected_blocking_gaps = sorted(
            blocking_gaps_by_candidate.get(handoff.candidate_ref, set())
        )
        if handoff.unresolved_gap_refs != expected_blocking_gaps:
            raise ValueError(
                "handoff unresolved_gap_refs must exactly match and be lexicographically sorted"
            )
        has_blockers = bool(handoff.blocking_conflict_refs or handoff.unresolved_gap_refs)
        if has_blockers and handoff.handoff_posture == "ready_for_v71_review":
            raise ValueError("handoff cannot be ready with blockers")
        if (
            handoff.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
            and handoff.handoff_target == "v71_ratification_review"
        ):
            raise ValueError("product wedge handoff must stay deferred to future family review")
    missing_handoffs = sorted(set(summary_rows) - covered_summary_refs)
    if missing_handoffs:
        raise ValueError(f"handoff rows must cover every summary row: {missing_handoffs}")


def derive_v70c_repo_candidate_review_classification_summary(
    *,
    repo_root: Path,
) -> RepoCandidateReviewClassificationSummary:
    classification = RepoCandidateEvidenceClassificationRecord.model_validate(
        _load_json(repo_root, _V70A_CLASSIFICATION_FIXTURE)
    )
    matrix = RepoCandidateAdversarialReviewMatrix.model_validate(
        _load_json(repo_root, _V70B_MATRIX_FIXTURE)
    )
    conflict_register = RepoCandidateReviewConflictRegister.model_validate(
        _load_json(repo_root, _V70B_CONFLICT_FIXTURE)
    )
    gap_scan = RepoCandidateReviewGapScan.model_validate(_load_json(repo_root, _V70B_GAP_FIXTURE))
    rows = [
        RepoCandidateReviewClassificationSummaryRow(
            summary_ref="summary:v70c:odeu-diff:blocking-review",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            classification_refs=["classification:v70a:odeu-diff:requires-adversarial-review"],
            adversarial_review_refs=["review-row:v70b:odeu-diff:negative-control"],
            conflict_refs=["relation:v70b:odeu-diff:model-output-divergence"],
            gap_refs=["gap:v70b:odeu-diff:missing-counterevidence"],
            summary_posture="classified_blocked_by_conflict",
            handoff_readiness="blocked_by_conflict",
            non_authority_guardrail="Carry forward for later review only; not a decision.",
            limitation_note="Model-output divergence remains blocked by counterevidence needs.",
        ),
        RepoCandidateReviewClassificationSummaryRow(
            summary_ref="summary:v70c:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            classification_refs=["classification:v70a:product-wedge:authority-boundary"],
            adversarial_review_refs=["review-row:v70b:product-wedge:authority-boundary"],
            conflict_refs=["relation:v70b:product-wedge:authority-boundary"],
            gap_refs=[
                "gap:v70b:product-wedge:single-source-overclaim",
                "gap:v70b:product-wedge:v74-boundary",
            ],
            summary_posture="classified_deferred_to_future_family",
            handoff_readiness="deferred_to_future_family",
            non_authority_guardrail="Carry forward for future review only; not a decision.",
            limitation_note="Product pressure remains deferred to later boundary review.",
        ),
        RepoCandidateReviewClassificationSummaryRow(
            summary_ref="summary:v70c:self-evidencing:ready-review",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            classification_refs=["classification:v70a:self-evidencing:source-bound"],
            adversarial_review_refs=["review-row:v70b:self-evidencing:supporting"],
            conflict_refs=["relation:v70b:self-evidencing:complementarity"],
            gap_refs=["gap:v70b:self-evidencing:carry-forward-review"],
            summary_posture="classified_ready_for_later_review",
            handoff_readiness="ready_for_later_review",
            non_authority_guardrail="Carry forward for later review only; not a decision.",
            limitation_note="Source-bound workflow residue is ready for later review.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA,
        "review_id": "review:v70c:summary-pre-ratification-handoff",
        "snapshot_id": "vNext+196-prestart-on-main",
        "source_set_id": classification.source_set_id,
        "classification_record_id": classification.classification_record_id,
        "review_matrix_id": matrix.review_matrix_id,
        "conflict_register_id": conflict_register.conflict_register_id,
        "gap_scan_id": gap_scan.gap_scan_id,
        "classification_refs": [
            row.classification_ref for row in classification.claim_classification_rows
        ],
        "adversarial_review_refs": [row.review_ref for row in matrix.adversarial_review_rows],
        "conflict_refs": [row.relation_ref for row in conflict_register.relation_rows],
        "gap_refs": [row.gap_ref for row in gap_scan.gap_rows],
        "summary_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.summary_ref)
        ],
        "non_ratification_summary": "V70-C summary rows request later review only.",
    }
    payload["summary_register_id"] = _surface_id(
        "repo_candidate_review_classification_summary",
        REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA,
        payload,
        "summary_register_id",
    )
    return RepoCandidateReviewClassificationSummary.model_validate(payload)


def derive_v70c_repo_candidate_pre_ratification_handoff(
    *,
    repo_root: Path,
) -> RepoCandidatePreRatificationHandoff:
    summary = derive_v70c_repo_candidate_review_classification_summary(repo_root=repo_root)
    rows = [
        RepoCandidatePreRatificationHandoffRow(
            handoff_ref="handoff:v70c:odeu-diff:blocking-review",
            summary_ref="summary:v70c:odeu-diff:blocking-review",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            handoff_target="v71_ratification_review",
            handoff_posture="blocked_by_conflict",
            classification_refs=["classification:v70a:odeu-diff:requires-adversarial-review"],
            adversarial_review_refs=["review-row:v70b:odeu-diff:negative-control"],
            unresolved_gap_refs=["gap:v70b:odeu-diff:missing-counterevidence"],
            blocking_conflict_refs=["relation:v70b:odeu-diff:model-output-divergence"],
            required_resolution_surface="v71_ratification_review",
            non_authority_guardrail="Request later review only; not a decision.",
        ),
        RepoCandidatePreRatificationHandoffRow(
            handoff_ref="handoff:v70c:product-wedge:future-family",
            summary_ref="summary:v70c:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            handoff_target="future_family_review",
            handoff_posture="deferred_to_future_family",
            classification_refs=["classification:v70a:product-wedge:authority-boundary"],
            adversarial_review_refs=["review-row:v70b:product-wedge:authority-boundary"],
            unresolved_gap_refs=[
                "gap:v70b:product-wedge:v74-boundary",
            ],
            blocking_conflict_refs=["relation:v70b:product-wedge:authority-boundary"],
            required_resolution_surface="future_family_review",
            non_authority_guardrail="Request future review only; not a decision.",
        ),
        RepoCandidatePreRatificationHandoffRow(
            handoff_ref="handoff:v70c:self-evidencing:ready-review",
            summary_ref="summary:v70c:self-evidencing:ready-review",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            handoff_target="v71_ratification_review",
            handoff_posture="ready_for_v71_review",
            classification_refs=["classification:v70a:self-evidencing:source-bound"],
            adversarial_review_refs=["review-row:v70b:self-evidencing:supporting"],
            unresolved_gap_refs=[],
            blocking_conflict_refs=[],
            required_resolution_surface="v71_ratification_review",
            non_authority_guardrail="Request later review only; not a decision.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA,
        "review_id": summary.review_id,
        "snapshot_id": summary.snapshot_id,
        "source_set_id": summary.source_set_id,
        "summary_register_id": summary.summary_register_id,
        "handoff_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.handoff_ref)
        ],
        "non_ratification_summary": "V70-C handoff rows request later review only.",
    }
    payload["handoff_register_id"] = _surface_id(
        "repo_candidate_pre_ratification_handoff",
        REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA,
        payload,
        "handoff_register_id",
    )
    return RepoCandidatePreRatificationHandoff.model_validate(payload)


def derive_v70c_repo_candidate_review_summary_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoCandidateEvidenceSourceIndex,
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateAdversarialReviewMatrix,
    RepoCandidateReviewConflictRegister,
    RepoCandidateReviewGapScan,
    RepoCandidateReviewClassificationSummary,
    RepoCandidatePreRatificationHandoff,
]:
    source_index = RepoCandidateEvidenceSourceIndex.model_validate(
        _load_json(repo_root, _V70A_SOURCE_FIXTURE)
    )
    classification = RepoCandidateEvidenceClassificationRecord.model_validate(
        _load_json(repo_root, _V70A_CLASSIFICATION_FIXTURE)
    )
    matrix = RepoCandidateAdversarialReviewMatrix.model_validate(
        _load_json(repo_root, _V70B_MATRIX_FIXTURE)
    )
    conflict_register = RepoCandidateReviewConflictRegister.model_validate(
        _load_json(repo_root, _V70B_CONFLICT_FIXTURE)
    )
    gap_scan = RepoCandidateReviewGapScan.model_validate(_load_json(repo_root, _V70B_GAP_FIXTURE))
    summary = derive_v70c_repo_candidate_review_classification_summary(repo_root=repo_root)
    handoff = derive_v70c_repo_candidate_pre_ratification_handoff(repo_root=repo_root)
    validate_v70c_candidate_review_summary_bundle(
        source_index=source_index,
        classification_record=classification,
        adversarial_review_matrix=matrix,
        conflict_register=conflict_register,
        gap_scan=gap_scan,
        classification_summary=summary,
        pre_ratification_handoff=handoff,
    )
    return source_index, classification, matrix, conflict_register, gap_scan, summary, handoff
