from __future__ import annotations

import re
from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA = "repo_arc_series_cartography@1"
REPO_ARC_NAMESPACE_MAP_SCHEMA = "repo_arc_namespace_map@1"
REPO_FAMILY_CLOSURE_REGISTER_SCHEMA = "repo_family_closure_register@1"
REPO_BRANCH_POSTURE_REGISTER_SCHEMA = "repo_branch_posture_register@1"
REPO_SUPPORT_LINEAGE_REGISTER_SCHEMA = "repo_support_lineage_register@1"
REPO_EVIDENCE_SURFACE_INDEX_SCHEMA = "repo_evidence_surface_index@1"
REPO_ARC_MAPPING_TOOL_APPLICABILITY_REPORT_SCHEMA = "repo_arc_mapping_tool_applicability_report@1"
REPO_RECURSIVE_COORDINATE_EMISSION_PLAN_SCHEMA = "repo_recursive_coordinate_emission_plan@1"

AuthorityLayer = Literal["lock", "architecture", "planning", "support", "schema", "fixture"]
SourceKind = Literal[
    "planning_doc",
    "lock_doc",
    "decision_doc",
    "assessment_doc",
    "architecture_doc",
    "support_doc",
    "review_input",
    "schema_file",
    "fixture_file",
    "evidence_artifact",
    "generated_view",
]
SourceStatus = Literal[
    "integrated_shaping_source",
    "available_but_not_integrated",
    "review_pending_input",
    "rejected_or_superseded_source",
]
SourcePresencePosture = Literal[
    "present",
    "missing_expected_support_artifact",
    "not_uploaded_in_review_snapshot",
    "generated_later",
    "external_unavailable",
]
NamespaceKind = Literal[
    "selector_version",
    "family_id",
    "family_slice_id",
    "implementation_arc_id",
    "closeout_arc_id",
    "evidence_arc_id",
    "branch_local_execution_target",
    "planning_doc_ref",
    "lock_doc_ref",
    "decision_doc_ref",
    "assessment_doc_ref",
    "architecture_doc_ref",
    "support_doc_ref",
    "schema_id",
    "fixture_dir_ref",
    "evidence_input_ref",
    "stop_gate_ref",
]
EquivalencePosture = Literal[
    "self_identity_only",
    "related_not_equivalent",
    "unknown_needs_review",
]
ClosurePosture = Literal[
    "closed_on_main",
    "open_in_progress",
    "planned_not_started",
    "deferred_to_later_family",
    "superseded_by_alternate_surface",
    "not_selected_yet",
    "unknown_needs_review",
]
BranchPosture = Literal[
    "connected_conditional_branch",
    "deferred_branch",
    "selected_branch",
    "superseded_branch",
    "not_selected_branch",
    "review_required_branch",
]
EvidenceKind = Literal[
    "planning_selection",
    "lock_contract",
    "stop_gate_decision",
    "edge_assessment",
    "support_mapping",
    "review_capture",
    "schema_export",
    "fixture",
    "tool_run",
    "closeout_artifact",
]
ClaimHorizon = Literal[
    "descriptive_support",
    "planning_candidate",
    "architecture_decomposition",
    "lock_authorized",
    "closeout_evidence",
    "released_schema_or_runtime",
    "future_deferred",
    "review_pending",
]
ToolApplicabilityPosture = Literal[
    "applicable_and_supporting",
    "applicable_with_warnings",
    "namespace_limited",
    "not_applicable_to_claim",
    "failed_or_inconclusive",
    "not_run",
]
CoordinatePosture = Literal[
    "coordinate_emitted",
    "coordinate_absent_deliberate",
    "coordinate_absent_tool_not_applicable",
    "coordinate_absent_missing_source",
    "coordinate_absent_review_required",
]

_ABSOLUTE_PATH_RE = re.compile(r"^(?:/|[A-Za-z]:[\\/])")
_GLOB_TOKEN_RE = re.compile(r"[*?\[]")
_FORBIDDEN_AUTHORITY_VERB_RE = re.compile(
    r"\b(authorizes?|adopts?|admits?|ratifies?|implements?|releases?|dispatches?|commits?|merges?)\b",
    re.IGNORECASE,
)


def _non_empty(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _repo_ref(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    if _ABSOLUTE_PATH_RE.search(normalized):
        raise ValueError(f"{field_name} must be repo-relative, not absolute")
    if _GLOB_TOKEN_RE.search(normalized):
        raise ValueError(f"{field_name} must be a concrete source ref, not a glob")
    return normalized


def _sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_non_empty(value, field_name=field_name) for value in values]
    if len(set(normalized)) != len(normalized):
        raise ValueError(f"{field_name} values must be unique")
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted lexicographically")
    return normalized


def _sorted_unique_by_ref[T](rows: list[T], *, attr: str, field_name: str) -> list[T]:
    refs = [getattr(row, attr) for row in rows]
    if len(set(refs)) != len(refs):
        raise ValueError(f"{field_name} {attr} values must be unique")
    if refs != sorted(refs):
        raise ValueError(f"{field_name} must be sorted lexicographically by {attr}")
    return rows


def _reject_authority_laundering(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    if _FORBIDDEN_AUTHORITY_VERB_RE.search(normalized):
        raise ValueError(
            f"{field_name} may not carry candidate, implementation, or release authority"
        )
    return normalized


class _CartographyBase(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())


class RepoArcCartographySourceRow(_CartographyBase):
    source_ref: str
    source_kind: SourceKind
    authority_layer: AuthorityLayer
    source_status: SourceStatus
    source_presence_posture: SourcePresencePosture
    integration_note: str

    @model_validator(mode="after")
    def _validate_source(self) -> RepoArcCartographySourceRow:
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self,
            "integration_note",
            _non_empty(self.integration_note, field_name="integration_note"),
        )
        if (
            self.source_status == "integrated_shaping_source"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("integrated source rows must have source_presence_posture = present")
        if self.source_kind in {"support_doc", "review_input"} and self.authority_layer == "lock":
            raise ValueError("support and review sources cannot be marked as lock authority")
        if self.source_ref.startswith("docs/support/") and self.authority_layer == "lock":
            raise ValueError("support-layer source cannot be marked as lock authority")
        return self


class RepoArcNamespaceRow(_CartographyBase):
    namespace_ref: str
    namespace_kind: NamespaceKind
    canonical_label: str
    source_refs: list[str] = Field(min_length=1)
    equivalence_posture: EquivalencePosture

    @model_validator(mode="after")
    def _validate_namespace(self) -> RepoArcNamespaceRow:
        object.__setattr__(
            self,
            "namespace_ref",
            _non_empty(self.namespace_ref, field_name="namespace_ref"),
        )
        object.__setattr__(
            self,
            "canonical_label",
            _non_empty(self.canonical_label, field_name="canonical_label"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        if self.namespace_kind == "family_id" and self.canonical_label.startswith("vNext+"):
            raise ValueError("vNext+ implementation or closeout labels cannot be family_id rows")
        if self.namespace_kind in {"implementation_arc_id", "closeout_arc_id"} and re.fullmatch(
            r"V\d+(?:-[A-Z])?", self.canonical_label
        ):
            raise ValueError("V-family labels cannot be implementation or closeout arc rows")
        return self


class RepoFamilyClosureRow(_CartographyBase):
    family_ref: str
    family_id: str
    family_slice_id: str | None = None
    closure_posture: ClosurePosture
    selected_by_refs: list[str] = Field(default_factory=list)
    closeout_evidence_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_family(self) -> RepoFamilyClosureRow:
        object.__setattr__(self, "family_ref", _non_empty(self.family_ref, field_name="family_ref"))
        object.__setattr__(self, "family_id", _non_empty(self.family_id, field_name="family_id"))
        if self.family_slice_id is not None:
            object.__setattr__(
                self,
                "family_slice_id",
                _non_empty(self.family_slice_id, field_name="family_slice_id"),
            )
        object.__setattr__(
            self,
            "selected_by_refs",
            _sorted_unique(self.selected_by_refs, field_name="selected_by_refs"),
        )
        object.__setattr__(
            self,
            "closeout_evidence_refs",
            _sorted_unique(self.closeout_evidence_refs, field_name="closeout_evidence_refs"),
        )
        if self.closure_posture == "closed_on_main" and not self.closeout_evidence_refs:
            raise ValueError("closed_on_main family rows require closeout_evidence_refs")
        return self


class RepoBranchPostureRow(_CartographyBase):
    branch_ref: str
    branch_family_id: str
    branch_posture: BranchPosture
    selection_condition: str
    source_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_branch(self) -> RepoBranchPostureRow:
        object.__setattr__(self, "branch_ref", _non_empty(self.branch_ref, field_name="branch_ref"))
        object.__setattr__(
            self,
            "branch_family_id",
            _non_empty(self.branch_family_id, field_name="branch_family_id"),
        )
        object.__setattr__(
            self,
            "selection_condition",
            _non_empty(self.selection_condition, field_name="selection_condition"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        return self


class RepoSupportLineageRow(_CartographyBase):
    support_ref: str
    source_ref: str
    source_status: SourceStatus
    authority_layer: AuthorityLayer
    lineage_note: str

    @model_validator(mode="after")
    def _validate_support(self) -> RepoSupportLineageRow:
        object.__setattr__(
            self, "support_ref", _non_empty(self.support_ref, field_name="support_ref")
        )
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self,
            "lineage_note",
            _non_empty(self.lineage_note, field_name="lineage_note"),
        )
        if self.authority_layer == "lock":
            raise ValueError("support lineage rows cannot be lock authority")
        return self


class RepoEvidenceSurfaceRow(_CartographyBase):
    evidence_ref: str
    evidence_kind: EvidenceKind
    claim_horizon: ClaimHorizon
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_evidence(self) -> RepoEvidenceSurfaceRow:
        object.__setattr__(
            self,
            "evidence_ref",
            _non_empty(self.evidence_ref, field_name="evidence_ref"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_empty(self.limitation_note, field_name="limitation_note"),
        )
        return self


class RepoToolApplicabilityRow(_CartographyBase):
    tool_id: str
    target_claim_id: str
    target_namespace_kind: NamespaceKind
    applicability_posture: ToolApplicabilityPosture
    observed_result_ref: str | None = None
    limitation_note: str

    @model_validator(mode="after")
    def _validate_tool(self) -> RepoToolApplicabilityRow:
        object.__setattr__(self, "tool_id", _non_empty(self.tool_id, field_name="tool_id"))
        object.__setattr__(
            self,
            "target_claim_id",
            _non_empty(self.target_claim_id, field_name="target_claim_id"),
        )
        if self.observed_result_ref is not None:
            object.__setattr__(
                self,
                "observed_result_ref",
                _non_empty(self.observed_result_ref, field_name="observed_result_ref"),
            )
        object.__setattr__(
            self,
            "limitation_note",
            _non_empty(self.limitation_note, field_name="limitation_note"),
        )
        if (
            self.applicability_posture
            in {
                "applicable_and_supporting",
                "applicable_with_warnings",
                "namespace_limited",
                "failed_or_inconclusive",
            }
            and self.observed_result_ref is None
        ):
            raise ValueError("run-bearing tool applicability rows require observed_result_ref")
        if self.applicability_posture == "not_run" and self.observed_result_ref is not None:
            raise ValueError("not_run tool applicability rows cannot carry observed_result_ref")
        return self


class RepoRecursiveCoordinatePlanRow(_CartographyBase):
    coordinate_ref: str
    coordinate_posture: CoordinatePosture
    target_refs: list[str] = Field(default_factory=list)
    non_authority_guardrail: str

    @model_validator(mode="after")
    def _validate_coordinate(self) -> RepoRecursiveCoordinatePlanRow:
        object.__setattr__(
            self,
            "coordinate_ref",
            _non_empty(self.coordinate_ref, field_name="coordinate_ref"),
        )
        object.__setattr__(
            self,
            "target_refs",
            _sorted_unique(self.target_refs, field_name="target_refs"),
        )
        object.__setattr__(
            self,
            "non_authority_guardrail",
            _reject_authority_laundering(
                self.non_authority_guardrail, field_name="non_authority_guardrail"
            ),
        )
        return self


def _source_ref_set(source_rows: list[RepoArcCartographySourceRow]) -> set[str]:
    return {row.source_ref for row in source_rows}


def _require_source_refs(
    refs: list[str],
    *,
    known_source_refs: set[str],
    field_name: str,
) -> None:
    missing = sorted(set(refs) - known_source_refs)
    if missing:
        raise ValueError(f"{field_name} must reference known source rows: {missing}")


def _namespace_kind_by_ref(rows: list[RepoArcNamespaceRow]) -> dict[str, NamespaceKind]:
    return {row.namespace_ref: row.namespace_kind for row in rows}


def _canonical_label_kind_pairs(
    rows: list[RepoArcNamespaceRow],
) -> dict[str, set[NamespaceKind]]:
    labels: dict[str, set[NamespaceKind]] = {}
    for row in rows:
        labels.setdefault(row.canonical_label, set()).add(row.namespace_kind)
    return labels


def _validate_namespace_rows(rows: list[RepoArcNamespaceRow]) -> None:
    for label, kinds in _canonical_label_kind_pairs(rows).items():
        if len(kinds) > 1:
            raise ValueError(
                f"namespace canonical_label {label!r} may not collapse distinct kinds: "
                f"{sorted(kinds)}"
            )


def _validate_cartography_bundle(
    *,
    source_rows: list[RepoArcCartographySourceRow],
    namespace_rows: list[RepoArcNamespaceRow],
    family_rows: list[RepoFamilyClosureRow],
    branch_rows: list[RepoBranchPostureRow],
    support_lineage_rows: list[RepoSupportLineageRow],
    evidence_surface_rows: list[RepoEvidenceSurfaceRow],
    tool_applicability_rows: list[RepoToolApplicabilityRow],
    coordinate_plan_rows: list[RepoRecursiveCoordinatePlanRow],
    tracked_future_seams: list[str] | None = None,
) -> None:
    known_sources = _source_ref_set(source_rows)
    namespace_kind_by_ref = _namespace_kind_by_ref(namespace_rows)
    evidence_refs = {row.evidence_ref for row in evidence_surface_rows}
    coordinate_targets = (
        set(namespace_kind_by_ref)
        | {row.family_ref for row in family_rows}
        | {row.branch_ref for row in branch_rows}
        | evidence_refs
        | {row.tool_id for row in tool_applicability_rows}
    )

    for row in namespace_rows:
        _require_source_refs(
            row.source_refs, known_source_refs=known_sources, field_name="namespace source_refs"
        )
    _validate_namespace_rows(namespace_rows)

    for row in family_rows:
        if namespace_kind_by_ref.get(row.family_id) != "family_id":
            raise ValueError("family rows must reference a family_id namespace row")
        if (
            row.family_slice_id is not None
            and namespace_kind_by_ref.get(row.family_slice_id) != "family_slice_id"
        ):
            raise ValueError("family_slice_id must reference a family_slice_id namespace row")
        _require_source_refs(
            row.selected_by_refs,
            known_source_refs=known_sources,
            field_name="family selected_by_refs",
        )
        missing_evidence = sorted(set(row.closeout_evidence_refs) - evidence_refs)
        if missing_evidence:
            raise ValueError(
                f"family closeout_evidence_refs must reference evidence rows: {missing_evidence}"
            )

    family_labels_by_ref = {
        row.namespace_ref: row.canonical_label
        for row in namespace_rows
        if row.namespace_kind == "family_id"
    }
    branch_labels = {
        family_labels_by_ref.get(row.branch_family_id, row.branch_family_id): row
        for row in branch_rows
    }
    for row in branch_rows:
        if namespace_kind_by_ref.get(row.branch_family_id) != "family_id":
            raise ValueError("branch_family_id must reference a family_id namespace row")
        _require_source_refs(
            row.source_refs, known_source_refs=known_sources, field_name="branch source_refs"
        )

    for row in support_lineage_rows:
        if row.source_ref not in known_sources:
            raise ValueError("support lineage source_ref must reference a source row")
        source_row = next(source for source in source_rows if source.source_ref == row.source_ref)
        if row.source_status != source_row.source_status:
            raise ValueError("support lineage source_status must match the source row")

    for row in evidence_surface_rows:
        _require_source_refs(
            row.source_refs, known_source_refs=known_sources, field_name="evidence source_refs"
        )

    for row in tool_applicability_rows:
        if row.observed_result_ref is not None and row.observed_result_ref not in evidence_refs:
            raise ValueError("tool observed_result_ref must reference an evidence row")
        if (
            row.applicability_posture == "applicable_and_supporting"
            and "global" in row.limitation_note.lower()
        ):
            raise ValueError("tool applicability cannot claim global scope in limitation_note")

    for row in coordinate_plan_rows:
        missing_targets = sorted(set(row.target_refs) - coordinate_targets)
        if missing_targets:
            raise ValueError(
                f"coordinate target_refs must reference known cartography rows: {missing_targets}"
            )

    if tracked_future_seams and any(
        "external_contest_participation" in seam for seam in tracked_future_seams
    ):
        v43_branch = branch_labels.get("V43")
        if v43_branch is None or v43_branch.branch_posture != "connected_conditional_branch":
            raise ValueError(
                "external contest future seams require V43 connected conditional branch posture"
            )


class RepoArcSeriesCartography(_CartographyBase):
    schema: Literal["repo_arc_series_cartography@1"] = REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA
    cartography_id: str
    snapshot_id: str
    coverage_horizon: str
    cartography_scope: str
    tracked_future_seams: list[str] = Field(default_factory=list)
    source_rows: list[RepoArcCartographySourceRow] = Field(min_length=1)
    namespace_rows: list[RepoArcNamespaceRow] = Field(min_length=1)
    family_rows: list[RepoFamilyClosureRow] = Field(min_length=1)
    branch_rows: list[RepoBranchPostureRow] = Field(default_factory=list)
    support_lineage_rows: list[RepoSupportLineageRow] = Field(default_factory=list)
    evidence_surface_rows: list[RepoEvidenceSurfaceRow] = Field(min_length=1)
    tool_applicability_rows: list[RepoToolApplicabilityRow] = Field(default_factory=list)
    coordinate_plan_rows: list[RepoRecursiveCoordinatePlanRow] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_cartography(self) -> RepoArcSeriesCartography:
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "coverage_horizon",
            _non_empty(self.coverage_horizon, field_name="coverage_horizon"),
        )
        object.__setattr__(
            self,
            "cartography_scope",
            _reject_authority_laundering(self.cartography_scope, field_name="cartography_scope"),
        )
        object.__setattr__(
            self,
            "tracked_future_seams",
            _sorted_unique(self.tracked_future_seams, field_name="tracked_future_seams"),
        )
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        object.__setattr__(
            self,
            "namespace_rows",
            _sorted_unique_by_ref(
                self.namespace_rows, attr="namespace_ref", field_name="namespace_rows"
            ),
        )
        object.__setattr__(
            self,
            "family_rows",
            _sorted_unique_by_ref(self.family_rows, attr="family_ref", field_name="family_rows"),
        )
        object.__setattr__(
            self,
            "branch_rows",
            _sorted_unique_by_ref(self.branch_rows, attr="branch_ref", field_name="branch_rows"),
        )
        object.__setattr__(
            self,
            "support_lineage_rows",
            _sorted_unique_by_ref(
                self.support_lineage_rows, attr="support_ref", field_name="support_lineage_rows"
            ),
        )
        object.__setattr__(
            self,
            "evidence_surface_rows",
            _sorted_unique_by_ref(
                self.evidence_surface_rows, attr="evidence_ref", field_name="evidence_surface_rows"
            ),
        )
        object.__setattr__(
            self,
            "tool_applicability_rows",
            _sorted_unique_by_ref(
                self.tool_applicability_rows, attr="tool_id", field_name="tool_applicability_rows"
            ),
        )
        object.__setattr__(
            self,
            "coordinate_plan_rows",
            _sorted_unique_by_ref(
                self.coordinate_plan_rows, attr="coordinate_ref", field_name="coordinate_plan_rows"
            ),
        )
        _validate_cartography_bundle(
            source_rows=self.source_rows,
            namespace_rows=self.namespace_rows,
            family_rows=self.family_rows,
            branch_rows=self.branch_rows,
            support_lineage_rows=self.support_lineage_rows,
            evidence_surface_rows=self.evidence_surface_rows,
            tool_applicability_rows=self.tool_applicability_rows,
            coordinate_plan_rows=self.coordinate_plan_rows,
            tracked_future_seams=self.tracked_future_seams,
        )
        expected_id = compute_repo_arc_series_cartography_id(self.model_dump(mode="json"))
        if self.cartography_id != expected_id:
            raise ValueError("cartography_id must match canonical full payload hash identity")
        return self


class RepoArcNamespaceMap(_CartographyBase):
    schema: Literal["repo_arc_namespace_map@1"] = REPO_ARC_NAMESPACE_MAP_SCHEMA
    namespace_map_id: str
    cartography_id: str
    snapshot_id: str
    coverage_horizon: str
    source_rows: list[RepoArcCartographySourceRow] = Field(min_length=1)
    namespace_rows: list[RepoArcNamespaceRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_map(self) -> RepoArcNamespaceMap:
        object.__setattr__(
            self,
            "namespace_map_id",
            _non_empty(self.namespace_map_id, field_name="namespace_map_id"),
        )
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "coverage_horizon",
            _non_empty(self.coverage_horizon, field_name="coverage_horizon"),
        )
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        object.__setattr__(
            self,
            "namespace_rows",
            _sorted_unique_by_ref(
                self.namespace_rows, attr="namespace_ref", field_name="namespace_rows"
            ),
        )
        known_sources = _source_ref_set(self.source_rows)
        for row in self.namespace_rows:
            _require_source_refs(
                row.source_refs, known_source_refs=known_sources, field_name="namespace source_refs"
            )
        _validate_namespace_rows(self.namespace_rows)
        return self


class RepoFamilyClosureRegister(_CartographyBase):
    schema: Literal["repo_family_closure_register@1"] = REPO_FAMILY_CLOSURE_REGISTER_SCHEMA
    closure_register_id: str
    cartography_id: str
    snapshot_id: str
    family_rows: list[RepoFamilyClosureRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_register(self) -> RepoFamilyClosureRegister:
        object.__setattr__(
            self,
            "closure_register_id",
            _non_empty(self.closure_register_id, field_name="closure_register_id"),
        )
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "family_rows",
            _sorted_unique_by_ref(self.family_rows, attr="family_ref", field_name="family_rows"),
        )
        return self


class RepoBranchPostureRegister(_CartographyBase):
    schema: Literal["repo_branch_posture_register@1"] = REPO_BRANCH_POSTURE_REGISTER_SCHEMA
    branch_posture_register_id: str
    cartography_id: str
    snapshot_id: str
    branch_rows: list[RepoBranchPostureRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_register(self) -> RepoBranchPostureRegister:
        object.__setattr__(
            self,
            "branch_posture_register_id",
            _non_empty(self.branch_posture_register_id, field_name="branch_posture_register_id"),
        )
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "branch_rows",
            _sorted_unique_by_ref(self.branch_rows, attr="branch_ref", field_name="branch_rows"),
        )
        return self


class RepoSupportLineageRegister(_CartographyBase):
    schema: Literal["repo_support_lineage_register@1"] = REPO_SUPPORT_LINEAGE_REGISTER_SCHEMA
    support_lineage_register_id: str
    cartography_id: str
    snapshot_id: str
    support_lineage_rows: list[RepoSupportLineageRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_register(self) -> RepoSupportLineageRegister:
        object.__setattr__(
            self,
            "support_lineage_register_id",
            _non_empty(self.support_lineage_register_id, field_name="support_lineage_register_id"),
        )
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "support_lineage_rows",
            _sorted_unique_by_ref(
                self.support_lineage_rows, attr="support_ref", field_name="support_lineage_rows"
            ),
        )
        return self


class RepoEvidenceSurfaceIndex(_CartographyBase):
    schema: Literal["repo_evidence_surface_index@1"] = REPO_EVIDENCE_SURFACE_INDEX_SCHEMA
    evidence_surface_index_id: str
    cartography_id: str
    snapshot_id: str
    evidence_surface_rows: list[RepoEvidenceSurfaceRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_index(self) -> RepoEvidenceSurfaceIndex:
        object.__setattr__(
            self,
            "evidence_surface_index_id",
            _non_empty(self.evidence_surface_index_id, field_name="evidence_surface_index_id"),
        )
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "evidence_surface_rows",
            _sorted_unique_by_ref(
                self.evidence_surface_rows, attr="evidence_ref", field_name="evidence_surface_rows"
            ),
        )
        return self


class RepoArcMappingToolApplicabilityReport(_CartographyBase):
    schema: Literal["repo_arc_mapping_tool_applicability_report@1"] = (
        REPO_ARC_MAPPING_TOOL_APPLICABILITY_REPORT_SCHEMA
    )
    tool_applicability_report_id: str
    cartography_id: str
    snapshot_id: str
    tool_applicability_rows: list[RepoToolApplicabilityRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_report(self) -> RepoArcMappingToolApplicabilityReport:
        object.__setattr__(
            self,
            "tool_applicability_report_id",
            _non_empty(
                self.tool_applicability_report_id, field_name="tool_applicability_report_id"
            ),
        )
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "tool_applicability_rows",
            _sorted_unique_by_ref(
                self.tool_applicability_rows, attr="tool_id", field_name="tool_applicability_rows"
            ),
        )
        return self


class RepoRecursiveCoordinateEmissionPlan(_CartographyBase):
    schema: Literal["repo_recursive_coordinate_emission_plan@1"] = (
        REPO_RECURSIVE_COORDINATE_EMISSION_PLAN_SCHEMA
    )
    coordinate_emission_plan_id: str
    cartography_id: str
    snapshot_id: str
    coordinate_plan_rows: list[RepoRecursiveCoordinatePlanRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_plan(self) -> RepoRecursiveCoordinateEmissionPlan:
        object.__setattr__(
            self,
            "coordinate_emission_plan_id",
            _non_empty(self.coordinate_emission_plan_id, field_name="coordinate_emission_plan_id"),
        )
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "coordinate_plan_rows",
            _sorted_unique_by_ref(
                self.coordinate_plan_rows, attr="coordinate_ref", field_name="coordinate_plan_rows"
            ),
        )
        return self


def compute_repo_arc_series_cartography_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA)
    canonical_payload.pop("cartography_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_arc_series_cartography_{digest[:24]}"


def materialize_repo_arc_series_cartography_payload(
    payload_without_cartography_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_cartography_id)
    payload.setdefault("schema", REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA)
    payload["cartography_id"] = compute_repo_arc_series_cartography_id(payload)
    return RepoArcSeriesCartography.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_arc_series_cartography_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoArcSeriesCartography.model_validate(payload).model_dump(mode="json")
