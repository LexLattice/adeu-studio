from __future__ import annotations

import re
from pathlib import Path
from typing import Literal

from pydantic import Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .arc_series_cartography import (
    _ABSOLUTE_PATH_RE,
    _GLOB_TOKEN_RE,
    ClaimHorizon,
    CoordinatePosture,
    NamespaceKind,
    SourceKind,
    _CartographyBase,
    _non_empty,
    _reject_authority_laundering,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)

REPO_ARC_CARTOGRAPHY_DERIVATION_MANIFEST_SCHEMA = (
    "repo_arc_cartography_derivation_manifest@1"
)
REPO_ARC_CARTOGRAPHY_GAP_SCAN_REPORT_SCHEMA = "repo_arc_cartography_gap_scan_report@1"

DerivationPosture = Literal[
    "derived",
    "manual_seeded",
    "review_required",
    "not_observed",
    "ambiguous",
]
DerivedRowKind = Literal[
    "source_row",
    "namespace_row",
    "family_row",
    "branch_row",
    "support_lineage_row",
    "evidence_surface_row",
    "tool_applicability_row",
    "coordinate_plan_row",
    "gap_row",
]
GapFamily = Literal[
    "namespace_kind_ambiguous",
    "family_closure_posture_missing",
    "slice_closure_posture_missing",
    "source_status_missing",
    "support_lineage_missing",
    "evidence_surface_unindexed",
    "branch_posture_missing",
    "tool_applicability_unassessed",
    "coordinate_posture_absent",
    "expected_support_artifact_missing",
    "source_ref_missing",
    "source_ref_stale",
    "authority_layer_mismatch",
    "review_required_ambiguous_derivation",
]
GapSeverity = Literal["blocking_for_cartography", "needs_review", "advisory"]

_CLOSEOUT_EVIDENCE_PREFIXES = (
    "artifacts/agent_harness/",
    "artifacts/stop_gate/",
    "docs/ASSESSMENT_vNEXT_PLUS",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS",
)
_FUTURE_LIFECYCLE_RE = r"(^|[:/])V(?:69|70|71|72|73|74|75)(?:$|[^0-9])"
_GLOBAL_ARC_RE = re.compile(r"\bv(?:NEXT_PLUS|NEXT\+|\+)[0-9]+\b", re.IGNORECASE)


def _repo_pattern(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    if _ABSOLUTE_PATH_RE.search(normalized):
        raise ValueError(f"{field_name} must be repo-relative, not absolute")
    parts = normalized.split("/")
    if any(part == ".." for part in parts):
        raise ValueError(f"{field_name} must not traverse outside the repo")
    return normalized


def _source_refs_are_support_only(source_refs: list[str]) -> bool:
    return bool(source_refs) and all(ref.startswith("docs/support/") for ref in source_refs)


def _has_closeout_evidence(source_refs: list[str]) -> bool:
    return any(ref.startswith(_CLOSEOUT_EVIDENCE_PREFIXES) for ref in source_refs)


def _is_future_lifecycle_ref(value: str) -> bool:
    return re.search(_FUTURE_LIFECYCLE_RE, value) is not None


def _collapses_global_arc_into_family(*, target_ref: str, namespace_kind: NamespaceKind) -> bool:
    return namespace_kind in {"family_id", "family_slice_id"} and (
        _GLOBAL_ARC_RE.search(target_ref) is not None
    )


class RepoArcCartographyObservedInputRow(_CartographyBase):
    source_ref: str
    source_kind: SourceKind
    observed_for_patterns: list[str] = Field(min_length=1)
    content_presence: Literal["present", "missing_expected", "stale_reference"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_observed_input(self) -> RepoArcCartographyObservedInputRow:
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self,
            "observed_for_patterns",
            _sorted_unique(self.observed_for_patterns, field_name="observed_for_patterns"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_empty(self.limitation_note, field_name="limitation_note"),
        )
        for pattern in self.observed_for_patterns:
            _repo_pattern(pattern, field_name="observed_for_patterns")
        if self.content_presence == "present" and _GLOB_TOKEN_RE.search(self.source_ref):
            raise ValueError("observed input source_ref must be a concrete file, not a glob")
        return self


class RepoArcCartographyDerivedRowRecord(_CartographyBase):
    derived_ref: str
    derived_row_kind: DerivedRowKind
    target_ref: str
    target_namespace_kind: NamespaceKind
    derivation_posture: DerivationPosture
    claim_horizon: ClaimHorizon
    source_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_derived_row(self) -> RepoArcCartographyDerivedRowRecord:
        object.__setattr__(
            self,
            "derived_ref",
            _non_empty(self.derived_ref, field_name="derived_ref"),
        )
        object.__setattr__(
            self,
            "target_ref",
            _non_empty(self.target_ref, field_name="target_ref"),
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
        for ref in self.source_refs:
            _repo_ref(ref, field_name="derived source_refs")
        if self.derivation_posture == "derived" and not self.source_refs:
            raise ValueError("derived rows require at least one concrete source_ref")
        if self.derivation_posture in {"ambiguous", "review_required"} and self.claim_horizon in {
            "lock_authorized",
            "closeout_evidence",
            "released_schema_or_runtime",
        }:
            raise ValueError("ambiguous or review-required rows cannot carry settled claim horizon")
        if self.claim_horizon == "lock_authorized" and _source_refs_are_support_only(
            self.source_refs
        ):
            raise ValueError("support review text cannot be treated as lock evidence")
        if self.claim_horizon == "lock_authorized" and _is_future_lifecycle_ref(self.target_ref):
            raise ValueError("V69 through V75 cannot be derived as authorized locks by V68-B")
        if _collapses_global_arc_into_family(
            target_ref=self.target_ref,
            namespace_kind=self.target_namespace_kind,
        ):
            raise ValueError("global implementation arc refs cannot be treated as family ids")
        if (
            self.derived_row_kind == "family_row"
            and self.claim_horizon == "closeout_evidence"
            and not _has_closeout_evidence(self.source_refs)
        ):
            raise ValueError("closure derivation requires closeout decision or artifact evidence")
        return self


class RepoArcCartographyDerivationManifest(_CartographyBase):
    schema: Literal["repo_arc_cartography_derivation_manifest@1"] = (
        REPO_ARC_CARTOGRAPHY_DERIVATION_MANIFEST_SCHEMA
    )
    derivation_manifest_id: str
    cartography_id: str
    snapshot_id: str
    coverage_horizon: str
    scanned_source_patterns: list[str] = Field(min_length=1)
    observed_input_rows: list[RepoArcCartographyObservedInputRow] = Field(min_length=1)
    derived_row_records: list[RepoArcCartographyDerivedRowRecord] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_manifest(self) -> RepoArcCartographyDerivationManifest:
        object.__setattr__(
            self,
            "derivation_manifest_id",
            _non_empty(self.derivation_manifest_id, field_name="derivation_manifest_id"),
        )
        object.__setattr__(
            self,
            "cartography_id",
            _non_empty(self.cartography_id, field_name="cartography_id"),
        )
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "coverage_horizon",
            _non_empty(self.coverage_horizon, field_name="coverage_horizon"),
        )
        object.__setattr__(
            self,
            "scanned_source_patterns",
            _sorted_unique(self.scanned_source_patterns, field_name="scanned_source_patterns"),
        )
        object.__setattr__(
            self,
            "observed_input_rows",
            _sorted_unique_by_ref(
                self.observed_input_rows, attr="source_ref", field_name="observed_input_rows"
            ),
        )
        object.__setattr__(
            self,
            "derived_row_records",
            _sorted_unique_by_ref(
                self.derived_row_records, attr="derived_ref", field_name="derived_row_records"
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _reject_authority_laundering(self.limitation_note, field_name="limitation_note"),
        )
        for pattern in self.scanned_source_patterns:
            _repo_pattern(pattern, field_name="scanned_source_patterns")
        observed_refs = {row.source_ref for row in self.observed_input_rows}
        for row in self.derived_row_records:
            missing = sorted(set(row.source_refs) - observed_refs)
            if missing:
                raise ValueError(f"derived source_refs must reference observed inputs: {missing}")
        return self


class RepoArcCartographyGapRow(_CartographyBase):
    gap_id: str
    gap_family: GapFamily
    target_ref: str
    target_namespace_kind: NamespaceKind
    severity: GapSeverity
    claim_horizon: ClaimHorizon
    source_refs: list[str] = Field(default_factory=list)
    recommended_next_action: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_gap(self) -> RepoArcCartographyGapRow:
        object.__setattr__(self, "gap_id", _non_empty(self.gap_id, field_name="gap_id"))
        object.__setattr__(
            self,
            "target_ref",
            _non_empty(self.target_ref, field_name="target_ref"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "recommended_next_action",
            _reject_authority_laundering(
                self.recommended_next_action, field_name="recommended_next_action"
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_empty(self.limitation_note, field_name="limitation_note"),
        )
        for ref in self.source_refs:
            _repo_ref(ref, field_name="gap source_refs")
        if self.claim_horizon == "lock_authorized" and _source_refs_are_support_only(
            self.source_refs
        ):
            raise ValueError("support review text cannot be treated as lock evidence")
        if self.claim_horizon == "lock_authorized" and _is_future_lifecycle_ref(self.target_ref):
            raise ValueError("V69 through V75 cannot be gap-scanned as authorized locks by V68-B")
        if _collapses_global_arc_into_family(
            target_ref=self.target_ref,
            namespace_kind=self.target_namespace_kind,
        ):
            raise ValueError("global implementation arc refs cannot be treated as family ids")
        return self


class RepoArcCartographyGapScanReport(_CartographyBase):
    schema: Literal["repo_arc_cartography_gap_scan_report@1"] = (
        REPO_ARC_CARTOGRAPHY_GAP_SCAN_REPORT_SCHEMA
    )
    gap_scan_report_id: str
    derivation_manifest_id: str
    cartography_id: str
    snapshot_id: str
    coordinate_posture: CoordinatePosture
    expected_missing_support_refs: list[str] = Field(default_factory=list)
    gap_rows: list[RepoArcCartographyGapRow] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_gap_scan(self) -> RepoArcCartographyGapScanReport:
        object.__setattr__(
            self,
            "gap_scan_report_id",
            _non_empty(self.gap_scan_report_id, field_name="gap_scan_report_id"),
        )
        object.__setattr__(
            self,
            "derivation_manifest_id",
            _non_empty(self.derivation_manifest_id, field_name="derivation_manifest_id"),
        )
        object.__setattr__(
            self,
            "cartography_id",
            _non_empty(self.cartography_id, field_name="cartography_id"),
        )
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "expected_missing_support_refs",
            _sorted_unique(
                self.expected_missing_support_refs, field_name="expected_missing_support_refs"
            ),
        )
        object.__setattr__(
            self,
            "gap_rows",
            _sorted_unique_by_ref(self.gap_rows, attr="gap_id", field_name="gap_rows"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _reject_authority_laundering(self.limitation_note, field_name="limitation_note"),
        )
        for ref in self.expected_missing_support_refs:
            _repo_ref(ref, field_name="expected_missing_support_refs")
        missing_support_gap_targets = {
            row.target_ref
            for row in self.gap_rows
            if row.gap_family == "expected_support_artifact_missing"
        }
        missing_support_without_gap = sorted(
            set(self.expected_missing_support_refs) - missing_support_gap_targets
        )
        if missing_support_without_gap:
            raise ValueError(
                "expected missing support artifacts require expected_support_artifact_missing "
                f"gap rows: {missing_support_without_gap}"
            )
        if self.coordinate_posture != "coordinate_emitted" and not any(
            row.gap_family == "coordinate_posture_absent" for row in self.gap_rows
        ):
            raise ValueError("coordinate absence must be explicit in gap rows")
        return self


V68B_DEFAULT_SOURCE_PATTERNS: tuple[str, ...] = (
    "apps/api/fixtures/repo_description/vnext_plus188/repo_arc_series_cartography_v188_reference.json",
    "artifacts/agent_harness/v188/evidence_inputs/v68a_arc_series_cartography_evidence_v188.json",
    "docs/ARCHITECTURE_ADEU_ARC_SERIES_CARTOGRAPHY_FAMILY_v0.md",
    "docs/ASSESSMENT_vNEXT_PLUS188_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS189_EDGES.md",
    "docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v54.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS188.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS189.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS188.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS189.md",
    "packages/adeu_repo_description/schema/repo_arc_series_cartography.v1.json",
    "spec/repo_arc_series_cartography.schema.json",
)


def _source_kind_for_ref(source_ref: str) -> SourceKind:
    if source_ref.startswith("docs/DRAFT_NEXT_ARC_OPTIONS_"):
        return "planning_doc"
    if source_ref.startswith("docs/LOCKED_CONTINUATION_"):
        return "lock_doc"
    if source_ref.startswith("docs/DRAFT_STOP_GATE_DECISION_"):
        return "decision_doc"
    if source_ref.startswith("docs/ASSESSMENT_"):
        return "assessment_doc"
    if source_ref.startswith("docs/ARCHITECTURE_"):
        return "architecture_doc"
    if source_ref.startswith("docs/support/"):
        return "support_doc"
    if source_ref.startswith(("packages/", "spec/")) and source_ref.endswith(".json"):
        return "schema_file"
    if source_ref.startswith("apps/api/fixtures/"):
        return "fixture_file"
    if source_ref.startswith("artifacts/"):
        return "evidence_artifact"
    return "generated_view"


def _observe_source_patterns(
    *,
    root: Path,
    source_patterns: tuple[str, ...],
) -> list[RepoArcCartographyObservedInputRow]:
    rows: list[RepoArcCartographyObservedInputRow] = []
    seen: dict[str, set[str]] = {}
    for pattern in source_patterns:
        _repo_pattern(pattern, field_name="source_patterns")
        matches = sorted(path for path in root.glob(pattern) if path.is_file())
        for path in matches:
            source_ref = path.relative_to(root).as_posix()
            seen.setdefault(source_ref, set()).add(pattern)
    for source_ref in sorted(seen):
        rows.append(
            RepoArcCartographyObservedInputRow(
                source_ref=source_ref,
                source_kind=_source_kind_for_ref(source_ref),
                observed_for_patterns=sorted(seen[source_ref]),
                content_presence="present",
                limitation_note="Observed as a concrete V68-B derivation input.",
            )
        )
    return rows


def _manifest_id(payload_without_id: dict[str, object]) -> str:
    payload = dict(payload_without_id)
    payload.setdefault("schema", REPO_ARC_CARTOGRAPHY_DERIVATION_MANIFEST_SCHEMA)
    payload.pop("derivation_manifest_id", None)
    digest = sha256_canonical_json(payload)
    return f"repo_arc_cartography_derivation_manifest_{digest[:24]}"


def _gap_report_id(payload_without_id: dict[str, object]) -> str:
    payload = dict(payload_without_id)
    payload.setdefault("schema", REPO_ARC_CARTOGRAPHY_GAP_SCAN_REPORT_SCHEMA)
    payload.pop("gap_scan_report_id", None)
    digest = sha256_canonical_json(payload)
    return f"repo_arc_cartography_gap_scan_report_{digest[:24]}"


def derive_v68b_repo_arc_cartography_derivation_manifest(
    *,
    repo_root: Path,
    source_patterns: tuple[str, ...] = V68B_DEFAULT_SOURCE_PATTERNS,
) -> RepoArcCartographyDerivationManifest:
    observed_input_rows = _observe_source_patterns(root=repo_root, source_patterns=source_patterns)
    observed_refs = {row.source_ref for row in observed_input_rows}
    if not observed_input_rows:
        raise ValueError("V68-B derivation manifest requires at least one observed input")

    def refs(*items: str) -> list[str]:
        return sorted(item for item in items if item in observed_refs)

    derived_rows = [
        RepoArcCartographyDerivedRowRecord(
            derived_ref="derived:family:V68-B",
            derived_row_kind="family_row",
            target_ref="family:V68-B",
            target_namespace_kind="family_slice_id",
            derivation_posture="manual_seeded",
            claim_horizon="planning_candidate",
            source_refs=refs(
                "docs/DRAFT_NEXT_ARC_OPTIONS_v54.md",
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS189.md",
            ),
            limitation_note="V68-B is selected as a starter candidate but not yet closed.",
        ),
        RepoArcCartographyDerivedRowRecord(
            derived_ref="derived:closeout:V68-A",
            derived_row_kind="family_row",
            target_ref="family:V68-A",
            target_namespace_kind="family_slice_id",
            derivation_posture="derived",
            claim_horizon="closeout_evidence",
            source_refs=refs(
                "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS188.md",
                "docs/ASSESSMENT_vNEXT_PLUS188_EDGES.md",
                "artifacts/agent_harness/v188/evidence_inputs/v68a_arc_series_cartography_evidence_v188.json",
            ),
            limitation_note="V68-A closure is derived from post-closeout evidence on main.",
        ),
        RepoArcCartographyDerivedRowRecord(
            derived_ref="derived:coordinate_absence:V68-B",
            derived_row_kind="coordinate_plan_row",
            target_ref="coordinate:V68-B",
            target_namespace_kind="evidence_arc_id",
            derivation_posture="review_required",
            claim_horizon="review_pending",
            source_refs=refs("docs/ASSESSMENT_vNEXT_PLUS189_EDGES.md"),
            limitation_note="Coordinate emission remains absent until V68-C hardening.",
        ),
        RepoArcCartographyDerivedRowRecord(
            derived_ref="derived:branch:V43-connected-conditional",
            derived_row_kind="branch_row",
            target_ref="family:V43",
            target_namespace_kind="family_id",
            derivation_posture="derived",
            claim_horizon="closeout_evidence",
            source_refs=refs(
                "apps/api/fixtures/repo_description/vnext_plus188/repo_arc_series_cartography_v188_reference.json",
                "docs/ASSESSMENT_vNEXT_PLUS188_EDGES.md",
                "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS188.md",
            ),
            limitation_note=(
                "V43 remains represented as the connected conditional branch carried by V68-A."
            ),
        ),
    ]
    payload = {
        "schema": REPO_ARC_CARTOGRAPHY_DERIVATION_MANIFEST_SCHEMA,
        "cartography_id": "repo_arc_series_cartography_v68b_current_derivation_seed",
        "snapshot_id": "vNext+189-prestart-on-main",
        "coverage_horizon": (
            "V68-B starter derivation over V68-A closeout and v189 pre-start bundle only"
        ),
        "scanned_source_patterns": sorted(source_patterns),
        "observed_input_rows": [row.model_dump(mode="json") for row in observed_input_rows],
        "derived_row_records": [
            row.model_dump(mode="json")
            for row in sorted(derived_rows, key=lambda row: row.derived_ref)
        ],
        "limitation_note": (
            "Descriptive derivation support only; later action requires separate planning and lock."
        ),
    }
    payload["derivation_manifest_id"] = _manifest_id(payload)
    return RepoArcCartographyDerivationManifest.model_validate(payload)


def derive_v68b_repo_arc_cartography_gap_scan_report(
    *,
    manifest: RepoArcCartographyDerivationManifest,
) -> RepoArcCartographyGapScanReport:
    observed_refs = {row.source_ref for row in manifest.observed_input_rows}

    def refs(*items: str) -> list[str]:
        return sorted(item for item in items if item in observed_refs)

    gap_rows = [
        RepoArcCartographyGapRow(
            gap_id="gap:coordinate_posture_absent:V68-B",
            gap_family="coordinate_posture_absent",
            target_ref="coordinate:V68-B",
            target_namespace_kind="evidence_arc_id",
            severity="needs_review",
            claim_horizon="review_pending",
            source_refs=refs("docs/ASSESSMENT_vNEXT_PLUS189_EDGES.md"),
            recommended_next_action=(
                "Record coordinate absence until V68-C selects an emission posture."
            ),
            limitation_note="V68-B may expose absence but does not emit recursive coordinates.",
        ),
        RepoArcCartographyGapRow(
            gap_id="gap:tool_applicability_unassessed:V68-C",
            gap_family="tool_applicability_unassessed",
            target_ref="family:V68-C",
            target_namespace_kind="family_slice_id",
            severity="advisory",
            claim_horizon="future_deferred",
            source_refs=refs(
                "docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68B_IMPLEMENTATION_MAPPING_v0.md"
            ),
            recommended_next_action=(
                "Carry tool applicability hardening forward as a V68-C review item."
            ),
            limitation_note=(
                "V68-B describes this gap but does not run the V68-C tool evidence lane."
            ),
        ),
        RepoArcCartographyGapRow(
            gap_id="gap:review_required_ambiguous_derivation:historical_fullness",
            gap_family="review_required_ambiguous_derivation",
            target_ref="coverage:full_arc_history",
            target_namespace_kind="evidence_arc_id",
            severity="needs_review",
            claim_horizon="descriptive_support",
            source_refs=refs("docs/DRAFT_NEXT_ARC_OPTIONS_v54.md"),
            recommended_next_action=(
                "Keep the first derived map partial until additional historical rows are reviewed."
            ),
            limitation_note=(
                "Truthful partial coverage is preferred over fake whole-history completeness."
            ),
        ),
    ]
    payload = {
        "schema": REPO_ARC_CARTOGRAPHY_GAP_SCAN_REPORT_SCHEMA,
        "derivation_manifest_id": manifest.derivation_manifest_id,
        "cartography_id": manifest.cartography_id,
        "snapshot_id": manifest.snapshot_id,
        "coordinate_posture": "coordinate_absent_deliberate",
        "expected_missing_support_refs": [],
        "gap_rows": [
            row.model_dump(mode="json") for row in sorted(gap_rows, key=lambda row: row.gap_id)
        ],
        "limitation_note": (
            "Descriptive gap scan only; gap rows do not carry scheduling or delivery authority."
        ),
    }
    payload["gap_scan_report_id"] = _gap_report_id(payload)
    return RepoArcCartographyGapScanReport.model_validate(payload)


def derive_v68b_repo_arc_cartography_derivation_bundle(
    *,
    repo_root: Path,
    source_patterns: tuple[str, ...] = V68B_DEFAULT_SOURCE_PATTERNS,
) -> tuple[RepoArcCartographyDerivationManifest, RepoArcCartographyGapScanReport]:
    manifest = derive_v68b_repo_arc_cartography_derivation_manifest(
        repo_root=repo_root,
        source_patterns=source_patterns,
    )
    gap_scan = derive_v68b_repo_arc_cartography_gap_scan_report(manifest=manifest)
    return manifest, gap_scan
