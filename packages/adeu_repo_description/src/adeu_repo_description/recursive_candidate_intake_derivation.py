from __future__ import annotations

import json
from pathlib import Path
from typing import Literal

from pydantic import Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .arc_series_cartography import (
    _ABSOLUTE_PATH_RE,
    _GLOB_TOKEN_RE,
    SourceStatus,
    _CartographyBase,
    _non_empty,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    RequiredNextReviewSurface,
    _non_authority_note,
)

REPO_CANDIDATE_INTAKE_DERIVATION_MANIFEST_SCHEMA = "repo_candidate_intake_derivation_manifest@1"
REPO_CANDIDATE_INTAKE_GAP_SCAN_SCHEMA = "repo_candidate_intake_gap_scan@1"

CandidateDerivationPosture = Literal[
    "derived",
    "manual_seeded",
    "suppressed_duplicate",
    "suppressed_out_of_scope",
    "review_required",
]
CandidateGapKind = Literal[
    "expected_support_artifact_missing",
    "source_ref_missing",
    "source_presence_mismatch",
    "authority_layer_ambiguous",
    "origin_class_ambiguous",
    "odeu_lane_ambiguous",
    "v68_cartography_source_unmapped",
    "duplicate_without_equivalence",
    "candidate_without_guardrail",
    "candidate_overclaims_authority",
    "required_next_review_missing",
    "stale_candidate_source",
    "derivation_rule_inconclusive",
]
CandidateGapSeverity = Literal["info", "warning", "blocking"]

_SUPPORT_SOURCE_PREFIXES = ("docs/support/",)
_DEFAULT_INTAKE_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus191/"
    "repo_recursive_candidate_intake_v191_reference.json"
)

V69B_DEFAULT_SOURCE_PATTERNS: tuple[str, ...] = (
    _DEFAULT_INTAKE_FIXTURE,
    "artifacts/agent_harness/v191/evidence_inputs/v69a_recursive_candidate_intake_evidence_v191.json",
    "docs/ARCHITECTURE_ADEU_RECURSIVE_CANDIDATE_INTAKE_FAMILY_v0.md",
    "docs/ASSESSMENT_vNEXT_PLUS191_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS192_EDGES.md",
    "docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md",
    "docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v56.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v57.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v58.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS191.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS192.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS191.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS192.md",
    "docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md",
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.report.json",
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md",
    "docs/support/arc_series_mapping/REVIEW_GPTPRO_RECURSIVE_CANDIDATE_INTAKE_V69_PLANNING_v0.md",
    "docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.json",
    "docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md",
    "docs/support/arc_series_mapping/odeu_conceptual_diff_report.schema.json",
)


def _repo_pattern(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    if _ABSOLUTE_PATH_RE.search(normalized):
        raise ValueError(f"{field_name} must be repo-relative, not absolute")
    parts = normalized.split("/")
    if any(part == ".." for part in parts):
        raise ValueError(f"{field_name} must not traverse outside the repo")
    return normalized


def _source_kind_for_ref(source_ref: str) -> CandidateSourceKind:
    if source_ref.startswith("docs/DRAFT_NEXT_ARC_OPTIONS_"):
        return "planning_doc"
    if source_ref.startswith("docs/ARCHITECTURE_"):
        return "architecture_doc"
    if source_ref.startswith("docs/support/") and source_ref.endswith(".schema.json"):
        return "schema_file"
    if source_ref.startswith("docs/support/") and source_ref.endswith(".report.json"):
        return "support_doc"
    if source_ref.startswith("docs/support/") and "REVIEW_" in source_ref:
        return "review_input"
    if source_ref.startswith("docs/support/"):
        return "support_doc"
    if source_ref.startswith("docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_"):
        return "closeout_doc"
    if source_ref.startswith("docs/DRAFT_STOP_GATE_DECISION_"):
        return "evidence_artifact"
    if source_ref.startswith("docs/ASSESSMENT_"):
        return "evidence_artifact"
    if source_ref.startswith("apps/api/fixtures/"):
        return "fixture_file"
    if source_ref.startswith("artifacts/"):
        return "evidence_artifact"
    if source_ref.startswith(("packages/", "spec/")) and source_ref.endswith(".json"):
        return "schema_file"
    return "repo_observation"


def _authority_layer_for_ref(source_ref: str) -> CandidateAuthorityLayer:
    if source_ref.startswith("docs/LOCKED_CONTINUATION_"):
        return "lock"
    if source_ref.startswith("docs/ARCHITECTURE_"):
        return "architecture"
    if source_ref.startswith("docs/DRAFT_NEXT_ARC_OPTIONS_"):
        return "planning"
    if source_ref.startswith(("packages/", "spec/")) and source_ref.endswith(".json"):
        return "schema"
    if source_ref.startswith("apps/api/fixtures/"):
        return "fixture"
    if source_ref.startswith("docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_"):
        return "closeout_evidence"
    if source_ref.startswith(("artifacts/", "docs/DRAFT_STOP_GATE_DECISION_", "docs/ASSESSMENT_")):
        return "closeout_evidence"
    return "support"


def _source_refs_are_support_only(source_refs: list[str]) -> bool:
    return bool(source_refs) and all(
        ref.startswith(_SUPPORT_SOURCE_PREFIXES) for ref in source_refs
    )


class RepoCandidateIntakeObservedSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    observed_for_patterns: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_observed_source(self) -> RepoCandidateIntakeObservedSourceRow:
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self,
            "observed_for_patterns",
            _sorted_unique(self.observed_for_patterns, field_name="observed_for_patterns"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_authority_note(self.limitation_note, field_name="limitation_note"),
        )
        for pattern in self.observed_for_patterns:
            _repo_pattern(pattern, field_name="observed_for_patterns")
        if (
            self.source_status == "integrated_shaping_source"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("integrated observed sources must have presence posture present")
        if self.authority_layer == "lock" and self.source_ref.startswith("docs/support/"):
            raise ValueError("support-layer observed sources cannot become lock authority")
        return self


class RepoCandidateDerivationRow(_CartographyBase):
    derivation_ref: str
    candidate_ref: str
    derivation_posture: CandidateDerivationPosture
    derived_authority_layer: CandidateAuthorityLayer
    derivation_rule_ref: str
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_derivation_row(self) -> RepoCandidateDerivationRow:
        object.__setattr__(
            self,
            "derivation_ref",
            _non_empty(self.derivation_ref, field_name="derivation_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "derivation_rule_ref",
            _non_empty(self.derivation_rule_ref, field_name="derivation_rule_ref"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_authority_note(self.limitation_note, field_name="limitation_note"),
        )
        for ref in self.source_refs:
            _repo_ref(ref, field_name="derivation source_refs")
        if self.derived_authority_layer == "lock" and _source_refs_are_support_only(
            self.source_refs
        ):
            raise ValueError("support input cannot be upgraded to lock authority")
        return self


class RepoCandidateDuplicateGroup(_CartographyBase):
    duplicate_group_ref: str
    candidate_refs: list[str] = Field(min_length=2)
    source_refs: list[str] = Field(default_factory=list)
    equivalence_posture: Literal["equivalent_to_existing_candidate", "review_required"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_duplicate_group(self) -> RepoCandidateDuplicateGroup:
        object.__setattr__(
            self,
            "duplicate_group_ref",
            _non_empty(self.duplicate_group_ref, field_name="duplicate_group_ref"),
        )
        object.__setattr__(
            self,
            "candidate_refs",
            _sorted_unique(self.candidate_refs, field_name="candidate_refs"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_authority_note(self.limitation_note, field_name="limitation_note"),
        )
        for ref in self.source_refs:
            _repo_ref(ref, field_name="duplicate source_refs")
        return self


class RepoCandidateIntakeDerivationManifest(_CartographyBase):
    schema: Literal["repo_candidate_intake_derivation_manifest@1"] = (
        REPO_CANDIDATE_INTAKE_DERIVATION_MANIFEST_SCHEMA
    )
    derivation_manifest_id: str
    intake_id: str
    snapshot_id: str
    coverage_horizon: str
    source_globs_scanned: list[str] = Field(min_length=1)
    observed_source_rows: list[RepoCandidateIntakeObservedSourceRow] = Field(min_length=1)
    derivation_rows: list[RepoCandidateDerivationRow] = Field(min_length=1)
    duplicate_groups: list[RepoCandidateDuplicateGroup] = Field(default_factory=list)
    candidate_refs_emitted: list[str] = Field(default_factory=list)
    candidate_refs_suppressed: list[str] = Field(default_factory=list)
    derivation_limitations: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_manifest(self) -> RepoCandidateIntakeDerivationManifest:
        object.__setattr__(
            self,
            "derivation_manifest_id",
            _non_empty(self.derivation_manifest_id, field_name="derivation_manifest_id"),
        )
        object.__setattr__(self, "intake_id", _non_empty(self.intake_id, field_name="intake_id"))
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
            "source_globs_scanned",
            _sorted_unique(self.source_globs_scanned, field_name="source_globs_scanned"),
        )
        object.__setattr__(
            self,
            "observed_source_rows",
            _sorted_unique_by_ref(
                self.observed_source_rows,
                attr="source_ref",
                field_name="observed_source_rows",
            ),
        )
        object.__setattr__(
            self,
            "derivation_rows",
            _sorted_unique_by_ref(
                self.derivation_rows,
                attr="derivation_ref",
                field_name="derivation_rows",
            ),
        )
        object.__setattr__(
            self,
            "duplicate_groups",
            _sorted_unique_by_ref(
                self.duplicate_groups,
                attr="duplicate_group_ref",
                field_name="duplicate_groups",
            ),
        )
        object.__setattr__(
            self,
            "candidate_refs_emitted",
            _sorted_unique(self.candidate_refs_emitted, field_name="candidate_refs_emitted"),
        )
        object.__setattr__(
            self,
            "candidate_refs_suppressed",
            _sorted_unique(self.candidate_refs_suppressed, field_name="candidate_refs_suppressed"),
        )
        object.__setattr__(
            self,
            "derivation_limitations",
            _sorted_unique(
                [
                    _non_authority_note(note, field_name="derivation_limitations")
                    for note in self.derivation_limitations
                ],
                field_name="derivation_limitations",
            ),
        )
        for pattern in self.source_globs_scanned:
            _repo_pattern(pattern, field_name="source_globs_scanned")
        observed_refs = {row.source_ref for row in self.observed_source_rows}
        derived_candidate_refs = {row.candidate_ref for row in self.derivation_rows}
        emitted_rows = {
            row.candidate_ref
            for row in self.derivation_rows
            if row.derivation_posture in {"derived", "manual_seeded", "review_required"}
        }
        suppressed_rows = {
            row.candidate_ref
            for row in self.derivation_rows
            if row.derivation_posture in {"suppressed_duplicate", "suppressed_out_of_scope"}
        }
        for row in self.derivation_rows:
            missing = sorted(set(row.source_refs) - observed_refs)
            if missing:
                raise ValueError(
                    f"derivation source_refs must reference observed sources: {missing}"
                )
        emitted_mismatch = sorted(set(self.candidate_refs_emitted) ^ emitted_rows)
        if emitted_mismatch:
            raise ValueError(
                f"candidate_refs_emitted must match emitted derivation rows: {emitted_mismatch}"
            )
        suppressed_mismatch = sorted(set(self.candidate_refs_suppressed) ^ suppressed_rows)
        if suppressed_mismatch:
            raise ValueError(
                "candidate_refs_suppressed must match suppressed derivation rows: "
                f"{suppressed_mismatch}"
            )
        duplicate_candidate_refs = {
            candidate_ref
            for group in self.duplicate_groups
            for candidate_ref in group.candidate_refs
        }
        duplicate_suppressed = {
            row.candidate_ref
            for row in self.derivation_rows
            if row.derivation_posture == "suppressed_duplicate"
        }
        missing_duplicate_witness = sorted(duplicate_suppressed - duplicate_candidate_refs)
        if missing_duplicate_witness:
            raise ValueError(
                "suppressed_duplicate candidates require duplicate_groups: "
                f"{missing_duplicate_witness}"
            )
        unknown_duplicate_refs = sorted(duplicate_candidate_refs - derived_candidate_refs)
        if unknown_duplicate_refs:
            raise ValueError(
                f"duplicate_groups must reference derived candidates: {unknown_duplicate_refs}"
            )
        return self


class RepoCandidateIntakeGapRow(_CartographyBase):
    gap_ref: str
    gap_kind: CandidateGapKind
    target_candidate_ref: str
    source_refs: list[str] = Field(default_factory=list)
    severity: CandidateGapSeverity
    recommended_next_surface: RequiredNextReviewSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_gap_row(self) -> RepoCandidateIntakeGapRow:
        object.__setattr__(self, "gap_ref", _non_empty(self.gap_ref, field_name="gap_ref"))
        object.__setattr__(
            self,
            "target_candidate_ref",
            _non_empty(self.target_candidate_ref, field_name="target_candidate_ref"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_authority_note(self.limitation_note, field_name="limitation_note"),
        )
        for ref in self.source_refs:
            _repo_ref(ref, field_name="gap source_refs")
        if self.gap_kind == "candidate_overclaims_authority" and self.severity != "blocking":
            raise ValueError("candidate overclaims must remain blocking gaps")
        return self


class RepoCandidateIntakeGapScan(_CartographyBase):
    schema: Literal["repo_candidate_intake_gap_scan@1"] = REPO_CANDIDATE_INTAKE_GAP_SCAN_SCHEMA
    gap_scan_id: str
    derivation_manifest_id: str
    intake_id: str
    snapshot_id: str
    observed_source_refs: list[str] = Field(min_length=1)
    expected_missing_support_refs: list[str] = Field(default_factory=list)
    expected_v68_unmapped_source_refs: list[str] = Field(default_factory=list)
    expected_overclaim_candidate_refs: list[str] = Field(default_factory=list)
    gap_rows: list[RepoCandidateIntakeGapRow] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_gap_scan(self) -> RepoCandidateIntakeGapScan:
        object.__setattr__(
            self,
            "gap_scan_id",
            _non_empty(self.gap_scan_id, field_name="gap_scan_id"),
        )
        object.__setattr__(
            self,
            "derivation_manifest_id",
            _non_empty(self.derivation_manifest_id, field_name="derivation_manifest_id"),
        )
        object.__setattr__(self, "intake_id", _non_empty(self.intake_id, field_name="intake_id"))
        object.__setattr__(
            self,
            "snapshot_id",
            _non_empty(self.snapshot_id, field_name="snapshot_id"),
        )
        object.__setattr__(
            self,
            "observed_source_refs",
            _sorted_unique(self.observed_source_refs, field_name="observed_source_refs"),
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
            "expected_v68_unmapped_source_refs",
            _sorted_unique(
                self.expected_v68_unmapped_source_refs,
                field_name="expected_v68_unmapped_source_refs",
            ),
        )
        object.__setattr__(
            self,
            "expected_overclaim_candidate_refs",
            _sorted_unique(
                self.expected_overclaim_candidate_refs,
                field_name="expected_overclaim_candidate_refs",
            ),
        )
        object.__setattr__(
            self,
            "gap_rows",
            _sorted_unique_by_ref(self.gap_rows, attr="gap_ref", field_name="gap_rows"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_authority_note(self.limitation_note, field_name="limitation_note"),
        )
        for ref in self.observed_source_refs:
            _repo_ref(ref, field_name="observed_source_refs")
        for ref in self.expected_missing_support_refs:
            _repo_ref(ref, field_name="expected_missing_support_refs")
        for ref in self.expected_v68_unmapped_source_refs:
            _repo_ref(ref, field_name="expected_v68_unmapped_source_refs")
        observed_refs = set(self.observed_source_refs)
        for row in self.gap_rows:
            missing = sorted(set(row.source_refs) - observed_refs)
            if missing:
                raise ValueError(f"gap source_refs must reference observed sources: {missing}")
        missing_support_gap_targets = {
            row.target_candidate_ref
            for row in self.gap_rows
            if row.gap_kind == "expected_support_artifact_missing"
        }
        missing_expected_support = sorted(
            set(self.expected_missing_support_refs) - missing_support_gap_targets
        )
        if missing_expected_support:
            raise ValueError(
                "expected missing support artifacts require expected_support_artifact_missing "
                f"gap rows: {missing_expected_support}"
            )
        v68_unmapped_gap_targets = {
            row.target_candidate_ref
            for row in self.gap_rows
            if row.gap_kind == "v68_cartography_source_unmapped"
        }
        missing_v68_unmapped = sorted(
            set(self.expected_v68_unmapped_source_refs) - v68_unmapped_gap_targets
        )
        if missing_v68_unmapped:
            raise ValueError(
                "V68 cartography unmapped sources require v68_cartography_source_unmapped "
                f"gap rows: {missing_v68_unmapped}"
            )
        overclaim_gap_targets = {
            row.target_candidate_ref
            for row in self.gap_rows
            if row.gap_kind == "candidate_overclaims_authority"
        }
        missing_overclaim_gaps = sorted(
            set(self.expected_overclaim_candidate_refs) - overclaim_gap_targets
        )
        if missing_overclaim_gaps:
            raise ValueError(
                "candidate overclaims require blocking candidate_overclaims_authority gaps: "
                f"{missing_overclaim_gaps}"
            )
        return self


def _observe_source_patterns(
    *,
    root: Path,
    source_patterns: tuple[str, ...],
) -> list[RepoCandidateIntakeObservedSourceRow]:
    rows: list[RepoCandidateIntakeObservedSourceRow] = []
    seen: dict[str, set[str]] = {}
    for pattern in source_patterns:
        _repo_pattern(pattern, field_name="source_patterns")
        matches = sorted(path for path in root.glob(pattern) if path.is_file())
        if not matches and not _GLOB_TOKEN_RE.search(pattern):
            raise ValueError(f"expected V69-B source file is missing: {pattern}")
        for path in matches:
            source_ref = path.relative_to(root).as_posix()
            seen.setdefault(source_ref, set()).add(pattern)
    for source_ref in sorted(seen):
        rows.append(
            RepoCandidateIntakeObservedSourceRow(
                source_ref=source_ref,
                source_kind=_source_kind_for_ref(source_ref),
                authority_layer=_authority_layer_for_ref(source_ref),
                source_status="integrated_shaping_source",
                source_presence_posture="present",
                observed_for_patterns=sorted(seen[source_ref]),
                limitation_note="Observed as a concrete V69-B candidate-derivation input.",
            )
        )
    return rows


def _derivation_manifest_id(payload_without_id: dict[str, object]) -> str:
    payload = dict(payload_without_id)
    payload.setdefault("schema", REPO_CANDIDATE_INTAKE_DERIVATION_MANIFEST_SCHEMA)
    payload.pop("derivation_manifest_id", None)
    digest = sha256_canonical_json(payload)
    return f"repo_candidate_intake_derivation_manifest_{digest[:24]}"


def _gap_scan_id(payload_without_id: dict[str, object]) -> str:
    payload = dict(payload_without_id)
    payload.setdefault("schema", REPO_CANDIDATE_INTAKE_GAP_SCAN_SCHEMA)
    payload.pop("gap_scan_id", None)
    digest = sha256_canonical_json(payload)
    return f"repo_candidate_intake_gap_scan_{digest[:24]}"


def _load_intake_reference(repo_root: Path) -> dict[str, object]:
    path = repo_root / _DEFAULT_INTAKE_FIXTURE
    return json.loads(path.read_text(encoding="utf-8"))


def derive_v69b_repo_candidate_intake_derivation_manifest(
    *,
    repo_root: Path,
    source_patterns: tuple[str, ...] = V69B_DEFAULT_SOURCE_PATTERNS,
) -> RepoCandidateIntakeDerivationManifest:
    observed_source_rows = _observe_source_patterns(root=repo_root, source_patterns=source_patterns)
    observed_refs = {row.source_ref for row in observed_source_rows}
    if not observed_source_rows:
        raise ValueError("V69-B derivation manifest requires at least one observed input")
    if _DEFAULT_INTAKE_FIXTURE not in observed_refs:
        raise ValueError(
            f"expected V69-B derivation source_refs are missing: [{_DEFAULT_INTAKE_FIXTURE!r}]"
        )

    intake_payload = _load_intake_reference(repo_root)
    candidate_rows = intake_payload["candidate_rows"]
    if not isinstance(candidate_rows, list):
        raise ValueError("V69-A intake reference candidate_rows must be a list")

    derivation_rows: list[RepoCandidateDerivationRow] = []
    emitted_refs: list[str] = []
    for raw_row in sorted(candidate_rows, key=lambda row: row["candidate_ref"]):
        candidate_ref = str(raw_row["candidate_ref"])
        raw_source_refs = raw_row["source_refs"]
        if not isinstance(raw_source_refs, list):
            raise ValueError("V69-A intake candidate source_refs must be lists")
        source_refs = sorted(str(ref) for ref in raw_source_refs)
        missing = sorted(ref for ref in source_refs if ref not in observed_refs)
        if missing:
            raise ValueError(f"expected V69-B derivation source_refs are missing: {missing}")
        derivation_rows.append(
            RepoCandidateDerivationRow(
                derivation_ref=f"derivation:{candidate_ref}",
                candidate_ref=candidate_ref,
                derivation_posture="derived",
                derived_authority_layer="support",
                derivation_rule_ref="rule:v69b:source_bound_candidate_from_v69a_reference",
                source_refs=source_refs,
                limitation_note=(
                    "Derived as candidate pressure only from V69-A source-bound intake rows."
                ),
            )
        )
        emitted_refs.append(candidate_ref)

    payload = {
        "schema": REPO_CANDIDATE_INTAKE_DERIVATION_MANIFEST_SCHEMA,
        "intake_id": str(intake_payload["intake_id"]),
        "snapshot_id": "vNext+192-prestart-on-main",
        "coverage_horizon": (
            "V69-B starter derivation over V69-A reference fixture and committed "
            "V69 planning/support seed sources only"
        ),
        "source_globs_scanned": sorted(source_patterns),
        "observed_source_rows": [row.model_dump(mode="json") for row in observed_source_rows],
        "derivation_rows": [row.model_dump(mode="json") for row in derivation_rows],
        "duplicate_groups": [],
        "candidate_refs_emitted": sorted(emitted_refs),
        "candidate_refs_suppressed": [],
        "derivation_limitations": [
            "Derivation is descriptive intake support only.",
            "No candidate receives evidence verdicts or downstream authority from this manifest.",
        ],
    }
    payload["derivation_manifest_id"] = _derivation_manifest_id(payload)
    return RepoCandidateIntakeDerivationManifest.model_validate(payload)


def derive_v69b_repo_candidate_intake_gap_scan(
    *,
    manifest: RepoCandidateIntakeDerivationManifest,
) -> RepoCandidateIntakeGapScan:
    observed_refs = {row.source_ref for row in manifest.observed_source_rows}

    def refs(*items: str) -> list[str]:
        missing = sorted(item for item in items if item not in observed_refs)
        if missing:
            raise ValueError(f"expected V69-B gap-scan source_refs are missing: {missing}")
        return list(items)

    v68_unmapped_source = "docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md"
    gap_rows = [
        RepoCandidateIntakeGapRow(
            gap_ref="gap:derivation_rule_inconclusive:full_candidate_discovery",
            gap_kind="derivation_rule_inconclusive",
            target_candidate_ref="coverage:full_candidate_discovery",
            source_refs=refs(
                "docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69B_IMPLEMENTATION_MAPPING_v0.md"
            ),
            severity="info",
            recommended_next_surface="future_family_review",
            limitation_note=(
                "Reference derivation is bounded to present V69 seed sources and is "
                "not whole-repo discovery."
            ),
        ),
        RepoCandidateIntakeGapRow(
            gap_ref="gap:v68_cartography_source_unmapped:V69_PREFLIGHT_DOGFOOD_TEST_v0",
            gap_kind="v68_cartography_source_unmapped",
            target_candidate_ref=v68_unmapped_source,
            source_refs=refs(v68_unmapped_source),
            severity="warning",
            recommended_next_surface="future_family_review",
            limitation_note=(
                "This post-V68 candidate source is expected to be absent from the closed V68 map."
            ),
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_INTAKE_GAP_SCAN_SCHEMA,
        "derivation_manifest_id": manifest.derivation_manifest_id,
        "intake_id": manifest.intake_id,
        "snapshot_id": manifest.snapshot_id,
        "observed_source_refs": sorted(observed_refs),
        "expected_missing_support_refs": [],
        "expected_v68_unmapped_source_refs": [v68_unmapped_source],
        "expected_overclaim_candidate_refs": [],
        "gap_rows": [
            row.model_dump(mode="json") for row in sorted(gap_rows, key=lambda row: row.gap_ref)
        ],
        "limitation_note": (
            "Descriptive V69-B gap scan only; gaps carry no adoption or scheduling authority."
        ),
    }
    payload["gap_scan_id"] = _gap_scan_id(payload)
    return RepoCandidateIntakeGapScan.model_validate(payload)


def derive_v69b_repo_candidate_intake_derivation_bundle(
    *,
    repo_root: Path,
    source_patterns: tuple[str, ...] = V69B_DEFAULT_SOURCE_PATTERNS,
) -> tuple[RepoCandidateIntakeDerivationManifest, RepoCandidateIntakeGapScan]:
    manifest = derive_v69b_repo_candidate_intake_derivation_manifest(
        repo_root=repo_root,
        source_patterns=source_patterns,
    )
    gap_scan = derive_v69b_repo_candidate_intake_gap_scan(manifest=manifest)
    return manifest, gap_scan
