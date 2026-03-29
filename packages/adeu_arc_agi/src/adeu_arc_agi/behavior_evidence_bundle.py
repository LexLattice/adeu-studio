from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .three_puzzle_harness import AdeuArcThreePuzzleHarnessRecord

ADEU_ARC_BEHAVIOR_EVIDENCE_BUNDLE_SCHEMA = "adeu_arc_behavior_evidence_bundle@1"
V42G4_V98_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS98.md#v98-continuation-contract-machine-checkable"
)

ClaimInferenceKind = Literal["observed_per_puzzle", "inferred_cross_puzzle"]
SupportPosture = Literal["supported_subset", "supported_all_three"]
ConfigConsistencyPosture = Literal[
    "uniform_across_all_puzzles",
    "explicit_divergence_declared",
]

_EXPECTED_PUZZLE_COUNT = 3
_FORBIDDEN_AUTHORITY_TERMS: tuple[str, ...] = (
    "leaderboard_ready",
    "leaderboard_readiness",
    "universal_necessity",
    "blanket_competitiveness",
    "official_authority_granted",
    "deterministic_fresh_model_reexecution",
    "semantic_solver_authority",
    "puzzle_rule_authority",
    "capability_authority",
)


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field_name} must be a string")
    if not value:
        raise ValueError(f"{field_name} must not be empty")
    if value != value.strip():
        raise ValueError(f"{field_name} must not include leading/trailing whitespace")
    return value


def _assert_sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted lexicographically")
    return normalized


def _assert_unique_preserving_order(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return normalized


def _assert_hash(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if len(normalized) != 64:
        raise ValueError(f"{field_name} must be a 64-character lowercase hex digest")
    for ch in normalized:
        if ch not in "0123456789abcdef":
            raise ValueError(f"{field_name} must be a 64-character lowercase hex digest")
    return normalized


def _normalize_for_term_match(value: str) -> str:
    lowered = value.lower()
    for token in ("-", " "):
        lowered = lowered.replace(token, "_")
    return lowered


def _assert_no_forbidden_terms(*, value: str, field_name: str, terms: tuple[str, ...]) -> None:
    normalized = _normalize_for_term_match(value)
    for term in terms:
        normalized_term = _normalize_for_term_match(term)
        if normalized_term in normalized:
            raise ValueError(f"{field_name} may not contain forbidden term '{term}'")


def _puzzle_behavior_entry_ref(puzzle_id: str) -> str:
    return f"puzzle_behavior:{puzzle_id}"


def _cross_pattern_claim_target(pattern_id: str) -> str:
    return f"cross_pattern:{pattern_id}"


class ArcBehaviorCrossPuzzlePatternEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    pattern_id: str
    pattern_kind: str
    support_puzzle_ids: list[str] = Field(min_length=1)
    support_behavior_entry_refs: list[str] = Field(min_length=1)
    support_evidence_refs: list[str] = Field(min_length=1)
    pattern_claim_posture: str
    support_posture: SupportPosture

    @model_validator(mode="after")
    def _validate_entry(self) -> ArcBehaviorCrossPuzzlePatternEntry:
        object.__setattr__(
            self, "pattern_id", _assert_non_empty_text(self.pattern_id, field_name="pattern_id")
        )
        object.__setattr__(
            self,
            "pattern_kind",
            _assert_non_empty_text(self.pattern_kind, field_name="pattern_kind"),
        )
        object.__setattr__(
            self,
            "pattern_claim_posture",
            _assert_non_empty_text(self.pattern_claim_posture, field_name="pattern_claim_posture"),
        )
        object.__setattr__(
            self,
            "support_puzzle_ids",
            _assert_unique_preserving_order(
                self.support_puzzle_ids, field_name="support_puzzle_ids"
            ),
        )
        object.__setattr__(
            self,
            "support_behavior_entry_refs",
            _assert_sorted_unique(
                self.support_behavior_entry_refs, field_name="support_behavior_entry_refs"
            ),
        )
        object.__setattr__(
            self,
            "support_evidence_refs",
            _assert_sorted_unique(self.support_evidence_refs, field_name="support_evidence_refs"),
        )
        return self


class ArcBehaviorFailureModeEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    failure_mode_id: str
    failure_mode_kind: str
    failure_mode_scope: str
    evidence_refs: list[str] = Field(min_length=1)
    claim_posture: str

    @model_validator(mode="after")
    def _validate_entry(self) -> ArcBehaviorFailureModeEntry:
        object.__setattr__(
            self,
            "failure_mode_id",
            _assert_non_empty_text(self.failure_mode_id, field_name="failure_mode_id"),
        )
        object.__setattr__(
            self,
            "failure_mode_kind",
            _assert_non_empty_text(self.failure_mode_kind, field_name="failure_mode_kind"),
        )
        object.__setattr__(
            self,
            "failure_mode_scope",
            _assert_non_empty_text(self.failure_mode_scope, field_name="failure_mode_scope"),
        )
        object.__setattr__(
            self,
            "claim_posture",
            _assert_non_empty_text(self.claim_posture, field_name="claim_posture"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )
        _assert_no_forbidden_terms(
            value=self.failure_mode_scope,
            field_name="failure_mode_scope",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )
        return self


class ArcBehaviorClaimPostureEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    claim_id: str
    claim_target_ref: str
    supporting_refs: list[str] = Field(min_length=1)
    posture_kind: str
    limitation_scope: str
    claim_inference_kind: ClaimInferenceKind

    @model_validator(mode="after")
    def _validate_entry(self) -> ArcBehaviorClaimPostureEntry:
        text_fields = (
            "claim_id",
            "claim_target_ref",
            "posture_kind",
            "limitation_scope",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "supporting_refs",
            _assert_sorted_unique(self.supporting_refs, field_name="supporting_refs"),
        )
        if (
            self.claim_inference_kind == "observed_per_puzzle"
            and not self.claim_target_ref.startswith("puzzle_behavior:")
        ):
            raise ValueError(
                "observed_per_puzzle claim_inference_kind requires claim_target_ref to start "
                "with 'puzzle_behavior:'"
            )
        if (
            self.claim_inference_kind == "inferred_cross_puzzle"
            and not self.claim_target_ref.startswith("cross_pattern:")
        ):
            raise ValueError(
                "inferred_cross_puzzle claim_inference_kind requires claim_target_ref to start "
                "with 'cross_pattern:'"
            )
        _assert_no_forbidden_terms(
            value=self.claim_target_ref,
            field_name="claim_target_ref",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )
        _assert_no_forbidden_terms(
            value=self.limitation_scope,
            field_name="limitation_scope",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )
        return self


class ArcBehaviorAuthorityBoundaryRegister(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    authoritative_surface_refs: list[str] = Field(min_length=1)
    descriptive_only_surface_refs: list[str] = Field(min_length=1)
    deferred_claim_refs: list[str] = Field(default_factory=list)
    boundary_violation_flags: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_register(self) -> ArcBehaviorAuthorityBoundaryRegister:
        object.__setattr__(
            self,
            "authoritative_surface_refs",
            _assert_sorted_unique(
                self.authoritative_surface_refs, field_name="authoritative_surface_refs"
            ),
        )
        object.__setattr__(
            self,
            "descriptive_only_surface_refs",
            _assert_sorted_unique(
                self.descriptive_only_surface_refs, field_name="descriptive_only_surface_refs"
            ),
        )
        object.__setattr__(
            self,
            "deferred_claim_refs",
            _assert_sorted_unique(self.deferred_claim_refs, field_name="deferred_claim_refs"),
        )
        object.__setattr__(
            self,
            "boundary_violation_flags",
            _assert_sorted_unique(
                self.boundary_violation_flags, field_name="boundary_violation_flags"
            ),
        )
        if set(self.authoritative_surface_refs) & set(self.descriptive_only_surface_refs):
            raise ValueError(
                "authority_boundary_register authoritative and descriptive surface refs must be "
                "disjoint"
            )
        if self.boundary_violation_flags:
            raise ValueError(
                "authority_boundary_register boundary_violation_flags must be empty for valid "
                "v42g4 bundles"
            )
        return self


class AdeuArcPerPuzzleBehaviorEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    puzzle_index: int = Field(ge=1, le=_EXPECTED_PUZZLE_COUNT)
    puzzle_id: str
    reasoning_run_record_ref: str
    local_eval_ref: str
    scorecard_manifest_ref: str | None = None
    submission_execution_record_ref: str | None = None
    behavior_signal_refs: list[str] = Field(min_length=1)
    mapped_failure_mode_ids: list[str] = Field(min_length=1)
    claim_posture: str

    @model_validator(mode="after")
    def _validate_entry(self) -> AdeuArcPerPuzzleBehaviorEntry:
        text_fields = (
            "puzzle_id",
            "reasoning_run_record_ref",
            "local_eval_ref",
            "claim_posture",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.scorecard_manifest_ref is not None:
            object.__setattr__(
                self,
                "scorecard_manifest_ref",
                _assert_non_empty_text(
                    self.scorecard_manifest_ref, field_name="scorecard_manifest_ref"
                ),
            )
        if self.submission_execution_record_ref is not None:
            object.__setattr__(
                self,
                "submission_execution_record_ref",
                _assert_non_empty_text(
                    self.submission_execution_record_ref,
                    field_name="submission_execution_record_ref",
                ),
            )
        object.__setattr__(
            self,
            "behavior_signal_refs",
            _assert_sorted_unique(self.behavior_signal_refs, field_name="behavior_signal_refs"),
        )
        object.__setattr__(
            self,
            "mapped_failure_mode_ids",
            _assert_sorted_unique(
                self.mapped_failure_mode_ids, field_name="mapped_failure_mode_ids"
            ),
        )
        return self


class AdeuArcBehaviorEvidenceBundle(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_BEHAVIOR_EVIDENCE_BUNDLE_SCHEMA] = (
        ADEU_ARC_BEHAVIOR_EVIDENCE_BUNDLE_SCHEMA
    )
    behavior_evidence_bundle_id: str
    harness_record_id: str
    harness_run_id: str
    puzzle_input_bundle_id: str
    selection_register_id: str
    selection_register_hash: str
    selected_puzzle_ids: list[str] = Field(
        min_length=_EXPECTED_PUZZLE_COUNT,
        max_length=_EXPECTED_PUZZLE_COUNT,
    )
    canonical_puzzle_order: list[str] = Field(
        min_length=_EXPECTED_PUZZLE_COUNT,
        max_length=_EXPECTED_PUZZLE_COUNT,
    )
    per_puzzle_behavior_entries: list[AdeuArcPerPuzzleBehaviorEntry] = Field(
        min_length=_EXPECTED_PUZZLE_COUNT,
        max_length=_EXPECTED_PUZZLE_COUNT,
    )
    cross_puzzle_pattern_entries: list[ArcBehaviorCrossPuzzlePatternEntry] = Field(min_length=1)
    failure_mode_catalog: list[ArcBehaviorFailureModeEntry] = Field(min_length=1)
    claim_posture_register: list[ArcBehaviorClaimPostureEntry] = Field(min_length=1)
    authority_boundary_register: ArcBehaviorAuthorityBoundaryRegister
    cross_puzzle_config_consistency_posture: ConfigConsistencyPosture
    deterministic_replay_scope_note: str
    behavior_summary: str
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_bundle(self) -> AdeuArcBehaviorEvidenceBundle:
        text_fields = (
            "behavior_evidence_bundle_id",
            "harness_record_id",
            "harness_run_id",
            "puzzle_input_bundle_id",
            "selection_register_id",
            "deterministic_replay_scope_note",
            "behavior_summary",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )

        object.__setattr__(
            self,
            "selection_register_hash",
            _assert_hash(self.selection_register_hash, field_name="selection_register_hash"),
        )
        object.__setattr__(
            self,
            "selected_puzzle_ids",
            _assert_unique_preserving_order(
                self.selected_puzzle_ids, field_name="selected_puzzle_ids"
            ),
        )
        object.__setattr__(
            self,
            "canonical_puzzle_order",
            _assert_unique_preserving_order(
                self.canonical_puzzle_order, field_name="canonical_puzzle_order"
            ),
        )
        if self.selected_puzzle_ids != self.canonical_puzzle_order:
            raise ValueError("canonical_puzzle_order must match selected_puzzle_ids exactly")
        if self.selected_puzzle_ids != sorted(self.selected_puzzle_ids):
            raise ValueError("selected_puzzle_ids must be sorted lexicographically")

        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )

        if "fixed" not in self.deterministic_replay_scope_note.lower():
            raise ValueError(
                "deterministic_replay_scope_note must explicitly describe fixed-artifact "
                "replay scope"
            )
        _assert_no_forbidden_terms(
            value=self.behavior_summary,
            field_name="behavior_summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )
        expected_harness_ref = f"harness_record:{self.harness_record_id}"
        if expected_harness_ref not in self.authority_boundary_register.authoritative_surface_refs:
            raise ValueError(
                "authority_boundary_register authoritative_surface_refs must include "
                "harness_record "
                "binding for harness_record_id"
            )

        puzzle_entries_by_id: dict[str, AdeuArcPerPuzzleBehaviorEntry] = {}
        for expected_index, entry in enumerate(self.per_puzzle_behavior_entries, start=1):
            if entry.puzzle_index != expected_index:
                raise ValueError(
                    "per_puzzle_behavior_entries must be in canonical puzzle_index order "
                    "with no gaps"
                )
            expected_puzzle_id = self.canonical_puzzle_order[expected_index - 1]
            if entry.puzzle_id != expected_puzzle_id:
                raise ValueError(
                    "per_puzzle_behavior_entries puzzle_id order must follow canonical_puzzle_order"
                )
            puzzle_entries_by_id[entry.puzzle_id] = entry

        failure_mode_ids = [entry.failure_mode_id for entry in self.failure_mode_catalog]
        if len(failure_mode_ids) != len(set(failure_mode_ids)):
            raise ValueError(
                "failure_mode_catalog must not contain duplicate failure_mode_id values"
            )
        failure_mode_id_set = set(failure_mode_ids)

        claim_entries_by_id: dict[str, ArcBehaviorClaimPostureEntry] = {}
        for entry in self.claim_posture_register:
            if entry.claim_id in claim_entries_by_id:
                raise ValueError(
                    "claim_posture_register must not contain duplicate claim_id values"
                )
            claim_entries_by_id[entry.claim_id] = entry

        for entry in self.per_puzzle_behavior_entries:
            for failure_mode_id in entry.mapped_failure_mode_ids:
                if failure_mode_id not in failure_mode_id_set:
                    raise ValueError(
                        "per_puzzle_behavior_entries mapped_failure_mode_ids must reference "
                        "failure_mode_catalog entries"
                    )
            if entry.claim_posture not in claim_entries_by_id:
                raise ValueError(
                    "per_puzzle_behavior_entries claim_posture values must reference "
                    "claim_posture_register claim_id values"
                )
            expected_target = _puzzle_behavior_entry_ref(entry.puzzle_id)
            claim_entry = claim_entries_by_id[entry.claim_posture]
            if claim_entry.claim_target_ref != expected_target:
                raise ValueError(
                    "per-puzzle claim_posture entries must target matching puzzle_behavior surface"
                )
            if claim_entry.claim_inference_kind != "observed_per_puzzle":
                raise ValueError(
                    "per-puzzle claim_posture entries must use observed_per_puzzle inference kind"
                )

        seen_pattern_ids: set[str] = set()
        for pattern_entry in self.cross_puzzle_pattern_entries:
            if pattern_entry.pattern_id in seen_pattern_ids:
                raise ValueError(
                    "cross_puzzle_pattern_entries must not contain duplicate pattern_id values"
                )
            seen_pattern_ids.add(pattern_entry.pattern_id)
            for puzzle_id in pattern_entry.support_puzzle_ids:
                if puzzle_id not in self.canonical_puzzle_order:
                    raise ValueError(
                        "cross_puzzle_pattern_entries support_puzzle_ids must be canonical "
                        "puzzle IDs"
                    )
            expected_support_order = [
                puzzle_id
                for puzzle_id in self.canonical_puzzle_order
                if puzzle_id in set(pattern_entry.support_puzzle_ids)
            ]
            if expected_support_order != pattern_entry.support_puzzle_ids:
                raise ValueError(
                    "cross_puzzle_pattern_entries support_puzzle_ids must preserve canonical order"
                )

            expected_support_refs = sorted(
                _puzzle_behavior_entry_ref(puzzle_id)
                for puzzle_id in pattern_entry.support_puzzle_ids
            )
            if pattern_entry.support_behavior_entry_refs != expected_support_refs:
                raise ValueError(
                    "cross_puzzle_pattern_entries support_behavior_entry_refs must match "
                    "support_puzzle_ids over per-puzzle behavior surfaces"
                )
            if pattern_entry.support_posture == "supported_all_three":
                if pattern_entry.support_puzzle_ids != self.canonical_puzzle_order:
                    raise ValueError(
                        "supported_all_three posture requires support for all canonical puzzle IDs"
                    )
            elif len(pattern_entry.support_puzzle_ids) >= _EXPECTED_PUZZLE_COUNT:
                raise ValueError(
                    "supported_subset posture must not claim support across all three puzzles"
                )

            if pattern_entry.pattern_claim_posture not in claim_entries_by_id:
                raise ValueError(
                    "cross_puzzle_pattern_entries pattern_claim_posture must reference "
                    "claim_posture_register claim_id values"
                )
            pattern_claim = claim_entries_by_id[pattern_entry.pattern_claim_posture]
            expected_claim_target = _cross_pattern_claim_target(pattern_entry.pattern_id)
            if pattern_claim.claim_target_ref != expected_claim_target:
                raise ValueError(
                    "cross-puzzle pattern claims must target matching cross_pattern surface"
                )
            if pattern_claim.claim_inference_kind != "inferred_cross_puzzle":
                raise ValueError(
                    "cross-puzzle pattern claims must use inferred_cross_puzzle inference kind"
                )
            if (
                self.cross_puzzle_config_consistency_posture == "explicit_divergence_declared"
                and pattern_entry.support_posture == "supported_all_three"
                and "config_divergence" not in pattern_claim.limitation_scope
            ):
                raise ValueError(
                    "cross-puzzle synthesis over explicit config divergence requires "
                    "config_divergence limitation_scope"
                )

        for failure_mode_entry in self.failure_mode_catalog:
            if failure_mode_entry.claim_posture not in claim_entries_by_id:
                raise ValueError(
                    "failure_mode_catalog claim_posture values must reference "
                    "claim_posture_register claim_id values"
                )

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("behavior_evidence_bundle_id", None)
        expected_id = compute_adeu_arc_behavior_evidence_bundle_id(payload_without_id)
        if self.behavior_evidence_bundle_id != expected_id:
            raise ValueError(
                "behavior_evidence_bundle_id must match canonical full payload hash identity"
            )
        return self


def compute_adeu_arc_behavior_evidence_bundle_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_BEHAVIOR_EVIDENCE_BUNDLE_SCHEMA)
    canonical_payload.pop("behavior_evidence_bundle_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_behavior_bundle_{digest[:32]}"


def canonicalize_adeu_arc_behavior_evidence_bundle_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return AdeuArcBehaviorEvidenceBundle.model_validate(payload).model_dump(mode="json")


def materialize_adeu_arc_behavior_evidence_bundle_payload(
    payload_without_bundle_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_bundle_id)
    payload.setdefault("schema", ADEU_ARC_BEHAVIOR_EVIDENCE_BUNDLE_SCHEMA)
    payload["behavior_evidence_bundle_id"] = compute_adeu_arc_behavior_evidence_bundle_id(payload)
    return canonicalize_adeu_arc_behavior_evidence_bundle_payload(payload)


def derive_v42g4_arc_behavior_evidence_bundle(
    *,
    three_puzzle_harness_record: dict[str, Any],
    per_puzzle_behavior_inputs: list[dict[str, Any]],
    cross_puzzle_pattern_entries: list[dict[str, Any]],
    failure_mode_catalog: list[dict[str, Any]],
    claim_posture_register: list[dict[str, Any]],
    authority_boundary_register: dict[str, Any],
    deterministic_replay_scope_note: str,
    behavior_summary: str,
    evidence_refs: list[str],
) -> dict[str, Any]:
    harness_record = AdeuArcThreePuzzleHarnessRecord.model_validate(three_puzzle_harness_record)
    if len(per_puzzle_behavior_inputs) != _EXPECTED_PUZZLE_COUNT:
        raise ValueError(
            "per_puzzle_behavior_inputs must contain exactly three canonical puzzle entries"
        )

    behavior_inputs_by_puzzle: dict[str, dict[str, Any]] = {}
    for entry in per_puzzle_behavior_inputs:
        puzzle_id = _assert_non_empty_text(entry["puzzle_id"], field_name="puzzle_id")
        if puzzle_id in behavior_inputs_by_puzzle:
            raise ValueError(
                "per_puzzle_behavior_inputs must not contain duplicate puzzle_id values"
            )
        behavior_inputs_by_puzzle[puzzle_id] = entry

    harness_entries_by_puzzle = {
        entry.puzzle_id: entry for entry in harness_record.puzzle_run_entries
    }
    per_puzzle_behavior_entries: list[dict[str, Any]] = []
    for puzzle_index, puzzle_id in enumerate(harness_record.canonical_puzzle_order, start=1):
        if puzzle_id not in behavior_inputs_by_puzzle:
            raise ValueError(
                "per_puzzle_behavior_inputs must provide one entry for each canonical puzzle_id"
            )
        behavior_input = behavior_inputs_by_puzzle[puzzle_id]
        harness_entry = harness_entries_by_puzzle[puzzle_id]

        if behavior_input["reasoning_run_record_ref"] != harness_entry.reasoning_run_record_ref:
            raise ValueError(
                "per_puzzle_behavior_inputs reasoning_run_record_ref must match harness entry"
            )
        if behavior_input["local_eval_ref"] != harness_entry.local_eval_ref:
            raise ValueError("per_puzzle_behavior_inputs local_eval_ref must match harness entry")
        if behavior_input.get("scorecard_manifest_ref") != harness_entry.scorecard_manifest_ref:
            raise ValueError(
                "per_puzzle_behavior_inputs scorecard_manifest_ref must match harness entry"
            )
        if (
            behavior_input.get("submission_execution_record_ref")
            != harness_entry.submission_execution_record_ref
        ):
            raise ValueError(
                "per_puzzle_behavior_inputs submission_execution_record_ref must match "
                "harness entry"
            )

        per_puzzle_behavior_entries.append(
            {
                "puzzle_index": puzzle_index,
                "puzzle_id": puzzle_id,
                "reasoning_run_record_ref": behavior_input["reasoning_run_record_ref"],
                "local_eval_ref": behavior_input["local_eval_ref"],
                "scorecard_manifest_ref": behavior_input.get("scorecard_manifest_ref"),
                "submission_execution_record_ref": behavior_input.get(
                    "submission_execution_record_ref"
                ),
                "behavior_signal_refs": behavior_input["behavior_signal_refs"],
                "mapped_failure_mode_ids": behavior_input["mapped_failure_mode_ids"],
                "claim_posture": behavior_input["claim_posture"],
            }
        )

    payload_without_id = {
        "schema": ADEU_ARC_BEHAVIOR_EVIDENCE_BUNDLE_SCHEMA,
        "harness_record_id": harness_record.three_puzzle_harness_record_id,
        "harness_run_id": harness_record.harness_run_id,
        "puzzle_input_bundle_id": harness_record.puzzle_input_bundle_id,
        "selection_register_id": harness_record.selection_register_id,
        "selection_register_hash": harness_record.selection_register_hash,
        "selected_puzzle_ids": harness_record.selected_puzzle_ids,
        "canonical_puzzle_order": harness_record.canonical_puzzle_order,
        "per_puzzle_behavior_entries": per_puzzle_behavior_entries,
        "cross_puzzle_pattern_entries": deepcopy(cross_puzzle_pattern_entries),
        "failure_mode_catalog": deepcopy(failure_mode_catalog),
        "claim_posture_register": deepcopy(claim_posture_register),
        "authority_boundary_register": deepcopy(authority_boundary_register),
        "cross_puzzle_config_consistency_posture": harness_record.config_consistency_posture,
        "deterministic_replay_scope_note": deterministic_replay_scope_note,
        "behavior_summary": behavior_summary,
        "evidence_refs": deepcopy(evidence_refs),
    }
    return materialize_adeu_arc_behavior_evidence_bundle_payload(payload_without_id)
