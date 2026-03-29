from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .puzzle_input_bundle import AdeuArcPuzzleInputBundle
from .reasoning_run_record import AdeuArcReasoningRunRecord

ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA = "adeu_arc_three_puzzle_harness_record@1"
V42G3_V97_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS97.md#v97-continuation-contract-machine-checkable"
)

ReasoningEffort = Literal["low", "medium", "high", "xhigh"]
RunExecutionStatus = Literal[
    "started",
    "failed_before_task_packet",
    "task_emitted",
    "observation_emitted",
    "hypothesis_emitted",
    "action_emitted",
    "rollout_emitted",
    "blocked_or_deferred",
    "completed",
]
RunTerminalPosture = Literal[
    "completed_with_rollout",
    "completed_without_rollout",
    "blocked_or_deferred",
    "failed",
]
RolloutPresencePosture = Literal["rollout_present", "rollout_absent"]
ScorecardPresencePosture = Literal["scorecard_present", "scorecard_absent_deferred"]
SubmissionPresencePosture = Literal["submission_present", "submission_absent_deferred"]
ConfigConsistencyPosture = Literal[
    "uniform_across_all_puzzles",
    "explicit_divergence_declared",
]
HarnessExecutionStatus = Literal[
    "in_progress",
    "completed",
    "completed_with_failures",
    "invalid",
]

_EXPECTED_PUZZLE_COUNT = 3
_FORBIDDEN_AUTHORITY_TERMS: tuple[str, ...] = (
    "leaderboard_ready",
    "competition_success_authority",
    "official_authority_granted",
    "universal_necessity",
    "deterministic_fresh_model_reexecution",
)
_TERMINAL_OR_BLOCKED_RUN_STATUSES: set[RunExecutionStatus] = {
    "action_emitted",
    "rollout_emitted",
    "blocked_or_deferred",
    "completed",
}


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


def compute_adeu_arc_harness_local_eval_aggregate_ref(*, local_eval_refs: list[str]) -> str:
    digest = sha256_canonical_json({"local_eval_refs": local_eval_refs})
    return f"aggregate:local_eval:{digest[:32]}"


def compute_adeu_arc_harness_scorecard_aggregate_ref(*, scorecard_refs: list[str]) -> str:
    digest = sha256_canonical_json({"scorecard_refs": scorecard_refs})
    return f"aggregate:scorecard:{digest[:32]}"


def compute_adeu_arc_harness_submission_aggregate_ref(*, submission_refs: list[str]) -> str:
    digest = sha256_canonical_json({"submission_refs": submission_refs})
    return f"aggregate:submission:{digest[:32]}"


class ArcHarnessSequenceEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    sequence_step: int = Field(ge=1)
    puzzle_index: int = Field(ge=1, le=_EXPECTED_PUZZLE_COUNT)
    puzzle_id: str
    run_id: str
    sequence_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> ArcHarnessSequenceEntry:
        object.__setattr__(
            self,
            "puzzle_id",
            _assert_non_empty_text(self.puzzle_id, field_name="puzzle_id"),
        )
        object.__setattr__(self, "run_id", _assert_non_empty_text(self.run_id, field_name="run_id"))
        object.__setattr__(
            self,
            "sequence_evidence_refs",
            _assert_sorted_unique(
                self.sequence_evidence_refs,
                field_name="sequence_evidence_refs",
            ),
        )
        return self


class AdeuArcThreePuzzleHarnessRunEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    puzzle_index: int = Field(ge=1, le=_EXPECTED_PUZZLE_COUNT)
    puzzle_input_id: str
    puzzle_id: str
    run_id: str
    reasoning_run_record_ref: str
    run_execution_status: RunExecutionStatus
    run_terminal_posture: RunTerminalPosture
    rollout_presence_posture: RolloutPresencePosture
    model_id: str
    agent_profile_ref: str
    run_config_ref: str
    run_config_hash: str
    prompt_profile_ref: str | None = None
    reasoning_effort_observed: ReasoningEffort
    stage_evidence_ref_set: list[str] = Field(min_length=1)
    local_eval_ref: str
    scorecard_manifest_ref: str | None = None
    scorecard_presence_posture: ScorecardPresencePosture
    submission_execution_record_ref: str | None = None
    submission_presence_posture: SubmissionPresencePosture

    @model_validator(mode="after")
    def _validate_entry(self) -> AdeuArcThreePuzzleHarnessRunEntry:
        text_fields = (
            "puzzle_input_id",
            "puzzle_id",
            "run_id",
            "reasoning_run_record_ref",
            "model_id",
            "agent_profile_ref",
            "run_config_ref",
            "local_eval_ref",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )

        object.__setattr__(
            self,
            "run_config_hash",
            _assert_hash(self.run_config_hash, field_name="run_config_hash"),
        )
        object.__setattr__(
            self,
            "stage_evidence_ref_set",
            _assert_sorted_unique(
                self.stage_evidence_ref_set,
                field_name="stage_evidence_ref_set",
            ),
        )

        if self.prompt_profile_ref is not None:
            object.__setattr__(
                self,
                "prompt_profile_ref",
                _assert_non_empty_text(
                    self.prompt_profile_ref,
                    field_name="prompt_profile_ref",
                ),
            )

        if self.scorecard_presence_posture == "scorecard_present":
            if self.scorecard_manifest_ref is None:
                raise ValueError(
                    "scorecard_presence_posture=scorecard_present requires scorecard_manifest_ref"
                )
            object.__setattr__(
                self,
                "scorecard_manifest_ref",
                _assert_non_empty_text(
                    self.scorecard_manifest_ref,
                    field_name="scorecard_manifest_ref",
                ),
            )
        elif self.scorecard_manifest_ref is not None:
            raise ValueError(
                "scorecard_presence_posture=scorecard_absent_deferred forbids "
                "scorecard_manifest_ref"
            )

        if self.submission_presence_posture == "submission_present":
            if self.submission_execution_record_ref is None:
                raise ValueError(
                    "submission_presence_posture=submission_present requires "
                    "submission_execution_record_ref"
                )
            object.__setattr__(
                self,
                "submission_execution_record_ref",
                _assert_non_empty_text(
                    self.submission_execution_record_ref,
                    field_name="submission_execution_record_ref",
                ),
            )
        elif self.submission_execution_record_ref is not None:
            raise ValueError(
                "submission_presence_posture=submission_absent_deferred forbids "
                "submission_execution_record_ref"
            )
        return self


class AdeuArcThreePuzzleHarnessRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[
        ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA
    ] = ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA
    three_puzzle_harness_record_id: str
    harness_run_id: str
    expected_puzzle_count: int = _EXPECTED_PUZZLE_COUNT
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
    harness_execution_status: HarnessExecutionStatus
    puzzle_run_entries: list[AdeuArcThreePuzzleHarnessRunEntry] = Field(
        min_length=_EXPECTED_PUZZLE_COUNT,
        max_length=_EXPECTED_PUZZLE_COUNT,
    )
    harness_sequence_register: str
    harness_sequence_entries: list[ArcHarnessSequenceEntry] = Field(
        min_length=_EXPECTED_PUZZLE_COUNT,
        max_length=_EXPECTED_PUZZLE_COUNT,
    )
    agent_profile_ref: str
    run_config_ref: str
    run_config_hash: str
    prompt_profile_ref: str | None = None
    config_consistency_posture: ConfigConsistencyPosture
    aggregated_local_eval_ref: str | None = None
    aggregated_scorecard_posture_ref: str | None = None
    aggregated_submission_posture_ref: str | None = None
    run_summary: str
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_record(self) -> AdeuArcThreePuzzleHarnessRecord:
        text_fields = (
            "three_puzzle_harness_record_id",
            "harness_run_id",
            "puzzle_input_bundle_id",
            "selection_register_id",
            "harness_sequence_register",
            "agent_profile_ref",
            "run_config_ref",
            "run_summary",
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
            "run_config_hash",
            _assert_hash(self.run_config_hash, field_name="run_config_hash"),
        )
        if self.prompt_profile_ref is not None:
            object.__setattr__(
                self,
                "prompt_profile_ref",
                _assert_non_empty_text(self.prompt_profile_ref, field_name="prompt_profile_ref"),
            )

        if self.expected_puzzle_count != _EXPECTED_PUZZLE_COUNT:
            raise ValueError(
                f"expected_puzzle_count must equal {_EXPECTED_PUZZLE_COUNT} in v42g3"
            )
        object.__setattr__(
            self,
            "selected_puzzle_ids",
            _assert_unique_preserving_order(
                self.selected_puzzle_ids,
                field_name="selected_puzzle_ids",
            ),
        )
        object.__setattr__(
            self,
            "canonical_puzzle_order",
            _assert_unique_preserving_order(
                self.canonical_puzzle_order,
                field_name="canonical_puzzle_order",
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

        ordered_entries = self.puzzle_run_entries
        by_index: dict[int, AdeuArcThreePuzzleHarnessRunEntry] = {}
        seen_run_ids: set[str] = set()
        seen_puzzle_input_ids: set[str] = set()
        for expected_index, entry in enumerate(ordered_entries, start=1):
            if entry.puzzle_index != expected_index:
                raise ValueError(
                    "puzzle_run_entries must be in canonical puzzle_index order with no gaps"
                )
            if entry.puzzle_id != self.canonical_puzzle_order[expected_index - 1]:
                raise ValueError(
                    "puzzle_run_entries puzzle_id order must follow canonical_puzzle_order"
                )
            if entry.run_id in seen_run_ids:
                raise ValueError("puzzle_run_entries must not contain duplicate run_id values")
            seen_run_ids.add(entry.run_id)
            if entry.puzzle_input_id in seen_puzzle_input_ids:
                raise ValueError(
                    "puzzle_run_entries must not contain duplicate puzzle_input_id values"
                )
            seen_puzzle_input_ids.add(entry.puzzle_input_id)
            by_index[entry.puzzle_index] = entry

        entry_config_tuples = [
            (
                entry.agent_profile_ref,
                entry.run_config_ref,
                entry.run_config_hash,
                entry.prompt_profile_ref,
            )
            for entry in ordered_entries
        ]
        top_level_config = (
            self.agent_profile_ref,
            self.run_config_ref,
            self.run_config_hash,
            self.prompt_profile_ref,
        )
        if self.config_consistency_posture == "uniform_across_all_puzzles":
            if any(entry_tuple != top_level_config for entry_tuple in entry_config_tuples):
                raise ValueError(
                    "uniform config_consistency_posture requires all puzzle entries to match "
                    "top-level agent/config identity"
                )
        else:
            has_divergence = any(
                entry_tuple != top_level_config for entry_tuple in entry_config_tuples
            )
            if not has_divergence:
                raise ValueError(
                    "explicit_divergence_declared posture requires at least one puzzle entry "
                    "to diverge from top-level agent/config identity"
                )
            if "evidence:config_divergence_declared" not in self.evidence_refs:
                raise ValueError(
                    "explicit_divergence_declared posture requires "
                    "'evidence:config_divergence_declared' in evidence_refs"
                )

        run_statuses = [entry.run_execution_status for entry in ordered_entries]
        if self.harness_execution_status == "completed":
            if not all(status in _TERMINAL_OR_BLOCKED_RUN_STATUSES for status in run_statuses):
                raise ValueError(
                    "harness_execution_status=completed requires each puzzle run to be terminal "
                    "or blocked/deferred"
                )
        elif self.harness_execution_status == "completed_with_failures":
            if all(status in _TERMINAL_OR_BLOCKED_RUN_STATUSES for status in run_statuses):
                raise ValueError(
                    "completed_with_failures requires at least one non-terminal "
                    "run_execution_status"
                )
        elif self.harness_execution_status == "in_progress":
            if all(status in _TERMINAL_OR_BLOCKED_RUN_STATUSES for status in run_statuses):
                raise ValueError(
                    "in_progress requires at least one non-terminal run_execution_status"
                )

        sequence_steps = [entry.sequence_step for entry in self.harness_sequence_entries]
        if sequence_steps != [1, 2, 3]:
            raise ValueError(
                "harness_sequence_entries sequence_step values must be exactly [1,2,3]"
            )
        if [entry.puzzle_index for entry in self.harness_sequence_entries] != [1, 2, 3]:
            raise ValueError("harness_sequence_entries puzzle_index values must be exactly [1,2,3]")
        for sequence_entry in self.harness_sequence_entries:
            run_entry = by_index[sequence_entry.puzzle_index]
            if sequence_entry.puzzle_id != run_entry.puzzle_id:
                raise ValueError(
                    "harness_sequence_entries puzzle_id values must match puzzle_run_entries by "
                    "puzzle_index"
                )
            if sequence_entry.run_id != run_entry.run_id:
                raise ValueError(
                    "harness_sequence_entries run_id values must match puzzle_run_entries by "
                    "puzzle_index"
                )

        local_eval_refs = [entry.local_eval_ref for entry in ordered_entries]
        if self.aggregated_local_eval_ref is not None:
            object.__setattr__(
                self,
                "aggregated_local_eval_ref",
                _assert_non_empty_text(
                    self.aggregated_local_eval_ref,
                    field_name="aggregated_local_eval_ref",
                ),
            )
            expected_local_aggregate = compute_adeu_arc_harness_local_eval_aggregate_ref(
                local_eval_refs=sorted(local_eval_refs)
            )
            if self.aggregated_local_eval_ref != expected_local_aggregate:
                raise ValueError(
                    "aggregated_local_eval_ref must match canonical aggregate over per-puzzle "
                    "local_eval_ref values"
                )

        scorecard_refs = [
            entry.scorecard_manifest_ref
            for entry in ordered_entries
            if entry.scorecard_manifest_ref is not None
        ]
        if self.aggregated_scorecard_posture_ref is not None:
            if not scorecard_refs:
                raise ValueError(
                    "aggregated_scorecard_posture_ref requires at least one scorecard_manifest_ref"
                )
            object.__setattr__(
                self,
                "aggregated_scorecard_posture_ref",
                _assert_non_empty_text(
                    self.aggregated_scorecard_posture_ref,
                    field_name="aggregated_scorecard_posture_ref",
                ),
            )
            expected_scorecard_aggregate = compute_adeu_arc_harness_scorecard_aggregate_ref(
                scorecard_refs=sorted(scorecard_refs)
            )
            if self.aggregated_scorecard_posture_ref != expected_scorecard_aggregate:
                raise ValueError(
                    "aggregated_scorecard_posture_ref must match canonical aggregate over "
                    "per-puzzle scorecard refs"
                )

        submission_refs = [
            entry.submission_execution_record_ref
            for entry in ordered_entries
            if entry.submission_execution_record_ref is not None
        ]
        if self.aggregated_submission_posture_ref is not None:
            if not submission_refs:
                raise ValueError(
                    "aggregated_submission_posture_ref requires at least one "
                    "submission_execution_record_ref"
                )
            object.__setattr__(
                self,
                "aggregated_submission_posture_ref",
                _assert_non_empty_text(
                    self.aggregated_submission_posture_ref,
                    field_name="aggregated_submission_posture_ref",
                ),
            )
            expected_submission_aggregate = compute_adeu_arc_harness_submission_aggregate_ref(
                submission_refs=sorted(submission_refs)
            )
            if self.aggregated_submission_posture_ref != expected_submission_aggregate:
                raise ValueError(
                    "aggregated_submission_posture_ref must match canonical aggregate over "
                    "per-puzzle submission refs"
                )

        _assert_no_forbidden_terms(
            value=self.run_summary,
            field_name="run_summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )

        payload_without_id = self.model_dump(mode="json", exclude_none=False)
        payload_without_id.pop("three_puzzle_harness_record_id", None)
        expected_id = compute_adeu_arc_three_puzzle_harness_record_id(payload_without_id)
        if self.three_puzzle_harness_record_id != expected_id:
            raise ValueError(
                "three_puzzle_harness_record_id must match canonical full payload hash identity"
            )
        return self


def compute_adeu_arc_three_puzzle_harness_record_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA)
    canonical_payload.pop("three_puzzle_harness_record_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_harness_{digest[:32]}"


def canonicalize_adeu_arc_three_puzzle_harness_record_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return AdeuArcThreePuzzleHarnessRecord.model_validate(payload).model_dump(
        mode="json", exclude_none=False
    )


def materialize_adeu_arc_three_puzzle_harness_record_payload(
    payload_without_harness_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_harness_id)
    payload.setdefault("schema", ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA)
    payload["three_puzzle_harness_record_id"] = compute_adeu_arc_three_puzzle_harness_record_id(
        payload
    )
    return canonicalize_adeu_arc_three_puzzle_harness_record_payload(payload)


def derive_v42g3_arc_three_puzzle_harness_record(
    *,
    puzzle_input_bundle: dict[str, Any],
    harness_run_id: str,
    harness_execution_status: HarnessExecutionStatus,
    harness_sequence_register: str,
    config_consistency_posture: ConfigConsistencyPosture,
    puzzle_run_inputs: list[dict[str, Any]],
    run_summary: str,
    evidence_refs: list[str],
    aggregated_local_eval_ref: str | None = None,
    aggregated_scorecard_posture_ref: str | None = None,
    aggregated_submission_posture_ref: str | None = None,
) -> dict[str, Any]:
    validated_bundle = AdeuArcPuzzleInputBundle.model_validate(puzzle_input_bundle)
    if len(puzzle_run_inputs) != _EXPECTED_PUZZLE_COUNT:
        raise ValueError("puzzle_run_inputs must contain exactly three puzzle run definitions")

    bundle_entries_by_puzzle_id = {
        entry.puzzle_id: entry for entry in validated_bundle.puzzle_entries
    }
    run_inputs_by_puzzle_id: dict[str, dict[str, Any]] = {}
    shared_runtime_identity: tuple[str, str, str] | None = None
    for run_input in puzzle_run_inputs:
        run_record = AdeuArcReasoningRunRecord.model_validate(run_input["reasoning_run_record"])
        runtime_identity = (
            run_record.environment_ref,
            run_record.session_ref,
            run_record.competition_scope_ref,
        )
        if shared_runtime_identity is None:
            shared_runtime_identity = runtime_identity
        elif runtime_identity != shared_runtime_identity:
            raise ValueError(
                "puzzle_run_inputs reasoning runs must share environment_ref, session_ref, "
                "and competition_scope_ref across the harness"
            )
        puzzle_id = run_record.puzzle_id
        if puzzle_id in run_inputs_by_puzzle_id:
            raise ValueError("puzzle_run_inputs must not contain duplicate puzzle_id entries")
        run_inputs_by_puzzle_id[puzzle_id] = {"run_record": run_record, "input": run_input}

    puzzle_run_entries: list[dict[str, Any]] = []
    harness_sequence_entries: list[dict[str, Any]] = []
    for index, puzzle_id in enumerate(validated_bundle.canonical_puzzle_order, start=1):
        if puzzle_id not in run_inputs_by_puzzle_id:
            raise ValueError(
                "puzzle_run_inputs must provide one reasoning run for each canonical selected "
                "puzzle_id"
            )
        bundle_entry = bundle_entries_by_puzzle_id[puzzle_id]
        run_record = run_inputs_by_puzzle_id[puzzle_id]["run_record"]
        run_input = run_inputs_by_puzzle_id[puzzle_id]["input"]

        if run_record.puzzle_input_bundle_id != validated_bundle.puzzle_input_bundle_id:
            raise ValueError("reasoning run records must bind to the released puzzle_input_bundle")
        if run_record.selection_register_id != validated_bundle.selection_register_id:
            raise ValueError(
                "reasoning run records must bind to the released selection_register_id"
            )
        if run_record.puzzle_input_id != bundle_entry.puzzle_input_id:
            raise ValueError("reasoning run records must bind to canonical puzzle_input_id")

        expected_stage_evidence_ref_set_raw = (
            run_record.task_packet_emission_evidence_refs
            + run_record.observation_frame_emission_evidence_refs
            + run_record.hypothesis_frame_emission_evidence_refs
            + run_record.action_proposal_emission_evidence_refs
            + run_record.rollout_trace_emission_evidence_refs
        )
        expected_stage_evidence_ref_set = [
            _assert_non_empty_text(ref, field_name="stage_evidence_ref_set")
            for ref in expected_stage_evidence_ref_set_raw
        ]
        if len(expected_stage_evidence_ref_set) != len(set(expected_stage_evidence_ref_set)):
            raise ValueError(
                "reasoning run records must not repeat stage evidence refs across occupied stages"
            )
        expected_stage_evidence_ref_set = sorted(expected_stage_evidence_ref_set)
        if not expected_stage_evidence_ref_set:
            raise ValueError(
                "reasoning run records must provide non-empty stage evidence for each harness entry"
            )

        stage_evidence_ref_set_source = run_input.get("stage_evidence_ref_set")
        if stage_evidence_ref_set_source is None:
            stage_evidence_ref_set = expected_stage_evidence_ref_set
        else:
            if not isinstance(stage_evidence_ref_set_source, list):
                raise ValueError("stage_evidence_ref_set must be a list when explicitly provided")
            stage_evidence_ref_set = _assert_sorted_unique(
                stage_evidence_ref_set_source,
                field_name="stage_evidence_ref_set",
            )
            if stage_evidence_ref_set != expected_stage_evidence_ref_set:
                raise ValueError(
                    "stage_evidence_ref_set must exactly match stage evidence derived from "
                    "reasoning_run_record"
                )
        sequence_evidence_refs = sorted(
            {
                _assert_non_empty_text(
                    sequence_entry.evidence_ref, field_name="sequence_evidence_refs"
                )
                for sequence_entry in run_record.emission_sequence_register
            }
        )
        puzzle_run_entries.append(
            {
                "puzzle_index": index,
                "puzzle_input_id": run_record.puzzle_input_id,
                "puzzle_id": run_record.puzzle_id,
                "run_id": run_record.run_id,
                "reasoning_run_record_ref": run_input["reasoning_run_record_ref"],
                "run_execution_status": run_record.run_execution_status,
                "run_terminal_posture": run_record.run_terminal_posture,
                "rollout_presence_posture": run_record.rollout_presence_posture,
                "model_id": run_record.model_id,
                "agent_profile_ref": run_record.agent_profile_ref,
                "run_config_ref": run_record.run_config_ref,
                "run_config_hash": run_record.run_config_hash,
                "prompt_profile_ref": run_record.prompt_profile_ref,
                "reasoning_effort_observed": run_record.reasoning_effort_observed,
                "stage_evidence_ref_set": stage_evidence_ref_set,
                "local_eval_ref": run_input["local_eval_ref"],
                "scorecard_manifest_ref": run_input.get("scorecard_manifest_ref"),
                "scorecard_presence_posture": run_input["scorecard_presence_posture"],
                "submission_execution_record_ref": run_input.get(
                    "submission_execution_record_ref"
                ),
                "submission_presence_posture": run_input["submission_presence_posture"],
            }
        )
        harness_sequence_entries.append(
            {
                "sequence_step": index,
                "puzzle_index": index,
                "puzzle_id": run_record.puzzle_id,
                "run_id": run_record.run_id,
                "sequence_evidence_refs": sequence_evidence_refs,
            }
        )

    first_entry = puzzle_run_entries[0]
    if aggregated_local_eval_ref is None:
        aggregated_local_eval_ref = compute_adeu_arc_harness_local_eval_aggregate_ref(
            local_eval_refs=sorted(entry["local_eval_ref"] for entry in puzzle_run_entries)
        )

    scorecard_refs = sorted(
        entry["scorecard_manifest_ref"]
        for entry in puzzle_run_entries
        if entry["scorecard_manifest_ref"] is not None
    )
    if aggregated_scorecard_posture_ref is None and scorecard_refs:
        aggregated_scorecard_posture_ref = compute_adeu_arc_harness_scorecard_aggregate_ref(
            scorecard_refs=scorecard_refs
        )

    submission_refs = sorted(
        entry["submission_execution_record_ref"]
        for entry in puzzle_run_entries
        if entry["submission_execution_record_ref"] is not None
    )
    if aggregated_submission_posture_ref is None and submission_refs:
        aggregated_submission_posture_ref = compute_adeu_arc_harness_submission_aggregate_ref(
            submission_refs=submission_refs
        )

    payload_without_id = {
        "schema": ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA,
        "harness_run_id": harness_run_id,
        "expected_puzzle_count": _EXPECTED_PUZZLE_COUNT,
        "puzzle_input_bundle_id": validated_bundle.puzzle_input_bundle_id,
        "selection_register_id": validated_bundle.selection_register_id,
        "selection_register_hash": validated_bundle.selection_register_hash,
        "selected_puzzle_ids": validated_bundle.selected_puzzle_ids,
        "canonical_puzzle_order": validated_bundle.canonical_puzzle_order,
        "harness_execution_status": harness_execution_status,
        "puzzle_run_entries": puzzle_run_entries,
        "harness_sequence_register": harness_sequence_register,
        "harness_sequence_entries": harness_sequence_entries,
        "agent_profile_ref": first_entry["agent_profile_ref"],
        "run_config_ref": first_entry["run_config_ref"],
        "run_config_hash": first_entry["run_config_hash"],
        "prompt_profile_ref": first_entry["prompt_profile_ref"],
        "config_consistency_posture": config_consistency_posture,
        "aggregated_local_eval_ref": aggregated_local_eval_ref,
        "aggregated_scorecard_posture_ref": aggregated_scorecard_posture_ref,
        "aggregated_submission_posture_ref": aggregated_submission_posture_ref,
        "run_summary": run_summary,
        "evidence_refs": deepcopy(evidence_refs),
    }
    return materialize_adeu_arc_three_puzzle_harness_record_payload(payload_without_id)
