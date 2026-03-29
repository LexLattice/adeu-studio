from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .puzzle_input_bundle import AdeuArcPuzzleInputBundle

ADEU_ARC_REASONING_RUN_RECORD_SCHEMA = "adeu_arc_reasoning_run_record@1"
V42G2_V96_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS96.md#v96-continuation-contract-machine-checkable"
)

ReasoningEffort = Literal["low", "medium", "high", "xhigh"]
ReasoningEffortSourceKind = Literal["requested_only", "provider_observed"]
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
BranchingPosture = Literal["no_branching", "branching_observed"]
BranchingVisibilityStatus = Literal["not_applicable", "typed_visible"]
EmissionStage = Literal[
    "task_packet",
    "observation_frame",
    "hypothesis_frame",
    "action_proposal",
    "rollout_trace",
]

_EMISSION_STAGE_ORDER: dict[EmissionStage, int] = {
    "task_packet": 1,
    "observation_frame": 2,
    "hypothesis_frame": 3,
    "action_proposal": 4,
    "rollout_trace": 5,
}
_REQUIRED_STAGES: tuple[EmissionStage, ...] = (
    "task_packet",
    "observation_frame",
    "hypothesis_frame",
    "action_proposal",
)
_STATUS_EXACT_MAX_STAGE: dict[RunExecutionStatus, int | None] = {
    "started": 0,
    "failed_before_task_packet": 0,
    "task_emitted": 1,
    "observation_emitted": 2,
    "hypothesis_emitted": 3,
    "action_emitted": 4,
    "rollout_emitted": 5,
    "blocked_or_deferred": 4,
    "completed": None,
}
_FORBIDDEN_AUTHORITY_TERMS: tuple[str, ...] = (
    "leaderboard_ready",
    "competition_success_authority",
    "official_authority_granted",
    "universal_necessity",
    "deterministic_fresh_model_reexecution",
    "post_hoc_reconstruction",
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


def compute_adeu_arc_reasoning_identity_chain(
    *,
    run_id: str,
    puzzle_input_bundle_id: str,
    selection_register_id: str,
    puzzle_input_id: str,
    puzzle_id: str,
    environment_ref: str,
    session_ref: str,
    competition_scope_ref: str,
) -> str:
    return (
        f"{run_id}|{puzzle_input_bundle_id}|{selection_register_id}|"
        f"{puzzle_input_id}|{puzzle_id}|{environment_ref}|{session_ref}|"
        f"{competition_scope_ref}"
    )


def compute_adeu_arc_run_config_hash(
    *,
    model_id: str,
    agent_profile_ref: str,
    run_config_ref: str,
    prompt_profile_ref: str | None,
    reasoning_effort_requested: ReasoningEffort,
    reasoning_effort_observed: ReasoningEffort,
    reasoning_effort_source_kind: ReasoningEffortSourceKind,
) -> str:
    return sha256_canonical_json(
        {
            "model_id": model_id,
            "agent_profile_ref": agent_profile_ref,
            "run_config_ref": run_config_ref,
            "prompt_profile_ref": prompt_profile_ref,
            "reasoning_effort_requested": reasoning_effort_requested,
            "reasoning_effort_observed": reasoning_effort_observed,
            "reasoning_effort_source_kind": reasoning_effort_source_kind,
        }
    )


class ArcRunSettlementPostureCarry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    ambiguity_posture_preserved: bool = True
    claim_posture_preserved: bool = True
    necessity_laundering_detected: bool = False
    summary: str

    @model_validator(mode="after")
    def _validate_settlement(self) -> ArcRunSettlementPostureCarry:
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        _assert_no_forbidden_terms(
            value=self.summary,
            field_name="summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )
        if self.necessity_laundering_detected:
            raise ValueError("necessity_laundering_detected must be false for v42g2 records")
        return self


class ArcEmissionSequenceEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    stage: EmissionStage
    sequence_index: int = Field(ge=0)
    evidence_ref: str

    @model_validator(mode="after")
    def _validate_entry(self) -> ArcEmissionSequenceEntry:
        object.__setattr__(
            self,
            "evidence_ref",
            _assert_non_empty_text(self.evidence_ref, field_name="evidence_ref"),
        )
        return self


class AdeuArcReasoningRunRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_REASONING_RUN_RECORD_SCHEMA] = ADEU_ARC_REASONING_RUN_RECORD_SCHEMA
    reasoning_run_record_id: str
    run_id: str
    puzzle_input_bundle_id: str
    selection_register_id: str
    puzzle_input_id: str
    puzzle_id: str
    environment_ref: str
    session_ref: str
    competition_scope_ref: str
    model_id: str
    agent_profile_ref: str
    run_config_ref: str
    run_config_hash: str
    prompt_profile_ref: str | None = None
    reasoning_effort_requested: ReasoningEffort
    reasoning_effort_observed: ReasoningEffort
    reasoning_effort_source_kind: ReasoningEffortSourceKind
    task_packet_ref: str
    observation_frame_ref: str
    hypothesis_frame_ref: str
    action_proposal_ref: str
    rollout_trace_ref: str | None = None
    task_packet_emission_evidence_refs: list[str] = Field(min_length=1)
    observation_frame_emission_evidence_refs: list[str] = Field(min_length=1)
    hypothesis_frame_emission_evidence_refs: list[str] = Field(min_length=1)
    action_proposal_emission_evidence_refs: list[str] = Field(min_length=1)
    rollout_trace_emission_evidence_refs: list[str] = Field(default_factory=list)
    emission_sequence_register: list[ArcEmissionSequenceEntry] = Field(min_length=1)
    run_execution_status: RunExecutionStatus
    run_terminal_posture: RunTerminalPosture
    rollout_presence_posture: RolloutPresencePosture
    branching_posture: BranchingPosture
    branching_visibility_status: BranchingVisibilityStatus
    branch_event_refs: list[str] = Field(default_factory=list)
    settlement_posture_carry: ArcRunSettlementPostureCarry
    run_summary: str
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_record(self) -> AdeuArcReasoningRunRecord:
        text_fields = (
            "reasoning_run_record_id",
            "run_id",
            "puzzle_input_bundle_id",
            "selection_register_id",
            "puzzle_input_id",
            "puzzle_id",
            "environment_ref",
            "session_ref",
            "competition_scope_ref",
            "model_id",
            "agent_profile_ref",
            "run_config_ref",
            "task_packet_ref",
            "observation_frame_ref",
            "hypothesis_frame_ref",
            "action_proposal_ref",
            "run_summary",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )

        if self.prompt_profile_ref is not None:
            object.__setattr__(
                self,
                "prompt_profile_ref",
                _assert_non_empty_text(self.prompt_profile_ref, field_name="prompt_profile_ref"),
            )

        object.__setattr__(
            self,
            "run_config_hash",
            _assert_hash(self.run_config_hash, field_name="run_config_hash"),
        )
        expected_run_config_hash = compute_adeu_arc_run_config_hash(
            model_id=self.model_id,
            agent_profile_ref=self.agent_profile_ref,
            run_config_ref=self.run_config_ref,
            prompt_profile_ref=self.prompt_profile_ref,
            reasoning_effort_requested=self.reasoning_effort_requested,
            reasoning_effort_observed=self.reasoning_effort_observed,
            reasoning_effort_source_kind=self.reasoning_effort_source_kind,
        )
        if self.run_config_hash != expected_run_config_hash:
            raise ValueError(
                "run_config_hash must match canonical model/profile/config/reasoning tuple"
            )

        if self.reasoning_effort_source_kind == "requested_only":
            if self.reasoning_effort_observed != self.reasoning_effort_requested:
                raise ValueError(
                    "reasoning_effort_observed must equal reasoning_effort_requested when "
                    "reasoning_effort_source_kind=requested_only"
                )

        if self.rollout_trace_ref is not None:
            object.__setattr__(
                self,
                "rollout_trace_ref",
                _assert_non_empty_text(self.rollout_trace_ref, field_name="rollout_trace_ref"),
            )

        object.__setattr__(
            self,
            "task_packet_emission_evidence_refs",
            _assert_sorted_unique(
                self.task_packet_emission_evidence_refs,
                field_name="task_packet_emission_evidence_refs",
            ),
        )
        object.__setattr__(
            self,
            "observation_frame_emission_evidence_refs",
            _assert_sorted_unique(
                self.observation_frame_emission_evidence_refs,
                field_name="observation_frame_emission_evidence_refs",
            ),
        )
        object.__setattr__(
            self,
            "hypothesis_frame_emission_evidence_refs",
            _assert_sorted_unique(
                self.hypothesis_frame_emission_evidence_refs,
                field_name="hypothesis_frame_emission_evidence_refs",
            ),
        )
        object.__setattr__(
            self,
            "action_proposal_emission_evidence_refs",
            _assert_sorted_unique(
                self.action_proposal_emission_evidence_refs,
                field_name="action_proposal_emission_evidence_refs",
            ),
        )
        object.__setattr__(
            self,
            "rollout_trace_emission_evidence_refs",
            _assert_sorted_unique(
                self.rollout_trace_emission_evidence_refs,
                field_name="rollout_trace_emission_evidence_refs",
            ),
        )
        object.__setattr__(
            self,
            "branch_event_refs",
            _assert_sorted_unique(self.branch_event_refs, field_name="branch_event_refs"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )

        expected_identity_chain = compute_adeu_arc_reasoning_identity_chain(
            run_id=self.run_id,
            puzzle_input_bundle_id=self.puzzle_input_bundle_id,
            selection_register_id=self.selection_register_id,
            puzzle_input_id=self.puzzle_input_id,
            puzzle_id=self.puzzle_id,
            environment_ref=self.environment_ref,
            session_ref=self.session_ref,
            competition_scope_ref=self.competition_scope_ref,
        )
        expected_identity_chain_ref = f"identity_chain:{expected_identity_chain}"
        if expected_identity_chain_ref not in self.evidence_refs:
            raise ValueError(
                "evidence_refs must include identity_chain evidence bound to run/puzzle/"
                "environment/session/competition refs"
            )

        stage_to_refs: dict[EmissionStage, list[str]] = {
            "task_packet": self.task_packet_emission_evidence_refs,
            "observation_frame": self.observation_frame_emission_evidence_refs,
            "hypothesis_frame": self.hypothesis_frame_emission_evidence_refs,
            "action_proposal": self.action_proposal_emission_evidence_refs,
            "rollout_trace": self.rollout_trace_emission_evidence_refs,
        }
        all_stage_and_branch_refs = (
            self.task_packet_emission_evidence_refs
            + self.observation_frame_emission_evidence_refs
            + self.hypothesis_frame_emission_evidence_refs
            + self.action_proposal_emission_evidence_refs
            + self.rollout_trace_emission_evidence_refs
            + self.branch_event_refs
        )
        for ref in all_stage_and_branch_refs:
            if not ref.endswith(expected_identity_chain):
                raise ValueError(
                    "stage and branch evidence refs must bind to the same identity chain"
                )

        sequence_indexes: list[int] = []
        stage_first_index: dict[EmissionStage, int] = {}
        stage_sequence_refs: dict[EmissionStage, list[str]] = {stage: [] for stage in stage_to_refs}
        for entry in self.emission_sequence_register:
            sequence_indexes.append(entry.sequence_index)
            stage_sequence_refs[entry.stage].append(entry.evidence_ref)
            stage_first_index.setdefault(entry.stage, entry.sequence_index)
            if entry.evidence_ref not in stage_to_refs[entry.stage]:
                raise ValueError(
                    "emission_sequence_register evidence refs must be listed in "
                    "the corresponding per-stage evidence register"
                )
            if not entry.evidence_ref.endswith(expected_identity_chain):
                raise ValueError(
                    "emission_sequence_register evidence refs must bind to identity chain"
                )

        if len(sequence_indexes) != len(set(sequence_indexes)):
            raise ValueError("emission_sequence_register sequence_index values must be unique")
        if sequence_indexes != sorted(sequence_indexes):
            raise ValueError("emission_sequence_register sequence_index values must be monotonic")

        for stage, refs in stage_to_refs.items():
            sequence_ref_set = set(stage_sequence_refs[stage])
            stage_ref_set = set(refs)
            if len(stage_sequence_refs[stage]) != len(refs) or sequence_ref_set != stage_ref_set:
                raise ValueError(
                    "emission_sequence_register must include each per-stage evidence ref "
                    "exactly once"
                )

        for required_stage in _REQUIRED_STAGES:
            if not stage_sequence_refs[required_stage]:
                raise ValueError(
                    "emission_sequence_register must include all required non-rollout stages"
                )
        for required_stage in _REQUIRED_STAGES[1:]:
            previous_stage = _REQUIRED_STAGES[_REQUIRED_STAGES.index(required_stage) - 1]
            if stage_first_index[required_stage] <= stage_first_index[previous_stage]:
                raise ValueError(
                    "emission_sequence_register required stages must follow canonical stage order"
                )
        previous_stage_order = 0
        for entry in self.emission_sequence_register:
            stage_order = _EMISSION_STAGE_ORDER[entry.stage]
            if stage_order < previous_stage_order:
                raise ValueError("emission_sequence_register stage order must be non-regressing")
            previous_stage_order = stage_order

        if self.rollout_presence_posture == "rollout_present":
            if self.rollout_trace_ref is None:
                raise ValueError("rollout_present posture requires rollout_trace_ref")
            if not self.rollout_trace_emission_evidence_refs:
                raise ValueError(
                    "rollout_present posture requires rollout_trace_emission_evidence_refs"
                )
            if not stage_sequence_refs["rollout_trace"]:
                raise ValueError("rollout_present posture requires rollout_trace stage evidence")
            if stage_first_index["rollout_trace"] <= stage_first_index["action_proposal"]:
                raise ValueError(
                    "rollout_trace stage evidence must occur after action_proposal stage evidence"
                )
        else:
            if self.rollout_trace_ref is not None:
                raise ValueError("rollout_absent posture forbids rollout_trace_ref")
            if self.rollout_trace_emission_evidence_refs:
                raise ValueError(
                    "rollout_absent posture forbids rollout_trace_emission_evidence_refs"
                )
            if stage_sequence_refs["rollout_trace"]:
                raise ValueError("rollout_absent posture forbids rollout_trace stage evidence")

        max_stage_order = max(
            _EMISSION_STAGE_ORDER[entry.stage] for entry in self.emission_sequence_register
        )
        expected_exact_stage = _STATUS_EXACT_MAX_STAGE[self.run_execution_status]
        if expected_exact_stage is None:
            if max_stage_order not in (4, 5):
                raise ValueError(
                    "run_execution_status=completed requires action/rollout stage occupation"
                )
        elif max_stage_order != expected_exact_stage:
            raise ValueError("run_execution_status is inconsistent with staged emission occupation")

        if self.run_terminal_posture == "completed_with_rollout":
            if self.rollout_presence_posture != "rollout_present":
                raise ValueError(
                    "completed_with_rollout terminal posture requires rollout_presence_posture="
                    "rollout_present"
                )
            if self.run_execution_status not in ("rollout_emitted", "completed"):
                raise ValueError(
                    "completed_with_rollout terminal posture requires rollout-emitted/completed "
                    "execution status"
                )
        elif self.run_terminal_posture == "completed_without_rollout":
            if self.rollout_presence_posture != "rollout_absent":
                raise ValueError(
                    "completed_without_rollout terminal posture requires rollout_presence_posture="
                    "rollout_absent"
                )
            if self.run_execution_status not in ("action_emitted", "completed"):
                raise ValueError(
                    "completed_without_rollout terminal posture requires action-emitted/completed "
                    "execution status"
                )
        elif self.run_terminal_posture == "blocked_or_deferred":
            if self.rollout_presence_posture != "rollout_absent":
                raise ValueError(
                    "blocked_or_deferred terminal posture requires rollout_presence_posture="
                    "rollout_absent"
                )
            if self.run_execution_status != "blocked_or_deferred":
                raise ValueError(
                    "blocked_or_deferred terminal posture requires run_execution_status="
                    "blocked_or_deferred"
                )
        else:
            if self.run_execution_status == "completed":
                raise ValueError(
                    "failed terminal posture may not use run_execution_status=completed"
                )

        if self.run_execution_status == "rollout_emitted":
            if self.rollout_presence_posture != "rollout_present":
                raise ValueError(
                    "run_execution_status=rollout_emitted requires rollout_presence_posture="
                    "rollout_present"
                )
        if self.run_execution_status == "blocked_or_deferred":
            if self.rollout_presence_posture != "rollout_absent":
                raise ValueError(
                    "run_execution_status=blocked_or_deferred requires rollout_presence_posture="
                    "rollout_absent"
                )

        if self.branching_posture == "no_branching":
            if self.branching_visibility_status != "not_applicable":
                raise ValueError(
                    "no_branching posture requires branching_visibility_status=not_applicable"
                )
            if self.branch_event_refs:
                raise ValueError("no_branching posture forbids branch_event_refs")
        else:
            if self.branching_visibility_status != "typed_visible":
                raise ValueError(
                    "branching_observed posture requires branching_visibility_status=typed_visible"
                )
            if not self.branch_event_refs:
                raise ValueError("branching_observed posture requires branch_event_refs")

        _assert_no_forbidden_terms(
            value=self.run_summary,
            field_name="run_summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )

        payload_without_id = self.model_dump(mode="json", exclude_none=False)
        payload_without_id.pop("reasoning_run_record_id", None)
        expected_id = compute_adeu_arc_reasoning_run_record_id(payload_without_id)
        if self.reasoning_run_record_id != expected_id:
            raise ValueError(
                "reasoning_run_record_id must match canonical full payload hash identity"
            )
        return self


def compute_adeu_arc_reasoning_run_record_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_REASONING_RUN_RECORD_SCHEMA)
    canonical_payload.pop("reasoning_run_record_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_run_{digest[:32]}"


def canonicalize_adeu_arc_reasoning_run_record_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcReasoningRunRecord.model_validate(payload).model_dump(
        mode="json", exclude_none=False
    )


def materialize_adeu_arc_reasoning_run_record_payload(
    payload_without_reasoning_run_record_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_reasoning_run_record_id)
    payload.setdefault("schema", ADEU_ARC_REASONING_RUN_RECORD_SCHEMA)
    payload.setdefault("rollout_trace_emission_evidence_refs", [])
    payload.setdefault("branch_event_refs", [])
    payload["reasoning_run_record_id"] = compute_adeu_arc_reasoning_run_record_id(payload)
    return canonicalize_adeu_arc_reasoning_run_record_payload(payload)


def derive_v42g2_arc_reasoning_run_record(
    *,
    puzzle_input_bundle: dict[str, Any],
    selected_puzzle_id: str,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    observation_frame: dict[str, Any],
    observation_frame_ref: str,
    hypothesis_frame: dict[str, Any],
    hypothesis_frame_ref: str,
    action_proposal: dict[str, Any],
    action_proposal_ref: str,
    rollout_trace: dict[str, Any] | None,
    rollout_trace_ref: str | None,
    environment_ref: str,
    session_ref: str,
    competition_scope_ref: str,
    model_id: str,
    run_id: str,
    agent_profile_ref: str,
    run_config_ref: str,
    prompt_profile_ref: str | None,
    reasoning_effort_requested: ReasoningEffort,
    reasoning_effort_observed: ReasoningEffort,
    reasoning_effort_source_kind: ReasoningEffortSourceKind,
    task_packet_emission_evidence_refs: list[str],
    observation_frame_emission_evidence_refs: list[str],
    hypothesis_frame_emission_evidence_refs: list[str],
    action_proposal_emission_evidence_refs: list[str],
    rollout_trace_emission_evidence_refs: list[str],
    emission_sequence_register: list[dict[str, Any]],
    run_execution_status: RunExecutionStatus,
    run_terminal_posture: RunTerminalPosture,
    rollout_presence_posture: RolloutPresencePosture,
    branching_posture: BranchingPosture,
    branching_visibility_status: BranchingVisibilityStatus,
    branch_event_refs: list[str],
    settlement_posture_carry: dict[str, Any],
    run_summary: str,
    evidence_refs: list[str],
) -> dict[str, Any]:
    validated_bundle = AdeuArcPuzzleInputBundle.model_validate(puzzle_input_bundle)
    selected_entry = next(
        (
            entry
            for entry in validated_bundle.puzzle_entries
            if entry.puzzle_id == selected_puzzle_id
        ),
        None,
    )
    if selected_entry is None:
        raise ValueError("selected_puzzle_id must exist in released puzzle_input_bundle entries")

    task_packet_id = task_packet["task_packet_id"]
    if observation_frame["task_packet_id"] != task_packet_id:
        raise ValueError("observation_frame must bind to released task_packet_id")
    if hypothesis_frame["task_packet_id"] != task_packet_id:
        raise ValueError("hypothesis_frame must bind to released task_packet_id")
    if action_proposal["task_packet_id"] != task_packet_id:
        raise ValueError("action_proposal must bind to released task_packet_id")

    if observation_frame["task_packet_ref"] != task_packet_ref:
        raise ValueError("observation_frame must preserve released task_packet_ref")
    if hypothesis_frame["task_packet_ref"] != task_packet_ref:
        raise ValueError("hypothesis_frame must preserve released task_packet_ref")
    if hypothesis_frame["observation_frame_ref"] != observation_frame_ref:
        raise ValueError("hypothesis_frame must preserve released observation_frame_ref")
    if action_proposal["task_packet_ref"] != task_packet_ref:
        raise ValueError("action_proposal must preserve released task_packet_ref")
    if action_proposal["observation_frame_ref"] != observation_frame_ref:
        raise ValueError("action_proposal must preserve released observation_frame_ref")
    if action_proposal["hypothesis_frame_ref"] != hypothesis_frame_ref:
        raise ValueError("action_proposal must preserve released hypothesis_frame_ref")

    if rollout_presence_posture == "rollout_present":
        if rollout_trace is None or rollout_trace_ref is None:
            raise ValueError("rollout_present posture requires rollout_trace and rollout_trace_ref")
        if rollout_trace["task_packet_id"] != task_packet_id:
            raise ValueError("rollout_trace must bind to released task_packet_id")
        if rollout_trace["task_packet_ref"] != task_packet_ref:
            raise ValueError("rollout_trace must preserve released task_packet_ref")
        for step in rollout_trace.get("rollout_steps", []):
            if step["action_proposal_ref"] != action_proposal_ref:
                raise ValueError("rollout_steps must preserve released action_proposal_ref")
    else:
        if rollout_trace is not None or rollout_trace_ref is not None:
            raise ValueError("rollout_absent posture forbids rollout_trace inputs")

    payload_without_id: dict[str, Any] = {
        "schema": ADEU_ARC_REASONING_RUN_RECORD_SCHEMA,
        "run_id": run_id,
        "puzzle_input_bundle_id": validated_bundle.puzzle_input_bundle_id,
        "selection_register_id": validated_bundle.selection_register_id,
        "puzzle_input_id": selected_entry.puzzle_input_id,
        "puzzle_id": selected_entry.puzzle_id,
        "environment_ref": environment_ref,
        "session_ref": session_ref,
        "competition_scope_ref": competition_scope_ref,
        "model_id": model_id,
        "agent_profile_ref": agent_profile_ref,
        "run_config_ref": run_config_ref,
        "run_config_hash": compute_adeu_arc_run_config_hash(
            model_id=model_id,
            agent_profile_ref=agent_profile_ref,
            run_config_ref=run_config_ref,
            prompt_profile_ref=prompt_profile_ref,
            reasoning_effort_requested=reasoning_effort_requested,
            reasoning_effort_observed=reasoning_effort_observed,
            reasoning_effort_source_kind=reasoning_effort_source_kind,
        ),
        "prompt_profile_ref": prompt_profile_ref,
        "reasoning_effort_requested": reasoning_effort_requested,
        "reasoning_effort_observed": reasoning_effort_observed,
        "reasoning_effort_source_kind": reasoning_effort_source_kind,
        "task_packet_ref": task_packet_ref,
        "observation_frame_ref": observation_frame_ref,
        "hypothesis_frame_ref": hypothesis_frame_ref,
        "action_proposal_ref": action_proposal_ref,
        "rollout_trace_ref": rollout_trace_ref,
        "task_packet_emission_evidence_refs": deepcopy(task_packet_emission_evidence_refs),
        "observation_frame_emission_evidence_refs": deepcopy(
            observation_frame_emission_evidence_refs
        ),
        "hypothesis_frame_emission_evidence_refs": deepcopy(
            hypothesis_frame_emission_evidence_refs
        ),
        "action_proposal_emission_evidence_refs": deepcopy(action_proposal_emission_evidence_refs),
        "rollout_trace_emission_evidence_refs": deepcopy(rollout_trace_emission_evidence_refs),
        "emission_sequence_register": deepcopy(emission_sequence_register),
        "run_execution_status": run_execution_status,
        "run_terminal_posture": run_terminal_posture,
        "rollout_presence_posture": rollout_presence_posture,
        "branching_posture": branching_posture,
        "branching_visibility_status": branching_visibility_status,
        "branch_event_refs": deepcopy(branch_event_refs),
        "settlement_posture_carry": deepcopy(settlement_posture_carry),
        "run_summary": run_summary,
        "evidence_refs": deepcopy(evidence_refs),
    }
    return materialize_adeu_arc_reasoning_run_record_payload(payload_without_id)
