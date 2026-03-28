from __future__ import annotations

import re
from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

ADEU_ARC_ACTION_PROPOSAL_SCHEMA = "adeu_arc_action_proposal@1"
ADEU_ARC_ROLLOUT_TRACE_SCHEMA = "adeu_arc_rollout_trace@1"
V42C_V91_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS91.md#v42c_arc_action_rollout_contract@1"
)

ArcProposalStatus = Literal[
    "admissible_candidate",
    "blocked",
    "deferred_pending_resolution",
]
ProposalDeonticAdmissibility = Literal["allowed", "deferred", "forbidden"]
ProposalUtilityPosture = Literal[
    "progress_seeking",
    "ambiguity_reducing",
    "discriminative_probe",
    "conservative_low_risk",
    "bounded_search_pressure",
]
HypothesisEffect = Literal["strengthen", "weaken", "unchanged"]
RolloutTerminalStatus = Literal["completed", "blocked", "stopped"]
RolloutStopReason = Literal[
    "none",
    "deontic_blocked",
    "deferred_pending_resolution",
    "expectation_mismatch_stop",
    "manual_stop",
]
ExpectationComparisonPosture = Literal[
    "matched",
    "partially_matched",
    "mismatched",
    "not_evaluated",
]

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_FORBIDDEN_SCORECARD_TERMS: tuple[str, ...] = (
    "scorecard",
    "leaderboard",
    "competition mode",
    "online submission",
    "replay authority",
)
_FORBIDDEN_NECESSITY_TERMS: tuple[str, ...] = (
    "universal necessity",
    "always must",
    "proves the rule",
    "all solutions must",
)


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
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


def _assert_sha256_hex(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name).lower()
    if not _SHA256_RE.fullmatch(normalized):
        raise ValueError(f"{field_name} must be a lowercase sha256 hex digest")
    return normalized


def _assert_no_forbidden_terms(*, value: str, field_name: str, terms: tuple[str, ...]) -> None:
    lowered = value.lower()
    for term in terms:
        if term in lowered:
            raise ValueError(f"{field_name} may not contain forbidden term '{term}'")


def _compute_expectation_surface_hash(payload: dict[str, Any]) -> str:
    return sha256_canonical_json(payload)


class ArcAlternativeActionRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    action_id: str
    action_kind: str
    rationale: str
    deontic_class: ProposalDeonticAdmissibility

    @model_validator(mode="after")
    def _validate_alternative(self) -> ArcAlternativeActionRecord:
        object.__setattr__(
            self, "action_id", _assert_non_empty_text(self.action_id, field_name="action_id")
        )
        object.__setattr__(
            self,
            "action_kind",
            _assert_non_empty_text(self.action_kind, field_name="action_kind"),
        )
        object.__setattr__(
            self, "rationale", _assert_non_empty_text(self.rationale, field_name="rationale")
        )
        _assert_no_forbidden_terms(
            value=self.rationale,
            field_name="rationale",
            terms=_FORBIDDEN_SCORECARD_TERMS,
        )
        return self


class ArcExpectedStateDelta(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    delta_id: str
    summary: str
    expected_cell_ref_hash: str

    @model_validator(mode="after")
    def _validate_delta(self) -> ArcExpectedStateDelta:
        object.__setattr__(
            self, "delta_id", _assert_non_empty_text(self.delta_id, field_name="delta_id")
        )
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        _assert_no_forbidden_terms(
            value=self.summary,
            field_name="summary",
            terms=_FORBIDDEN_SCORECARD_TERMS,
        )
        object.__setattr__(
            self,
            "expected_cell_ref_hash",
            _assert_sha256_hex(
                self.expected_cell_ref_hash,
                field_name="expected_cell_ref_hash",
            ),
        )
        return self


class ArcExpectedHypothesisEffect(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    hypothesis_id: str
    expected_effect: HypothesisEffect
    rationale: str

    @model_validator(mode="after")
    def _validate_effect(self) -> ArcExpectedHypothesisEffect:
        object.__setattr__(
            self,
            "hypothesis_id",
            _assert_non_empty_text(self.hypothesis_id, field_name="hypothesis_id"),
        )
        object.__setattr__(
            self, "rationale", _assert_non_empty_text(self.rationale, field_name="rationale")
        )
        _assert_no_forbidden_terms(
            value=self.rationale,
            field_name="rationale",
            terms=_FORBIDDEN_SCORECARD_TERMS,
        )
        return self


class ArcExpectedFalsificationCondition(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    condition_id: str
    summary: str
    falsifies_hypothesis_ids: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_condition(self) -> ArcExpectedFalsificationCondition:
        object.__setattr__(
            self,
            "condition_id",
            _assert_non_empty_text(self.condition_id, field_name="condition_id"),
        )
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        _assert_no_forbidden_terms(
            value=self.summary,
            field_name="summary",
            terms=_FORBIDDEN_SCORECARD_TERMS,
        )
        object.__setattr__(
            self,
            "falsifies_hypothesis_ids",
            _assert_sorted_unique(
                self.falsifies_hypothesis_ids,
                field_name="falsifies_hypothesis_ids",
            ),
        )
        return self


class AdeuArcActionProposal(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_ACTION_PROPOSAL_SCHEMA] = ADEU_ARC_ACTION_PROPOSAL_SCHEMA
    action_proposal_id: str
    task_packet_id: str
    task_packet_ref: str
    observation_frame_id: str
    observation_frame_ref: str
    hypothesis_frame_id: str
    hypothesis_frame_ref: str
    proposal_step_index: int = Field(ge=0)
    proposal_status: ArcProposalStatus
    proposed_action_kind: str | None = None
    proposed_action_payload: dict[str, Any] | None = None
    proposal_deontic_admissibility: ProposalDeonticAdmissibility
    proposal_decision_basis: str
    hypothesis_selection_basis: str
    utility_pressure_basis: str
    ambiguity_handling_basis: str
    proposal_utility_posture: ProposalUtilityPosture
    supporting_hypothesis_refs: list[str] = Field(min_length=1)
    alternative_action_register: list[ArcAlternativeActionRecord] = Field(min_length=1)
    expected_state_delta: list[ArcExpectedStateDelta]
    expected_hypothesis_effects: list[ArcExpectedHypothesisEffect]
    expected_falsification_conditions: list[ArcExpectedFalsificationCondition]
    expected_ambiguity_effects: list[str]
    expected_outcome_summary: str
    expected_outcome_refs: list[str] = Field(min_length=1)
    expectation_surface_hash: str

    @model_validator(mode="after")
    def _validate_proposal(self) -> AdeuArcActionProposal:
        object.__setattr__(
            self,
            "action_proposal_id",
            _assert_non_empty_text(self.action_proposal_id, field_name="action_proposal_id"),
        )
        object.__setattr__(
            self,
            "task_packet_id",
            _assert_non_empty_text(self.task_packet_id, field_name="task_packet_id"),
        )
        object.__setattr__(
            self,
            "task_packet_ref",
            _assert_non_empty_text(self.task_packet_ref, field_name="task_packet_ref"),
        )
        object.__setattr__(
            self,
            "observation_frame_id",
            _assert_non_empty_text(self.observation_frame_id, field_name="observation_frame_id"),
        )
        object.__setattr__(
            self,
            "observation_frame_ref",
            _assert_non_empty_text(
                self.observation_frame_ref,
                field_name="observation_frame_ref",
            ),
        )
        object.__setattr__(
            self,
            "hypothesis_frame_id",
            _assert_non_empty_text(self.hypothesis_frame_id, field_name="hypothesis_frame_id"),
        )
        object.__setattr__(
            self,
            "hypothesis_frame_ref",
            _assert_non_empty_text(
                self.hypothesis_frame_ref,
                field_name="hypothesis_frame_ref",
            ),
        )
        object.__setattr__(
            self,
            "proposal_decision_basis",
            _assert_non_empty_text(
                self.proposal_decision_basis,
                field_name="proposal_decision_basis",
            ),
        )
        object.__setattr__(
            self,
            "hypothesis_selection_basis",
            _assert_non_empty_text(
                self.hypothesis_selection_basis,
                field_name="hypothesis_selection_basis",
            ),
        )
        object.__setattr__(
            self,
            "utility_pressure_basis",
            _assert_non_empty_text(
                self.utility_pressure_basis,
                field_name="utility_pressure_basis",
            ),
        )
        object.__setattr__(
            self,
            "ambiguity_handling_basis",
            _assert_non_empty_text(
                self.ambiguity_handling_basis,
                field_name="ambiguity_handling_basis",
            ),
        )
        object.__setattr__(
            self,
            "supporting_hypothesis_refs",
            _assert_sorted_unique(
                self.supporting_hypothesis_refs,
                field_name="supporting_hypothesis_refs",
            ),
        )
        object.__setattr__(
            self,
            "expected_ambiguity_effects",
            _assert_sorted_unique(
                self.expected_ambiguity_effects,
                field_name="expected_ambiguity_effects",
            ),
        )
        object.__setattr__(
            self,
            "expected_outcome_summary",
            _assert_non_empty_text(
                self.expected_outcome_summary,
                field_name="expected_outcome_summary",
            ),
        )
        object.__setattr__(
            self,
            "expected_outcome_refs",
            _assert_sorted_unique(
                self.expected_outcome_refs,
                field_name="expected_outcome_refs",
            ),
        )
        object.__setattr__(
            self,
            "expectation_surface_hash",
            _assert_sha256_hex(
                self.expectation_surface_hash,
                field_name="expectation_surface_hash",
            ),
        )

        textual_fields = (
            self.proposal_decision_basis,
            self.hypothesis_selection_basis,
            self.utility_pressure_basis,
            self.ambiguity_handling_basis,
            self.expected_outcome_summary,
        )
        for field_value in textual_fields:
            _assert_no_forbidden_terms(
                value=field_value,
                field_name="proposal textual fields",
                terms=_FORBIDDEN_SCORECARD_TERMS,
            )

        if self.proposal_status == "admissible_candidate":
            if not self.proposed_action_kind:
                raise ValueError("admissible_candidate proposals must include proposed_action_kind")
            if self.proposed_action_payload is None:
                raise ValueError(
                    "admissible_candidate proposals must include proposed_action_payload"
                )
            if self.proposal_deontic_admissibility != "allowed":
                raise ValueError(
                    "admissible_candidate proposals must use proposal_deontic_admissibility=allowed"
                )
        else:
            if self.proposed_action_kind is not None or self.proposed_action_payload is not None:
                raise ValueError(
                    "blocked/deferred proposals may not emit committed proposed_action fields"
                )
            if (
                self.proposal_status == "blocked"
                and self.proposal_deontic_admissibility != "forbidden"
            ):
                raise ValueError(
                    "blocked proposal_status requires proposal_deontic_admissibility=forbidden"
                )
            if (
                self.proposal_status == "deferred_pending_resolution"
                and self.proposal_deontic_admissibility != "deferred"
            ):
                raise ValueError(
                    "deferred_pending_resolution requires proposal_deontic_admissibility=deferred"
                )

        alternative_ids = [entry.action_id for entry in self.alternative_action_register]
        if alternative_ids != sorted(alternative_ids):
            raise ValueError("alternative_action_register must be sorted by action_id")
        if len(alternative_ids) != len(set(alternative_ids)):
            raise ValueError("alternative_action_register must use unique action_id values")

        expectation_surface = expectation_surface_payload_for_proposal(
            self.model_dump(mode="json", exclude_none=False)
        )
        expected_hash = _compute_expectation_surface_hash(expectation_surface)
        if self.expectation_surface_hash != expected_hash:
            raise ValueError(
                "expectation_surface_hash must match canonical structured expectation surface"
            )

        payload_without_id = self.model_dump(mode="json", exclude_none=False)
        payload_without_id.pop("action_proposal_id", None)
        expected_id = compute_adeu_arc_action_proposal_id(payload_without_id)
        if self.action_proposal_id != expected_id:
            raise ValueError("action_proposal_id must match canonical full payload hash identity")
        return self


class ArcRolloutStep(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    step_index: int = Field(ge=0)
    action_proposal_ref: str
    pre_step_state_ref: str
    post_step_state_ref: str
    observed_outcome_refs: list[str] = Field(min_length=1)
    observed_outcome_summary: str

    @model_validator(mode="after")
    def _validate_step(self) -> ArcRolloutStep:
        object.__setattr__(
            self,
            "action_proposal_ref",
            _assert_non_empty_text(self.action_proposal_ref, field_name="action_proposal_ref"),
        )
        object.__setattr__(
            self,
            "pre_step_state_ref",
            _assert_non_empty_text(self.pre_step_state_ref, field_name="pre_step_state_ref"),
        )
        object.__setattr__(
            self,
            "post_step_state_ref",
            _assert_non_empty_text(self.post_step_state_ref, field_name="post_step_state_ref"),
        )
        object.__setattr__(
            self,
            "observed_outcome_refs",
            _assert_sorted_unique(
                self.observed_outcome_refs,
                field_name="observed_outcome_refs",
            ),
        )
        object.__setattr__(
            self,
            "observed_outcome_summary",
            _assert_non_empty_text(
                self.observed_outcome_summary,
                field_name="observed_outcome_summary",
            ),
        )
        _assert_no_forbidden_terms(
            value=self.observed_outcome_summary,
            field_name="observed_outcome_summary",
            terms=_FORBIDDEN_SCORECARD_TERMS,
        )
        return self


class ArcOutcomeHypothesisEffect(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    hypothesis_id: str
    observed_effect: HypothesisEffect
    rationale: str

    @model_validator(mode="after")
    def _validate_outcome(self) -> ArcOutcomeHypothesisEffect:
        object.__setattr__(
            self,
            "hypothesis_id",
            _assert_non_empty_text(self.hypothesis_id, field_name="hypothesis_id"),
        )
        object.__setattr__(
            self, "rationale", _assert_non_empty_text(self.rationale, field_name="rationale")
        )
        _assert_no_forbidden_terms(
            value=self.rationale,
            field_name="rationale",
            terms=_FORBIDDEN_SCORECARD_TERMS + _FORBIDDEN_NECESSITY_TERMS,
        )
        return self


class ArcExpectationOutcomeComparison(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    comparison_posture: ExpectationComparisonPosture
    comparison_summary: str
    unmet_expectation_refs: list[str]
    proposal_expectation_surface_hash: str
    matched_by_hash: bool = True

    @model_validator(mode="after")
    def _validate_comparison(self) -> ArcExpectationOutcomeComparison:
        object.__setattr__(
            self,
            "comparison_summary",
            _assert_non_empty_text(self.comparison_summary, field_name="comparison_summary"),
        )
        object.__setattr__(
            self,
            "unmet_expectation_refs",
            _assert_sorted_unique(
                self.unmet_expectation_refs,
                field_name="unmet_expectation_refs",
            ),
        )
        object.__setattr__(
            self,
            "proposal_expectation_surface_hash",
            _assert_sha256_hex(
                self.proposal_expectation_surface_hash,
                field_name="proposal_expectation_surface_hash",
            ),
        )
        _assert_no_forbidden_terms(
            value=self.comparison_summary,
            field_name="comparison_summary",
            terms=_FORBIDDEN_NECESSITY_TERMS,
        )
        return self


class ArcSettlementPostureCarry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    ambiguity_posture_preserved: bool = True
    claim_posture_preserved: bool = True
    necessity_laundering_detected: bool = False
    summary: str

    @model_validator(mode="after")
    def _validate_carry(self) -> ArcSettlementPostureCarry:
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        if self.necessity_laundering_detected:
            raise ValueError(
                "settlement_posture_carry may not report necessity_laundering_detected=true"
            )
        return self


class AdeuArcRolloutTrace(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_ROLLOUT_TRACE_SCHEMA] = ADEU_ARC_ROLLOUT_TRACE_SCHEMA
    rollout_trace_id: str
    task_packet_id: str
    task_packet_ref: str
    rollout_steps: list[ArcRolloutStep] = Field(min_length=1)
    pre_step_state_refs: list[str] = Field(min_length=1)
    post_step_state_refs: list[str] = Field(min_length=1)
    terminal_rollout_status: RolloutTerminalStatus
    rollout_stop_reason: RolloutStopReason
    outcome_hypothesis_effects: list[ArcOutcomeHypothesisEffect]
    expectation_surface_ref: str
    expectation_surface_hash: str
    expectation_outcome_comparison: ArcExpectationOutcomeComparison
    settlement_posture_carry: ArcSettlementPostureCarry

    @model_validator(mode="after")
    def _validate_trace(self) -> AdeuArcRolloutTrace:
        object.__setattr__(
            self,
            "rollout_trace_id",
            _assert_non_empty_text(self.rollout_trace_id, field_name="rollout_trace_id"),
        )
        object.__setattr__(
            self,
            "task_packet_id",
            _assert_non_empty_text(self.task_packet_id, field_name="task_packet_id"),
        )
        object.__setattr__(
            self,
            "task_packet_ref",
            _assert_non_empty_text(self.task_packet_ref, field_name="task_packet_ref"),
        )
        object.__setattr__(
            self,
            "expectation_surface_ref",
            _assert_non_empty_text(
                self.expectation_surface_ref,
                field_name="expectation_surface_ref",
            ),
        )
        object.__setattr__(
            self,
            "expectation_surface_hash",
            _assert_sha256_hex(
                self.expectation_surface_hash,
                field_name="expectation_surface_hash",
            ),
        )
        object.__setattr__(
            self,
            "pre_step_state_refs",
            [
                _assert_non_empty_text(value, field_name="pre_step_state_refs")
                for value in self.pre_step_state_refs
            ],
        )
        object.__setattr__(
            self,
            "post_step_state_refs",
            [
                _assert_non_empty_text(value, field_name="post_step_state_refs")
                for value in self.post_step_state_refs
            ],
        )

        indices = [step.step_index for step in self.rollout_steps]
        if indices != list(range(len(self.rollout_steps))):
            raise ValueError("rollout_steps must use deterministic contiguous step_index ordering")

        expected_pre_refs = [step.pre_step_state_ref for step in self.rollout_steps]
        expected_post_refs = [step.post_step_state_ref for step in self.rollout_steps]
        if self.pre_step_state_refs != expected_pre_refs:
            raise ValueError(
                "pre_step_state_refs must match ordered rollout_steps pre_step_state_ref"
            )
        if self.post_step_state_refs != expected_post_refs:
            raise ValueError(
                "post_step_state_refs must match ordered rollout_steps post_step_state_ref"
            )

        if self.terminal_rollout_status == "completed":
            if self.rollout_stop_reason != "none":
                raise ValueError(
                    "terminal_rollout_status=completed requires rollout_stop_reason=none"
                )
            if self.expectation_outcome_comparison.comparison_posture == "not_evaluated":
                raise ValueError(
                    "completed rollout traces must include evaluated expectation_outcome_comparison"
                )
        elif self.rollout_stop_reason == "none":
            raise ValueError("non-completed rollout traces may not use rollout_stop_reason=none")

        if (
            self.expectation_outcome_comparison.proposal_expectation_surface_hash
            != self.expectation_surface_hash
        ):
            raise ValueError(
                "expectation surface hash mismatch between rollout trace and proposal lineage"
            )
        if not self.expectation_outcome_comparison.matched_by_hash:
            raise ValueError(
                "expectation_outcome_comparison must preserve byte-identical expectation surface"
            )

        payload_without_id = self.model_dump(mode="json", exclude_none=False)
        payload_without_id.pop("rollout_trace_id", None)
        expected_id = compute_adeu_arc_rollout_trace_id(payload_without_id)
        if self.rollout_trace_id != expected_id:
            raise ValueError("rollout_trace_id must match canonical full payload hash identity")
        return self


def expectation_surface_payload_for_proposal(proposal_payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "expected_state_delta": deepcopy(proposal_payload["expected_state_delta"]),
        "expected_hypothesis_effects": deepcopy(proposal_payload["expected_hypothesis_effects"]),
        "expected_falsification_conditions": deepcopy(
            proposal_payload["expected_falsification_conditions"]
        ),
        "expected_ambiguity_effects": deepcopy(proposal_payload["expected_ambiguity_effects"]),
        "expected_outcome_summary": proposal_payload["expected_outcome_summary"],
        "expected_outcome_refs": deepcopy(proposal_payload["expected_outcome_refs"]),
    }


def compute_adeu_arc_action_proposal_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_ACTION_PROPOSAL_SCHEMA)
    canonical_payload.pop("action_proposal_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_act_{digest[:32]}"


def compute_adeu_arc_rollout_trace_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_ROLLOUT_TRACE_SCHEMA)
    canonical_payload.pop("rollout_trace_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_roll_{digest[:32]}"


def canonicalize_adeu_arc_action_proposal_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcActionProposal.model_validate(payload).model_dump(mode="json", exclude_none=False)


def canonicalize_adeu_arc_rollout_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcRolloutTrace.model_validate(payload).model_dump(mode="json", exclude_none=False)


def materialize_adeu_arc_action_proposal_payload(
    payload_without_action_proposal_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_action_proposal_id)
    payload.setdefault("schema", ADEU_ARC_ACTION_PROPOSAL_SCHEMA)
    expectation_surface = expectation_surface_payload_for_proposal(payload)
    payload["expectation_surface_hash"] = _compute_expectation_surface_hash(expectation_surface)
    payload["action_proposal_id"] = compute_adeu_arc_action_proposal_id(payload)
    return canonicalize_adeu_arc_action_proposal_payload(payload)


def materialize_adeu_arc_rollout_trace_payload(
    payload_without_rollout_trace_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_rollout_trace_id)
    payload.setdefault("schema", ADEU_ARC_ROLLOUT_TRACE_SCHEMA)
    payload["rollout_trace_id"] = compute_adeu_arc_rollout_trace_id(payload)
    return canonicalize_adeu_arc_rollout_trace_payload(payload)


def derive_v42c_arc_action_proposal(
    *,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    observation_frame: dict[str, Any],
    observation_frame_ref: str,
    hypothesis_frame: dict[str, Any],
    hypothesis_frame_ref: str,
    proposal_step_index: int,
    proposal_status: ArcProposalStatus,
    proposed_action_kind: str | None,
    proposed_action_payload: dict[str, Any] | None,
    proposal_deontic_admissibility: ProposalDeonticAdmissibility,
    proposal_decision_basis: str,
    hypothesis_selection_basis: str,
    utility_pressure_basis: str,
    ambiguity_handling_basis: str,
    proposal_utility_posture: ProposalUtilityPosture,
    supporting_hypothesis_refs: list[str],
    alternative_action_register: list[dict[str, Any]],
    expected_state_delta: list[dict[str, Any]],
    expected_hypothesis_effects: list[dict[str, Any]],
    expected_falsification_conditions: list[dict[str, Any]],
    expected_ambiguity_effects: list[str],
    expected_outcome_summary: str,
    expected_outcome_refs: list[str],
) -> dict[str, Any]:
    if proposal_status == "admissible_candidate" and proposed_action_kind is not None:
        legal_envelope = set(task_packet["legal_action_envelope"])
        if proposed_action_kind not in legal_envelope:
            raise ValueError("proposed_action_kind is outside released legal_action_envelope")
    payload_without_id: dict[str, Any] = {
        "schema": ADEU_ARC_ACTION_PROPOSAL_SCHEMA,
        "task_packet_id": task_packet["task_packet_id"],
        "task_packet_ref": task_packet_ref,
        "observation_frame_id": observation_frame["observation_frame_id"],
        "observation_frame_ref": observation_frame_ref,
        "hypothesis_frame_id": hypothesis_frame["hypothesis_frame_id"],
        "hypothesis_frame_ref": hypothesis_frame_ref,
        "proposal_step_index": proposal_step_index,
        "proposal_status": proposal_status,
        "proposed_action_kind": proposed_action_kind,
        "proposed_action_payload": deepcopy(proposed_action_payload),
        "proposal_deontic_admissibility": proposal_deontic_admissibility,
        "proposal_decision_basis": proposal_decision_basis,
        "hypothesis_selection_basis": hypothesis_selection_basis,
        "utility_pressure_basis": utility_pressure_basis,
        "ambiguity_handling_basis": ambiguity_handling_basis,
        "proposal_utility_posture": proposal_utility_posture,
        "supporting_hypothesis_refs": deepcopy(supporting_hypothesis_refs),
        "alternative_action_register": deepcopy(alternative_action_register),
        "expected_state_delta": deepcopy(expected_state_delta),
        "expected_hypothesis_effects": deepcopy(expected_hypothesis_effects),
        "expected_falsification_conditions": deepcopy(expected_falsification_conditions),
        "expected_ambiguity_effects": deepcopy(expected_ambiguity_effects),
        "expected_outcome_summary": expected_outcome_summary,
        "expected_outcome_refs": deepcopy(expected_outcome_refs),
    }
    return materialize_adeu_arc_action_proposal_payload(payload_without_id)


def derive_v42c_arc_rollout_trace(
    *,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    action_proposal: dict[str, Any],
    action_proposal_ref: str,
    rollout_steps: list[dict[str, Any]],
    terminal_rollout_status: RolloutTerminalStatus,
    rollout_stop_reason: RolloutStopReason,
    outcome_hypothesis_effects: list[dict[str, Any]],
    expectation_outcome_comparison: dict[str, Any],
    settlement_posture_carry: dict[str, Any],
) -> dict[str, Any]:
    sorted_steps = sorted(deepcopy(rollout_steps), key=lambda step: step["step_index"])
    pre_refs = [step["pre_step_state_ref"] for step in sorted_steps]
    post_refs = [step["post_step_state_ref"] for step in sorted_steps]
    comparison = deepcopy(expectation_outcome_comparison)
    comparison.setdefault(
        "proposal_expectation_surface_hash",
        action_proposal["expectation_surface_hash"],
    )
    comparison.setdefault("matched_by_hash", True)
    payload_without_id: dict[str, Any] = {
        "schema": ADEU_ARC_ROLLOUT_TRACE_SCHEMA,
        "task_packet_id": task_packet["task_packet_id"],
        "task_packet_ref": task_packet_ref,
        "rollout_steps": sorted_steps,
        "pre_step_state_refs": pre_refs,
        "post_step_state_refs": post_refs,
        "terminal_rollout_status": terminal_rollout_status,
        "rollout_stop_reason": rollout_stop_reason,
        "outcome_hypothesis_effects": deepcopy(outcome_hypothesis_effects),
        "expectation_surface_ref": action_proposal_ref,
        "expectation_surface_hash": action_proposal["expectation_surface_hash"],
        "expectation_outcome_comparison": comparison,
        "settlement_posture_carry": deepcopy(settlement_posture_carry),
    }
    return materialize_adeu_arc_rollout_trace_payload(payload_without_id)
