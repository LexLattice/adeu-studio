from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA = "adeu_arc_local_eval_record@1"
V42D_V92_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS92.md#v42d_arc_local_benchmark_eval_contract@1"
)

BenchmarkScope = Literal["single_run_local_eval"]
AdherenceMetricStatus = Literal["pass", "fail"]
RolloutTerminalStatus = Literal["completed", "blocked", "stopped"]

_REQUIRED_ADHERENCE_KEYS: tuple[str, ...] = (
    "ambiguity_carry_fidelity",
    "claim_posture_honesty",
    "deontic_compliance",
    "expectation_outcome_honesty",
    "lineage_completeness",
    "retroactive_necessity_laundering_absent",
    "scorecard_replay_leakage_absent",
)
_REQUIRED_DEFERRED_ASSERTIONS: tuple[str, ...] = (
    "competition_mode_deferred",
    "replay_authority_deferred",
    "scorecard_authority_deferred",
)
_FORBIDDEN_AUTHORITY_TERMS: tuple[str, ...] = (
    "scorecard_authority_granted",
    "replay_authority_granted",
    "competition_mode_enabled",
    "online_submission_enabled",
    "adeu_arc_scorecard_manifest@1",
    "leaderboard_ready",
)
_FORBIDDEN_NECESSITY_TERMS: tuple[str, ...] = (
    "universal_necessity",
    "all_solutions_must",
    "proves_the_rule",
    "always_must",
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


def _normalize_for_term_match(value: str) -> str:
    lowered = value.lower()
    for token in ("-", " "):
        lowered = lowered.replace(token, "_")
    return lowered


def _assert_no_forbidden_terms(*, value: str, field_name: str, terms: tuple[str, ...]) -> None:
    normalized = _normalize_for_term_match(value)
    for term in terms:
        if term in normalized:
            raise ValueError(f"{field_name} may not contain forbidden term '{term}'")


class ArcTaskSuccessMetrics(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    task_solved: bool
    steps_executed: int = Field(ge=0)
    terminal_rollout_status: RolloutTerminalStatus
    goal_condition_summary: str

    @model_validator(mode="after")
    def _validate_task_success(self) -> ArcTaskSuccessMetrics:
        object.__setattr__(
            self,
            "goal_condition_summary",
            _assert_non_empty_text(
                self.goal_condition_summary,
                field_name="goal_condition_summary",
            ),
        )
        _assert_no_forbidden_terms(
            value=self.goal_condition_summary,
            field_name="goal_condition_summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS + _FORBIDDEN_NECESSITY_TERMS,
        )
        return self


class ArcAdherenceMetricEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    metric_key: str
    metric_value: float = Field(ge=0.0, le=1.0)
    status: AdherenceMetricStatus
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_adherence_metric(self) -> ArcAdherenceMetricEntry:
        object.__setattr__(
            self, "metric_key", _assert_non_empty_text(self.metric_key, field_name="metric_key")
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )
        return self


class ArcAdherenceFailure(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    metric_key: str
    reason: str
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_failure(self) -> ArcAdherenceFailure:
        object.__setattr__(
            self, "metric_key", _assert_non_empty_text(self.metric_key, field_name="metric_key")
        )
        object.__setattr__(self, "reason", _assert_non_empty_text(self.reason, field_name="reason"))
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )
        _assert_no_forbidden_terms(
            value=self.reason,
            field_name="reason",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )
        return self


class ArcControlPlaneAdherenceMetrics(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    checks_passed: int = Field(ge=0)
    checks_total: int = Field(ge=1)
    adherence_rate: float = Field(ge=0.0, le=1.0)

    @model_validator(mode="after")
    def _validate_summary(self) -> ArcControlPlaneAdherenceMetrics:
        if self.checks_passed > self.checks_total:
            raise ValueError("checks_passed may not exceed checks_total")
        expected_rate = self.checks_passed / self.checks_total
        if abs(self.adherence_rate - expected_rate) > 1e-9:
            raise ValueError("adherence_rate must match checks_passed/checks_total")
        return self


class ArcSettlementPostureChecks(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    ambiguity_posture_preserved: bool
    claim_posture_preserved: bool
    necessity_laundering_detected: bool
    summary: str

    @model_validator(mode="after")
    def _validate_settlement(self) -> ArcSettlementPostureChecks:
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        _assert_no_forbidden_terms(
            value=self.summary,
            field_name="summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS,
        )
        return self


class AdeuArcLocalEvalRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA] = ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA
    local_eval_record_id: str
    task_packet_id: str
    task_packet_ref: str
    observation_frame_id: str
    observation_frame_ref: str
    hypothesis_frame_id: str
    hypothesis_frame_ref: str
    action_proposal_id: str
    action_proposal_ref: str
    rollout_trace_id: str
    rollout_trace_ref: str
    benchmark_scope: BenchmarkScope
    benchmark_profile: str
    model_id: str
    run_id: str
    sample_basis: str
    evaluation_rule_set_ref: str
    evaluation_method_version: str
    task_success_basis: str
    adherence_metric_basis: str
    ground_truth_refs: list[str] = Field(min_length=1)
    task_success_metrics: ArcTaskSuccessMetrics
    adherence_metric_register: list[ArcAdherenceMetricEntry] = Field(min_length=1)
    adherence_failure_register: list[ArcAdherenceFailure]
    control_plane_adherence_metrics: ArcControlPlaneAdherenceMetrics
    settlement_posture_checks: ArcSettlementPostureChecks
    evaluation_summary: str
    evidence_refs: list[str] = Field(min_length=1)
    deferred_authority_assertions: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_record(self) -> AdeuArcLocalEvalRecord:
        text_fields = (
            "local_eval_record_id",
            "task_packet_id",
            "task_packet_ref",
            "observation_frame_id",
            "observation_frame_ref",
            "hypothesis_frame_id",
            "hypothesis_frame_ref",
            "action_proposal_id",
            "action_proposal_ref",
            "rollout_trace_id",
            "rollout_trace_ref",
            "benchmark_profile",
            "model_id",
            "run_id",
            "sample_basis",
            "evaluation_rule_set_ref",
            "evaluation_method_version",
            "task_success_basis",
            "adherence_metric_basis",
            "evaluation_summary",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )

        object.__setattr__(
            self,
            "ground_truth_refs",
            _assert_sorted_unique(self.ground_truth_refs, field_name="ground_truth_refs"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )
        object.__setattr__(
            self,
            "deferred_authority_assertions",
            _assert_sorted_unique(
                self.deferred_authority_assertions,
                field_name="deferred_authority_assertions",
            ),
        )

        for assertion in self.deferred_authority_assertions:
            _assert_no_forbidden_terms(
                value=assertion,
                field_name="deferred_authority_assertions",
                terms=("granted", "enabled", "authorized"),
            )
            if not assertion.endswith("_deferred"):
                raise ValueError("deferred_authority_assertions entries must end with '_deferred'")
        for required in _REQUIRED_DEFERRED_ASSERTIONS:
            if required not in self.deferred_authority_assertions:
                raise ValueError(
                    "deferred_authority_assertions must include "
                    "scorecard/replay/competition deferral"
                )

        _assert_no_forbidden_terms(
            value=self.evaluation_summary,
            field_name="evaluation_summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS + _FORBIDDEN_NECESSITY_TERMS,
        )

        metric_keys = [metric.metric_key for metric in self.adherence_metric_register]
        if metric_keys != sorted(metric_keys):
            raise ValueError("adherence_metric_register must be sorted by metric_key")
        if len(metric_keys) != len(set(metric_keys)):
            raise ValueError("adherence_metric_register metric_key values must be unique")
        if tuple(metric_keys) != _REQUIRED_ADHERENCE_KEYS:
            raise ValueError(
                "adherence_metric_register must include the required decomposition keys"
            )

        failed_metric_keys = {
            metric.metric_key
            for metric in self.adherence_metric_register
            if metric.status == "fail"
        }
        failure_keys = [failure.metric_key for failure in self.adherence_failure_register]
        if len(failure_keys) != len(set(failure_keys)):
            raise ValueError("adherence_failure_register metric_key values must be unique")
        if failed_metric_keys:
            if not failure_keys:
                raise ValueError(
                    "adherence_failure_register must be non-empty when adherence metrics fail"
                )
            if set(failure_keys) != failed_metric_keys:
                raise ValueError("adherence_failure_register must match failing adherence metrics")
        elif failure_keys:
            raise ValueError(
                "adherence_failure_register must be empty when all adherence metrics pass"
            )

        checks_total = len(self.adherence_metric_register)
        checks_passed = len(
            [metric for metric in self.adherence_metric_register if metric.status == "pass"]
        )
        if self.control_plane_adherence_metrics.checks_total != checks_total:
            raise ValueError("checks_total must equal adherence_metric_register length")
        if self.control_plane_adherence_metrics.checks_passed != checks_passed:
            raise ValueError("checks_passed must equal passing adherence metric count")

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("local_eval_record_id", None)
        expected_id = compute_adeu_arc_local_eval_record_id(payload_without_id)
        if self.local_eval_record_id != expected_id:
            raise ValueError("local_eval_record_id must match canonical full payload hash identity")
        return self


def compute_adeu_arc_local_eval_record_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA)
    canonical_payload.pop("local_eval_record_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_eval_{digest[:32]}"


def canonicalize_adeu_arc_local_eval_record_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcLocalEvalRecord.model_validate(payload).model_dump(mode="json")


def materialize_adeu_arc_local_eval_record_payload(
    payload_without_local_eval_record_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_local_eval_record_id)
    payload.setdefault("schema", ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA)
    payload["local_eval_record_id"] = compute_adeu_arc_local_eval_record_id(payload)
    return canonicalize_adeu_arc_local_eval_record_payload(payload)


def derive_v42d_arc_local_eval_record(
    *,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    observation_frame: dict[str, Any],
    observation_frame_ref: str,
    hypothesis_frame: dict[str, Any],
    hypothesis_frame_ref: str,
    action_proposal: dict[str, Any],
    action_proposal_ref: str,
    rollout_trace: dict[str, Any],
    rollout_trace_ref: str,
    benchmark_scope: BenchmarkScope,
    benchmark_profile: str,
    model_id: str,
    run_id: str,
    sample_basis: str,
    evaluation_rule_set_ref: str,
    evaluation_method_version: str,
    task_success_basis: str,
    adherence_metric_basis: str,
    ground_truth_refs: list[str],
    task_success_metrics: dict[str, Any],
    adherence_metric_register: list[dict[str, Any]],
    adherence_failure_register: list[dict[str, Any]],
    control_plane_adherence_metrics: dict[str, Any],
    settlement_posture_checks: dict[str, Any],
    evaluation_summary: str,
    evidence_refs: list[str],
    deferred_authority_assertions: list[str],
) -> dict[str, Any]:
    task_packet_id = task_packet["task_packet_id"]
    if observation_frame["task_packet_id"] != task_packet_id:
        raise ValueError("observation_frame must bind to released task_packet_id")
    if hypothesis_frame["task_packet_id"] != task_packet_id:
        raise ValueError("hypothesis_frame must bind to released task_packet_id")
    if hypothesis_frame["observation_frame_id"] != observation_frame["observation_frame_id"]:
        raise ValueError("hypothesis_frame must bind to released observation_frame_id")
    if action_proposal["task_packet_id"] != task_packet_id:
        raise ValueError("action_proposal must bind to released task_packet_id")
    if action_proposal["observation_frame_id"] != observation_frame["observation_frame_id"]:
        raise ValueError("action_proposal must bind to released observation_frame_id")
    if action_proposal["hypothesis_frame_id"] != hypothesis_frame["hypothesis_frame_id"]:
        raise ValueError("action_proposal must bind to released hypothesis_frame_id")
    if rollout_trace["task_packet_id"] != task_packet_id:
        raise ValueError("rollout_trace must bind to released task_packet_id")
    if rollout_trace["expectation_surface_hash"] != action_proposal["expectation_surface_hash"]:
        raise ValueError("rollout_trace must preserve released action expectation lineage")

    payload_without_id: dict[str, Any] = {
        "schema": ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA,
        "task_packet_id": task_packet_id,
        "task_packet_ref": task_packet_ref,
        "observation_frame_id": observation_frame["observation_frame_id"],
        "observation_frame_ref": observation_frame_ref,
        "hypothesis_frame_id": hypothesis_frame["hypothesis_frame_id"],
        "hypothesis_frame_ref": hypothesis_frame_ref,
        "action_proposal_id": action_proposal["action_proposal_id"],
        "action_proposal_ref": action_proposal_ref,
        "rollout_trace_id": rollout_trace["rollout_trace_id"],
        "rollout_trace_ref": rollout_trace_ref,
        "benchmark_scope": benchmark_scope,
        "benchmark_profile": benchmark_profile,
        "model_id": model_id,
        "run_id": run_id,
        "sample_basis": sample_basis,
        "evaluation_rule_set_ref": evaluation_rule_set_ref,
        "evaluation_method_version": evaluation_method_version,
        "task_success_basis": task_success_basis,
        "adherence_metric_basis": adherence_metric_basis,
        "ground_truth_refs": deepcopy(ground_truth_refs),
        "task_success_metrics": deepcopy(task_success_metrics),
        "adherence_metric_register": deepcopy(adherence_metric_register),
        "adherence_failure_register": deepcopy(adherence_failure_register),
        "control_plane_adherence_metrics": deepcopy(control_plane_adherence_metrics),
        "settlement_posture_checks": deepcopy(settlement_posture_checks),
        "evaluation_summary": evaluation_summary,
        "evidence_refs": deepcopy(evidence_refs),
        "deferred_authority_assertions": deepcopy(deferred_authority_assertions),
    }
    return materialize_adeu_arc_local_eval_record_payload(payload_without_id)
