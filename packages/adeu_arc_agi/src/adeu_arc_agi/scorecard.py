from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

ADEU_ARC_SCORECARD_MANIFEST_SCHEMA = "adeu_arc_scorecard_manifest@1"
V42E_V93_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS93.md#v42e_arc_scorecard_competition_contract@1"
)

ScorecardScope = Literal["single_run_scorecard_posture"]
ScorecardSourceKind = Literal[
    "local_shadow_only",
    "official_imported",
    "competition_posture_declared_no_official_scorecard",
    "deferred_absent",
]
AuthorityScope = Literal[
    "local_only",
    "official_imported",
    "competition_posture_only",
    "deferred",
]
AuthoritySourceKind = ScorecardSourceKind
AuthorityValidity = Literal["valid", "provisional", "deferred"]
CompetitionModePosture = Literal[
    "not_applicable",
    "declared_deferred",
    "eligible_but_not_exercised",
    "officially_exercised",
]
MetricStatus = Literal["pass", "fail", "informational"]

_REQUIRED_DEFERRED_ASSERTIONS: tuple[str, ...] = (
    "api_web_operator_surfaces_deferred",
    "benchmark_tournament_orchestration_deferred",
    "direct_online_submission_deferred",
)
_SOURCE_KIND_TO_AUTHORITY_SCOPE: dict[ScorecardSourceKind, AuthorityScope] = {
    "local_shadow_only": "local_only",
    "official_imported": "official_imported",
    "competition_posture_declared_no_official_scorecard": "competition_posture_only",
    "deferred_absent": "deferred",
}
_FORBIDDEN_AUTHORITY_TERMS: tuple[str, ...] = (
    "leaderboard_ready",
    "leaderboard_readiness",
    "leaderboard-readiness",
    "challenge_ready",
    "challenge_readiness",
    "challenge-readiness",
    "competition_success_authority",
    "competition-success authority",
    "official_scorecard_authority_granted",
    "online_submission_enabled",
)
_FORBIDDEN_NECESSITY_TERMS: tuple[str, ...] = (
    "universal necessity",
    "all solutions must",
    "proves the rule",
    "always must",
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
        normalized_term = _normalize_for_term_match(term)
        if normalized_term in normalized:
            raise ValueError(f"{field_name} may not contain forbidden term '{term}'")


class ArcScorecardMetricEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    metric_key: str
    metric_value: float
    status: MetricStatus
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_metric(self) -> ArcScorecardMetricEntry:
        object.__setattr__(
            self, "metric_key", _assert_non_empty_text(self.metric_key, field_name="metric_key")
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )
        return self


class ArcScorecardSettlementPostureCarry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    ambiguity_posture_preserved: bool
    claim_posture_preserved: bool
    necessity_laundering_detected: bool
    summary: str

    @model_validator(mode="after")
    def _validate_settlement(self) -> ArcScorecardSettlementPostureCarry:
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        _assert_no_forbidden_terms(
            value=self.summary,
            field_name="summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS + _FORBIDDEN_NECESSITY_TERMS,
        )
        if self.necessity_laundering_detected:
            raise ValueError(
                "necessity_laundering_detected must be false for v42e scorecard artifacts"
            )
        if not self.ambiguity_posture_preserved:
            raise ValueError("ambiguity_posture_preserved must be true in v42e scorecards")
        if not self.claim_posture_preserved:
            raise ValueError("claim_posture_preserved must be true in v42e scorecards")
        return self


class AdeuArcScorecardManifest(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_SCORECARD_MANIFEST_SCHEMA] = ADEU_ARC_SCORECARD_MANIFEST_SCHEMA
    scorecard_manifest_id: str
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
    local_eval_record_id: str
    local_eval_record_ref: str
    environment_ref: str
    session_ref: str
    competition_scope_ref: str
    scorecard_scope: ScorecardScope
    scorecard_profile: str
    model_id: str
    run_id: str
    scorecard_source_kind: ScorecardSourceKind
    authority_posture: str
    authority_scope: AuthorityScope
    authority_source_kind: AuthoritySourceKind
    authority_validity: AuthorityValidity
    authority_limitations: str
    competition_mode_posture: CompetitionModePosture
    local_replay_lineage_refs: list[str] = Field(min_length=1)
    external_replay_authority_refs: list[str]
    scorecard_facing_metrics: list[ArcScorecardMetricEntry] = Field(min_length=1)
    official_scorecard_outcome_metrics: list[ArcScorecardMetricEntry]
    scorecard_outcome_summary: str
    settlement_posture_carry: ArcScorecardSettlementPostureCarry
    authority_basis_refs: list[str] = Field(min_length=1)
    deferred_authority_assertions: list[str] = Field(min_length=1)
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_manifest(self) -> AdeuArcScorecardManifest:
        text_fields = (
            "scorecard_manifest_id",
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
            "local_eval_record_id",
            "local_eval_record_ref",
            "environment_ref",
            "session_ref",
            "competition_scope_ref",
            "scorecard_profile",
            "model_id",
            "run_id",
            "authority_posture",
            "authority_limitations",
            "scorecard_outcome_summary",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )

        object.__setattr__(
            self,
            "local_replay_lineage_refs",
            _assert_sorted_unique(
                self.local_replay_lineage_refs,
                field_name="local_replay_lineage_refs",
            ),
        )
        object.__setattr__(
            self,
            "external_replay_authority_refs",
            _assert_sorted_unique(
                self.external_replay_authority_refs,
                field_name="external_replay_authority_refs",
            ),
        )
        object.__setattr__(
            self,
            "authority_basis_refs",
            _assert_sorted_unique(
                self.authority_basis_refs,
                field_name="authority_basis_refs",
            ),
        )
        object.__setattr__(
            self,
            "deferred_authority_assertions",
            _assert_sorted_unique(
                self.deferred_authority_assertions,
                field_name="deferred_authority_assertions",
            ),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )

        if self.authority_source_kind != self.scorecard_source_kind:
            raise ValueError("authority_source_kind must match scorecard_source_kind")

        expected_scope = _SOURCE_KIND_TO_AUTHORITY_SCOPE[self.scorecard_source_kind]
        if self.authority_scope != expected_scope:
            raise ValueError("authority_scope must match scorecard_source_kind posture")

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
                    "deferred_authority_assertions must include submission/tournament/operator "
                    "deferrals"
                )

        if set(self.local_replay_lineage_refs) & set(self.external_replay_authority_refs):
            raise ValueError(
                "local_replay_lineage_refs and external_replay_authority_refs may not overlap"
            )
        required_local_refs = {
            self.task_packet_ref,
            self.observation_frame_ref,
            self.hypothesis_frame_ref,
            self.action_proposal_ref,
            self.rollout_trace_ref,
            self.local_eval_record_ref,
        }
        if not required_local_refs.issubset(set(self.local_replay_lineage_refs)):
            raise ValueError("local_replay_lineage_refs must include all released lineage refs")

        scorecard_facing_keys = [metric.metric_key for metric in self.scorecard_facing_metrics]
        if scorecard_facing_keys != sorted(scorecard_facing_keys):
            raise ValueError("scorecard_facing_metrics must be sorted by metric_key")
        if len(scorecard_facing_keys) != len(set(scorecard_facing_keys)):
            raise ValueError("scorecard_facing_metrics must use unique metric_key values")

        official_keys = [metric.metric_key for metric in self.official_scorecard_outcome_metrics]
        if official_keys != sorted(official_keys):
            raise ValueError("official_scorecard_outcome_metrics must be sorted by metric_key")
        if len(official_keys) != len(set(official_keys)):
            raise ValueError("official_scorecard_outcome_metrics must use unique metric_key values")

        if self.scorecard_source_kind == "official_imported":
            if self.authority_validity != "valid":
                raise ValueError(
                    "authority_validity must be valid when scorecard_source_kind is "
                    "official_imported"
                )
            if not self.external_replay_authority_refs:
                raise ValueError(
                    "external_replay_authority_refs must be non-empty for official_imported "
                    "scorecards"
                )
            if not self.official_scorecard_outcome_metrics:
                raise ValueError(
                    "official_scorecard_outcome_metrics must be non-empty for official_imported "
                    "scorecards"
                )
        else:
            if self.official_scorecard_outcome_metrics:
                raise ValueError(
                    "official_scorecard_outcome_metrics requires scorecard_source_kind="
                    "official_imported"
                )

        if (
            self.competition_mode_posture == "officially_exercised"
            and self.scorecard_source_kind != "official_imported"
        ):
            raise ValueError(
                "competition_mode_posture=officially_exercised requires official_imported source"
            )

        if self.scorecard_source_kind == "deferred_absent":
            if self.authority_validity != "deferred":
                raise ValueError(
                    "authority_validity must be deferred when scorecard_source_kind is "
                    "deferred_absent"
                )
            if self.competition_mode_posture not in ("declared_deferred", "not_applicable"):
                raise ValueError(
                    "deferred_absent scorecards require declared_deferred or not_applicable "
                    "competition posture"
                )

        textual_fields = (
            self.authority_posture,
            self.authority_limitations,
            self.scorecard_outcome_summary,
            self.settlement_posture_carry.summary,
        )
        for field_value in textual_fields:
            _assert_no_forbidden_terms(
                value=field_value,
                field_name="scorecard textual fields",
                terms=_FORBIDDEN_NECESSITY_TERMS,
            )
        if self.scorecard_source_kind != "official_imported":
            for field_value in textual_fields:
                _assert_no_forbidden_terms(
                    value=field_value,
                    field_name="non-official textual fields",
                    terms=_FORBIDDEN_AUTHORITY_TERMS,
                )

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("scorecard_manifest_id", None)
        expected_id = compute_adeu_arc_scorecard_manifest_id(payload_without_id)
        if self.scorecard_manifest_id != expected_id:
            raise ValueError(
                "scorecard_manifest_id must match canonical full payload hash identity"
            )
        return self


def compute_adeu_arc_scorecard_manifest_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_SCORECARD_MANIFEST_SCHEMA)
    canonical_payload.pop("scorecard_manifest_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_score_{digest[:32]}"


def canonicalize_adeu_arc_scorecard_manifest_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcScorecardManifest.model_validate(payload).model_dump(mode="json")


def materialize_adeu_arc_scorecard_manifest_payload(
    payload_without_scorecard_manifest_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_scorecard_manifest_id)
    payload.setdefault("schema", ADEU_ARC_SCORECARD_MANIFEST_SCHEMA)
    payload["scorecard_manifest_id"] = compute_adeu_arc_scorecard_manifest_id(payload)
    return canonicalize_adeu_arc_scorecard_manifest_payload(payload)


def derive_v42e_arc_scorecard_manifest(
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
    local_eval_record: dict[str, Any],
    local_eval_record_ref: str,
    environment_ref: str,
    session_ref: str,
    competition_scope_ref: str,
    scorecard_scope: ScorecardScope,
    scorecard_profile: str,
    model_id: str,
    run_id: str,
    scorecard_source_kind: ScorecardSourceKind,
    authority_posture: str,
    authority_scope: AuthorityScope,
    authority_source_kind: AuthoritySourceKind,
    authority_validity: AuthorityValidity,
    authority_limitations: str,
    competition_mode_posture: CompetitionModePosture,
    local_replay_lineage_refs: list[str],
    external_replay_authority_refs: list[str],
    scorecard_facing_metrics: list[dict[str, Any]],
    official_scorecard_outcome_metrics: list[dict[str, Any]],
    scorecard_outcome_summary: str,
    settlement_posture_carry: dict[str, Any],
    authority_basis_refs: list[str],
    deferred_authority_assertions: list[str],
    evidence_refs: list[str],
) -> dict[str, Any]:
    task_packet_id = task_packet["task_packet_id"]
    if observation_frame["task_packet_id"] != task_packet_id:
        raise ValueError("observation_frame must bind to released task_packet_id")
    if hypothesis_frame["task_packet_id"] != task_packet_id:
        raise ValueError("hypothesis_frame must bind to released task_packet_id")
    if action_proposal["task_packet_id"] != task_packet_id:
        raise ValueError("action_proposal must bind to released task_packet_id")
    if rollout_trace["task_packet_id"] != task_packet_id:
        raise ValueError("rollout_trace must bind to released task_packet_id")
    if local_eval_record["task_packet_id"] != task_packet_id:
        raise ValueError("local_eval_record must bind to released task_packet_id")
    if local_eval_record["task_packet_ref"] != task_packet_ref:
        raise ValueError("local_eval_record must preserve released task_packet_ref")
    if local_eval_record["observation_frame_id"] != observation_frame["observation_frame_id"]:
        raise ValueError("local_eval_record must preserve released observation_frame_id")
    if local_eval_record["observation_frame_ref"] != observation_frame_ref:
        raise ValueError("local_eval_record must preserve released observation_frame_ref")
    if local_eval_record["hypothesis_frame_id"] != hypothesis_frame["hypothesis_frame_id"]:
        raise ValueError("local_eval_record must preserve released hypothesis_frame_id")
    if local_eval_record["hypothesis_frame_ref"] != hypothesis_frame_ref:
        raise ValueError("local_eval_record must preserve released hypothesis_frame_ref")
    if local_eval_record["action_proposal_id"] != action_proposal["action_proposal_id"]:
        raise ValueError("local_eval_record must preserve released action_proposal_id")
    if local_eval_record["action_proposal_ref"] != action_proposal_ref:
        raise ValueError("local_eval_record must preserve released action_proposal_ref")
    if local_eval_record["rollout_trace_id"] != rollout_trace["rollout_trace_id"]:
        raise ValueError("local_eval_record must preserve released rollout_trace_id")
    if local_eval_record["rollout_trace_ref"] != rollout_trace_ref:
        raise ValueError("local_eval_record must preserve released rollout_trace_ref")
    if local_eval_record["model_id"] != model_id:
        raise ValueError("model_id must match released local_eval_record model lineage")
    if local_eval_record["run_id"] != run_id:
        raise ValueError("run_id must match released local_eval_record run lineage")

    required_local_lineage_refs = {
        task_packet_ref,
        observation_frame_ref,
        hypothesis_frame_ref,
        action_proposal_ref,
        rollout_trace_ref,
        local_eval_record_ref,
    }
    if not required_local_lineage_refs.issubset(set(local_replay_lineage_refs)):
        raise ValueError(
            "local_replay_lineage_refs must include all released task/observation/hypothesis/"
            "action/rollout/local_eval refs"
        )

    payload_without_id: dict[str, Any] = {
        "schema": ADEU_ARC_SCORECARD_MANIFEST_SCHEMA,
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
        "local_eval_record_id": local_eval_record["local_eval_record_id"],
        "local_eval_record_ref": local_eval_record_ref,
        "environment_ref": environment_ref,
        "session_ref": session_ref,
        "competition_scope_ref": competition_scope_ref,
        "scorecard_scope": scorecard_scope,
        "scorecard_profile": scorecard_profile,
        "model_id": model_id,
        "run_id": run_id,
        "scorecard_source_kind": scorecard_source_kind,
        "authority_posture": authority_posture,
        "authority_scope": authority_scope,
        "authority_source_kind": authority_source_kind,
        "authority_validity": authority_validity,
        "authority_limitations": authority_limitations,
        "competition_mode_posture": competition_mode_posture,
        "local_replay_lineage_refs": deepcopy(local_replay_lineage_refs),
        "external_replay_authority_refs": deepcopy(external_replay_authority_refs),
        "scorecard_facing_metrics": deepcopy(scorecard_facing_metrics),
        "official_scorecard_outcome_metrics": deepcopy(official_scorecard_outcome_metrics),
        "scorecard_outcome_summary": scorecard_outcome_summary,
        "settlement_posture_carry": deepcopy(settlement_posture_carry),
        "authority_basis_refs": deepcopy(authority_basis_refs),
        "deferred_authority_assertions": deepcopy(deferred_authority_assertions),
        "evidence_refs": deepcopy(evidence_refs),
    }
    return materialize_adeu_arc_scorecard_manifest_payload(payload_without_id)
