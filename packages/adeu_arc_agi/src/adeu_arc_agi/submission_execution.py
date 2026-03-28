from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA = "adeu_arc_submission_execution_record@1"
V42F_V94_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS94.md#v42f_arc_submission_execution_contract@1"
)
V42F_V94_LIFECYCLE_TRANSITION_MATRIX_REF = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS94.md#v42f_submission_lifecycle_transition_matrix@1"
)

ScorecardSourceKind = Literal[
    "local_shadow_only",
    "official_imported",
    "competition_posture_declared_no_official_scorecard",
    "deferred_absent",
]
SubmissionAuthorizationStatus = Literal["not_authorized", "deferred", "authorized"]
SubmissionExecutionStatus = Literal[
    "not_submitted",
    "submitted_pending_receipt",
    "submitted_acknowledged",
    "submission_failed",
]
ResultImportStatus = Literal["not_imported", "deferred", "official_imported", "import_failed"]
AuthorizationValidity = Literal["valid", "deferred", "invalid"]
ResultAuthorityValidity = Literal["valid", "deferred", "invalid"]
BoundedOrchestrationConstraint = Literal[
    "deferred_multi_run",
    "no_parallel_competition_fanout",
    "no_tournament_execution",
    "single_submission_only",
]

_SUBMITTED_EXECUTION_STATUSES: tuple[SubmissionExecutionStatus, ...] = (
    "submitted_pending_receipt",
    "submitted_acknowledged",
    "submission_failed",
)
_RECEIPT_REQUIRED_EXECUTION_STATUSES: tuple[SubmissionExecutionStatus, ...] = (
    "submitted_acknowledged",
)
_REQUIRED_BOUNDED_ORCHESTRATION_CONSTRAINTS: tuple[BoundedOrchestrationConstraint, ...] = (
    "deferred_multi_run",
    "no_parallel_competition_fanout",
    "no_tournament_execution",
    "single_submission_only",
)
_ALLOWED_EXECUTION_TO_RESULT_IMPORT: dict[
    SubmissionExecutionStatus, tuple[ResultImportStatus, ...]
] = {
    "not_submitted": ("not_imported", "deferred"),
    "submitted_pending_receipt": ("not_imported", "deferred"),
    "submitted_acknowledged": ("not_imported", "deferred", "official_imported", "import_failed"),
    "submission_failed": ("not_imported", "deferred"),
}
_FORBIDDEN_AUTHORITY_TERMS: tuple[str, ...] = (
    "leaderboard_ready",
    "leaderboard_readiness",
    "competition_success_authority",
    "official_submission_authority_granted",
    "benchmark_tournament_orchestration_execution",
    "api_web_operator_surfaces_enabled",
)
_FORBIDDEN_NECESSITY_TERMS: tuple[str, ...] = (
    "universal_necessity",
    "all_solutions_must",
    "always_must",
    "proves_the_rule",
)
_FORBIDDEN_DEFERRED_ASSERTION_TERMS: tuple[str, ...] = (
    "authorized",
    "granted",
    "enabled",
    "official_imported",
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


def _assert_hash(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if len(normalized) != 64:
        raise ValueError(f"{field_name} must be a 64-character lowercase hex digest")
    for ch in normalized:
        if ch not in "0123456789abcdef":
            raise ValueError(f"{field_name} must be a 64-character lowercase hex digest")
    return normalized


def _assert_optional_hash(value: str | None, *, field_name: str) -> str | None:
    if value is None:
        return None
    return _assert_hash(value, field_name=field_name)


def _assert_identity_chain_binding(
    *,
    ref_value: str,
    ref_field_name: str,
    external_request_ref: str,
    environment_ref: str,
    session_ref: str,
    competition_scope_ref: str,
) -> None:
    required_tokens = (
        external_request_ref,
        environment_ref,
        session_ref,
        competition_scope_ref,
    )
    for token in required_tokens:
        if token not in ref_value:
            raise ValueError(
                f"{ref_field_name} must bind to the same request/environment/session/"
                "competition identity chain"
            )


class ArcSubmissionSettlementPostureCarry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    ambiguity_posture_preserved: bool
    claim_posture_preserved: bool
    necessity_laundering_detected: bool
    summary: str

    @model_validator(mode="after")
    def _validate_settlement(self) -> ArcSubmissionSettlementPostureCarry:
        object.__setattr__(
            self,
            "summary",
            _assert_non_empty_text(self.summary, field_name="summary"),
        )
        _assert_no_forbidden_terms(
            value=self.summary,
            field_name="summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS + _FORBIDDEN_NECESSITY_TERMS,
        )
        if not self.ambiguity_posture_preserved:
            raise ValueError("ambiguity_posture_preserved must be true for v42f artifacts")
        if not self.claim_posture_preserved:
            raise ValueError("claim_posture_preserved must be true for v42f artifacts")
        if self.necessity_laundering_detected:
            raise ValueError("necessity_laundering_detected must be false for v42f artifacts")
        return self


class AdeuArcSubmissionExecutionRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[
        ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA
    ] = ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA
    submission_execution_id: str
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
    scorecard_manifest_id: str
    scorecard_manifest_ref: str
    environment_ref: str
    session_ref: str
    competition_scope_ref: str
    model_id: str
    run_id: str
    submission_authorization_status: SubmissionAuthorizationStatus
    submission_authorization_source_kind: ScorecardSourceKind
    submission_authorization_validity: AuthorizationValidity
    submission_authorization_basis_refs: list[str] = Field(min_length=1)
    submission_execution_status: SubmissionExecutionStatus
    submission_transport_profile: str
    external_request_ref: str
    submission_payload_ref: str
    submission_payload_hash: str
    submission_request_ts: int = Field(ge=0)
    submission_receipt_ref: str | None = None
    submission_receipt_hash: str | None = None
    submission_receipt_ts: int | None = Field(default=None, ge=0)
    result_import_status: ResultImportStatus
    result_source_kind: ScorecardSourceKind
    result_authority_validity: ResultAuthorityValidity
    result_authority_basis_refs: list[str] = Field(min_length=1)
    result_import_ref: str | None = None
    result_import_hash: str | None = None
    result_import_ts: int | None = Field(default=None, ge=0)
    lifecycle_transition_matrix_ref: str
    submission_result_posture: str
    submission_result_summary: str
    bounded_orchestration_constraint_register: list[BoundedOrchestrationConstraint] = Field(
        min_length=1
    )
    settlement_posture_carry: ArcSubmissionSettlementPostureCarry
    deferred_authority_assertions: list[str] = Field(min_length=1)
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_record(self) -> AdeuArcSubmissionExecutionRecord:
        text_fields = (
            "submission_execution_id",
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
            "scorecard_manifest_id",
            "scorecard_manifest_ref",
            "environment_ref",
            "session_ref",
            "competition_scope_ref",
            "model_id",
            "run_id",
            "submission_transport_profile",
            "external_request_ref",
            "submission_payload_ref",
            "lifecycle_transition_matrix_ref",
            "submission_result_posture",
            "submission_result_summary",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )

        if self.lifecycle_transition_matrix_ref != V42F_V94_LIFECYCLE_TRANSITION_MATRIX_REF:
            raise ValueError(
                "lifecycle_transition_matrix_ref must match the released v42f transition matrix"
            )

        object.__setattr__(
            self,
            "submission_authorization_basis_refs",
            _assert_sorted_unique(
                self.submission_authorization_basis_refs,
                field_name="submission_authorization_basis_refs",
            ),
        )
        object.__setattr__(
            self,
            "result_authority_basis_refs",
            _assert_sorted_unique(
                self.result_authority_basis_refs,
                field_name="result_authority_basis_refs",
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

        object.__setattr__(
            self,
            "submission_payload_hash",
            _assert_hash(self.submission_payload_hash, field_name="submission_payload_hash"),
        )
        object.__setattr__(
            self,
            "submission_receipt_hash",
            _assert_optional_hash(
                self.submission_receipt_hash,
                field_name="submission_receipt_hash",
            ),
        )
        object.__setattr__(
            self,
            "result_import_hash",
            _assert_optional_hash(self.result_import_hash, field_name="result_import_hash"),
        )

        if self.submission_authorization_status == "authorized":
            if self.submission_authorization_source_kind != "official_imported":
                raise ValueError(
                    "authorized submission requires submission_authorization_source_kind="
                    "official_imported"
                )
            if self.submission_authorization_validity != "valid":
                raise ValueError(
                    "authorized submission requires submission_authorization_validity=valid"
                )
        elif self.submission_authorization_status == "deferred":
            if self.submission_authorization_validity != "deferred":
                raise ValueError(
                    "deferred submission requires submission_authorization_validity=deferred"
                )
            if self.submission_authorization_source_kind == "official_imported":
                raise ValueError("deferred submission may not use official_imported source kind")
        else:
            if self.submission_authorization_validity != "invalid":
                raise ValueError(
                    "not_authorized submission requires submission_authorization_validity=invalid"
                )
            if self.submission_authorization_source_kind == "official_imported":
                raise ValueError(
                    "not_authorized submission may not use official_imported source kind"
                )

        if self.submission_execution_status in _SUBMITTED_EXECUTION_STATUSES:
            if self.submission_authorization_status != "authorized":
                raise ValueError(
                    "submitted execution statuses require submission_authorization_status="
                    "authorized"
                )

        if self.submission_execution_status in _RECEIPT_REQUIRED_EXECUTION_STATUSES:
            if (
                self.submission_receipt_ref is None
                or self.submission_receipt_hash is None
                or self.submission_receipt_ts is None
            ):
                raise ValueError(
                    "submitted_acknowledged status requires receipt ref/hash/timestamp binding"
                )
        else:
            if any(
                value is not None
                for value in (
                    self.submission_receipt_ref,
                    self.submission_receipt_hash,
                    self.submission_receipt_ts,
                )
            ):
                raise ValueError(
                    "receipt ref/hash/timestamp may only be present for submitted_acknowledged "
                    "status"
                )

        allowed_result_statuses = _ALLOWED_EXECUTION_TO_RESULT_IMPORT[
            self.submission_execution_status
        ]
        if self.result_import_status not in allowed_result_statuses:
            raise ValueError(
                "result_import_status violates the released lifecycle transition matrix"
            )

        if self.result_import_status == "official_imported":
            if self.result_source_kind != "official_imported":
                raise ValueError(
                    "official result import requires result_source_kind=official_imported"
                )
            if self.result_authority_validity != "valid":
                raise ValueError(
                    "official result import requires result_authority_validity=valid"
                )
            if (
                self.result_import_ref is None
                or self.result_import_hash is None
                or self.result_import_ts is None
            ):
                raise ValueError(
                    "official result import requires result import ref/hash/timestamp binding"
                )
        elif self.result_import_status == "deferred":
            if self.result_authority_validity != "deferred":
                raise ValueError("deferred result import requires deferred authority validity")
            if self.result_source_kind == "official_imported":
                raise ValueError("deferred result import may not use official_imported source kind")
            if any(
                value is not None
                for value in (
                    self.result_import_ref,
                    self.result_import_hash,
                    self.result_import_ts,
                )
            ):
                raise ValueError("deferred result import may not include import ref/hash/timestamp")
        elif self.result_import_status == "not_imported":
            if self.result_authority_validity != "invalid":
                raise ValueError("not_imported result status requires invalid authority validity")
            if self.result_source_kind == "official_imported":
                raise ValueError("not_imported result status may not use official_imported source")
            if any(
                value is not None
                for value in (
                    self.result_import_ref,
                    self.result_import_hash,
                    self.result_import_ts,
                )
            ):
                raise ValueError(
                    "not_imported result status may not include import ref/hash/timestamp"
                )
        else:
            if self.result_source_kind != "official_imported":
                raise ValueError(
                    "import_failed status requires official_imported result source kind"
                )
            if self.result_authority_validity != "invalid":
                raise ValueError("import_failed status requires invalid result authority validity")
            if (
                self.result_import_ref is None
                or self.result_import_hash is None
                or self.result_import_ts is None
            ):
                raise ValueError("import_failed status requires import ref/hash/timestamp evidence")

        if self.submission_execution_status == "submitted_acknowledged":
            assert self.submission_receipt_ref is not None  # narrowed by prior validation
            _assert_identity_chain_binding(
                ref_value=self.submission_receipt_ref,
                ref_field_name="submission_receipt_ref",
                external_request_ref=self.external_request_ref,
                environment_ref=self.environment_ref,
                session_ref=self.session_ref,
                competition_scope_ref=self.competition_scope_ref,
            )
        if self.result_import_status in ("official_imported", "import_failed"):
            assert self.result_import_ref is not None  # narrowed by prior validation
            _assert_identity_chain_binding(
                ref_value=self.result_import_ref,
                ref_field_name="result_import_ref",
                external_request_ref=self.external_request_ref,
                environment_ref=self.environment_ref,
                session_ref=self.session_ref,
                competition_scope_ref=self.competition_scope_ref,
            )
        _assert_identity_chain_binding(
            ref_value=self.submission_payload_ref,
            ref_field_name="submission_payload_ref",
            external_request_ref=self.external_request_ref,
            environment_ref=self.environment_ref,
            session_ref=self.session_ref,
            competition_scope_ref=self.competition_scope_ref,
        )

        if self.submission_execution_status == "submitted_acknowledged":
            assert self.submission_receipt_ts is not None
            if self.submission_request_ts > self.submission_receipt_ts:
                raise ValueError(
                    "submission_request_ts may not exceed submission_receipt_ts for the same "
                    "request chain"
                )
        if self.result_import_status in ("official_imported", "import_failed"):
            assert self.submission_receipt_ts is not None
            assert self.result_import_ts is not None
            if self.submission_request_ts > self.submission_receipt_ts:
                raise ValueError(
                    "submission_request_ts may not exceed submission_receipt_ts for the same "
                    "request chain"
                )
            if self.submission_receipt_ts > self.result_import_ts:
                raise ValueError(
                    "submission_receipt_ts may not exceed result_import_ts for the same request "
                    "chain"
                )

        constraints = list(self.bounded_orchestration_constraint_register)
        if constraints != sorted(constraints):
            raise ValueError(
                "bounded_orchestration_constraint_register must be sorted lexicographically"
            )
        if len(constraints) != len(set(constraints)):
            raise ValueError(
                "bounded_orchestration_constraint_register must not contain duplicates"
            )
        if not set(_REQUIRED_BOUNDED_ORCHESTRATION_CONSTRAINTS).issubset(set(constraints)):
            raise ValueError(
                "bounded_orchestration_constraint_register must include all required constraints"
            )

        _assert_no_forbidden_terms(
            value=self.submission_result_posture,
            field_name="submission_result_posture",
            terms=_FORBIDDEN_AUTHORITY_TERMS + _FORBIDDEN_NECESSITY_TERMS,
        )
        _assert_no_forbidden_terms(
            value=self.submission_result_summary,
            field_name="submission_result_summary",
            terms=_FORBIDDEN_AUTHORITY_TERMS + _FORBIDDEN_NECESSITY_TERMS,
        )
        for assertion in self.deferred_authority_assertions:
            _assert_no_forbidden_terms(
                value=assertion,
                field_name="deferred_authority_assertions",
                terms=_FORBIDDEN_DEFERRED_ASSERTION_TERMS,
            )
            if not assertion.endswith("_deferred"):
                raise ValueError("deferred_authority_assertions entries must end with '_deferred'")

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("submission_execution_id", None)
        expected_id = compute_adeu_arc_submission_execution_id(payload_without_id)
        if self.submission_execution_id != expected_id:
            raise ValueError(
                "submission_execution_id must match canonical full payload hash identity"
            )
        return self


def compute_adeu_arc_submission_execution_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA)
    canonical_payload.pop("submission_execution_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_submit_{digest[:32]}"


def canonicalize_adeu_arc_submission_execution_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcSubmissionExecutionRecord.model_validate(payload).model_dump(mode="json")


def materialize_adeu_arc_submission_execution_payload(
    payload_without_submission_execution_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_submission_execution_id)
    payload.setdefault("schema", ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA)
    payload["submission_execution_id"] = compute_adeu_arc_submission_execution_id(payload)
    return canonicalize_adeu_arc_submission_execution_payload(payload)


def derive_v42f_arc_submission_execution_record(
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
    scorecard_manifest: dict[str, Any],
    scorecard_manifest_ref: str,
    environment_ref: str,
    session_ref: str,
    competition_scope_ref: str,
    model_id: str,
    run_id: str,
    submission_authorization_status: SubmissionAuthorizationStatus,
    submission_authorization_source_kind: ScorecardSourceKind,
    submission_authorization_validity: AuthorizationValidity,
    submission_authorization_basis_refs: list[str],
    submission_execution_status: SubmissionExecutionStatus,
    submission_transport_profile: str,
    external_request_ref: str,
    submission_payload_ref: str,
    submission_payload_hash: str,
    submission_request_ts: int,
    submission_receipt_ref: str | None,
    submission_receipt_hash: str | None,
    submission_receipt_ts: int | None,
    result_import_status: ResultImportStatus,
    result_source_kind: ScorecardSourceKind,
    result_authority_validity: ResultAuthorityValidity,
    result_authority_basis_refs: list[str],
    result_import_ref: str | None,
    result_import_hash: str | None,
    result_import_ts: int | None,
    lifecycle_transition_matrix_ref: str,
    submission_result_posture: str,
    submission_result_summary: str,
    bounded_orchestration_constraint_register: list[BoundedOrchestrationConstraint],
    settlement_posture_carry: dict[str, Any],
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
    if scorecard_manifest["task_packet_id"] != task_packet_id:
        raise ValueError("scorecard_manifest must bind to released task_packet_id")

    if local_eval_record["task_packet_ref"] != task_packet_ref:
        raise ValueError("local_eval_record must preserve released task_packet_ref")
    if local_eval_record["observation_frame_ref"] != observation_frame_ref:
        raise ValueError("local_eval_record must preserve released observation_frame_ref")
    if local_eval_record["hypothesis_frame_ref"] != hypothesis_frame_ref:
        raise ValueError("local_eval_record must preserve released hypothesis_frame_ref")
    if local_eval_record["action_proposal_ref"] != action_proposal_ref:
        raise ValueError("local_eval_record must preserve released action_proposal_ref")
    if local_eval_record["rollout_trace_ref"] != rollout_trace_ref:
        raise ValueError("local_eval_record must preserve released rollout_trace_ref")

    if scorecard_manifest["task_packet_ref"] != task_packet_ref:
        raise ValueError("scorecard_manifest must preserve released task_packet_ref")
    if scorecard_manifest["observation_frame_ref"] != observation_frame_ref:
        raise ValueError("scorecard_manifest must preserve released observation_frame_ref")
    if scorecard_manifest["hypothesis_frame_ref"] != hypothesis_frame_ref:
        raise ValueError("scorecard_manifest must preserve released hypothesis_frame_ref")
    if scorecard_manifest["action_proposal_ref"] != action_proposal_ref:
        raise ValueError("scorecard_manifest must preserve released action_proposal_ref")
    if scorecard_manifest["rollout_trace_ref"] != rollout_trace_ref:
        raise ValueError("scorecard_manifest must preserve released rollout_trace_ref")
    if scorecard_manifest["local_eval_record_ref"] != local_eval_record_ref:
        raise ValueError("scorecard_manifest must preserve released local_eval_record_ref")
    if scorecard_manifest["model_id"] != model_id:
        raise ValueError("model_id must match released scorecard manifest lineage")
    if scorecard_manifest["run_id"] != run_id:
        raise ValueError("run_id must match released scorecard manifest lineage")
    if scorecard_manifest["environment_ref"] != environment_ref:
        raise ValueError("environment_ref must match released scorecard manifest lineage")
    if scorecard_manifest["session_ref"] != session_ref:
        raise ValueError("session_ref must match released scorecard manifest lineage")
    if scorecard_manifest["competition_scope_ref"] != competition_scope_ref:
        raise ValueError("competition_scope_ref must match released scorecard manifest lineage")

    scorecard_source_kind = scorecard_manifest["scorecard_source_kind"]
    if submission_authorization_source_kind != scorecard_source_kind:
        raise ValueError(
            "submission_authorization_source_kind must match released scorecard_source_kind"
        )
    if scorecard_source_kind != "official_imported":
        if submission_authorization_status == "authorized":
            raise ValueError(
                "authorized submission is forbidden unless released scorecard_source_kind is "
                "official_imported"
            )
        if submission_execution_status in _SUBMITTED_EXECUTION_STATUSES:
            raise ValueError(
                "submitted execution statuses are forbidden for non-official scorecard source "
                "kinds"
            )
        if result_import_status == "official_imported":
            raise ValueError("official result import is forbidden for non-official scorecards")

    if scorecard_manifest_ref not in submission_authorization_basis_refs:
        raise ValueError(
            "submission_authorization_basis_refs must include released scorecard_manifest_ref"
        )
    if V42F_V94_CONTRACT_SOURCE not in submission_authorization_basis_refs:
        raise ValueError(
            "submission_authorization_basis_refs must include the released v42f contract source"
        )

    if result_import_status in ("official_imported", "import_failed"):
        if scorecard_manifest_ref not in result_authority_basis_refs:
            raise ValueError(
                "result_authority_basis_refs must include released scorecard_manifest_ref"
            )

    payload_without_id: dict[str, Any] = {
        "schema": ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA,
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
        "scorecard_manifest_id": scorecard_manifest["scorecard_manifest_id"],
        "scorecard_manifest_ref": scorecard_manifest_ref,
        "environment_ref": environment_ref,
        "session_ref": session_ref,
        "competition_scope_ref": competition_scope_ref,
        "model_id": model_id,
        "run_id": run_id,
        "submission_authorization_status": submission_authorization_status,
        "submission_authorization_source_kind": submission_authorization_source_kind,
        "submission_authorization_validity": submission_authorization_validity,
        "submission_authorization_basis_refs": deepcopy(submission_authorization_basis_refs),
        "submission_execution_status": submission_execution_status,
        "submission_transport_profile": submission_transport_profile,
        "external_request_ref": external_request_ref,
        "submission_payload_ref": submission_payload_ref,
        "submission_payload_hash": submission_payload_hash,
        "submission_request_ts": submission_request_ts,
        "submission_receipt_ref": submission_receipt_ref,
        "submission_receipt_hash": submission_receipt_hash,
        "submission_receipt_ts": submission_receipt_ts,
        "result_import_status": result_import_status,
        "result_source_kind": result_source_kind,
        "result_authority_validity": result_authority_validity,
        "result_authority_basis_refs": deepcopy(result_authority_basis_refs),
        "result_import_ref": result_import_ref,
        "result_import_hash": result_import_hash,
        "result_import_ts": result_import_ts,
        "lifecycle_transition_matrix_ref": lifecycle_transition_matrix_ref,
        "submission_result_posture": submission_result_posture,
        "submission_result_summary": submission_result_summary,
        "bounded_orchestration_constraint_register": deepcopy(
            bounded_orchestration_constraint_register
        ),
        "settlement_posture_carry": deepcopy(settlement_posture_carry),
        "deferred_authority_assertions": deepcopy(deferred_authority_assertions),
        "evidence_refs": deepcopy(evidence_refs),
    }
    return materialize_adeu_arc_submission_execution_payload(payload_without_id)
