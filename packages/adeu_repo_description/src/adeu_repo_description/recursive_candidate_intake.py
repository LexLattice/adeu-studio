from __future__ import annotations

import re
from copy import deepcopy
from typing import Any, Literal

from pydantic import Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .arc_series_cartography import (
    SourceStatus,
    _CartographyBase,
    _non_empty,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)

REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA = "repo_recursive_candidate_intake_record@1"
REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA = "repo_candidate_source_register@1"
REPO_CANDIDATE_NON_ADOPTION_GUARDRAIL_SCHEMA = "repo_candidate_non_adoption_guardrail@1"

CandidateSourceKind = Literal[
    "planning_doc",
    "architecture_doc",
    "support_doc",
    "review_input",
    "closeout_doc",
    "evidence_artifact",
    "schema_file",
    "fixture_file",
    "operator_turn",
    "transcript_artifact",
    "model_output",
    "repo_observation",
    "external_artifact",
]
CandidateAuthorityLayer = Literal[
    "lock",
    "architecture",
    "planning",
    "support",
    "schema",
    "fixture",
    "closeout_evidence",
]
CandidateSourcePresencePosture = Literal[
    "present",
    "missing_expected_support_artifact",
    "not_uploaded_in_review_snapshot",
    "generated_later",
    "external_unavailable",
    "operator_turn_not_committed",
]
CandidateOriginClass = Literal[
    "internal_reasoning_residue",
    "external_artifact",
    "operator_turn",
    "model_output",
    "support_doc",
    "review_feedback",
    "repo_observation",
    "planning_pressure",
]
CandidateIntakePosture = Literal[
    "intake_candidate",
    "intake_duplicate",
    "intake_rejected_out_of_scope",
    "intake_deferred_to_later_family",
    "intake_requires_v70_review",
    "intake_superseded",
    "intake_unknown_needs_review",
]
PrimaryOdeuLane = Literal["ontological", "deontic", "epistemic", "utility", "mixed"]
OdeuLane = Literal["ontological", "deontic", "epistemic", "utility"]
CandidateEquivalencePosture = Literal[
    "self_identity_only",
    "equivalent_to_existing_candidate",
    "related_not_equivalent",
    "unknown_needs_review",
]
AdmissibleRole = Literal[
    "support_input",
    "schema_candidate",
    "planning_pressure",
    "review_input",
    "evidence_review_request",
    "future_family_candidate",
    "product_projection_candidate",
    "operator_ingress_binding",
]
ForbiddenRole = Literal[
    "lock_authority",
    "released_schema",
    "ratified_decision",
    "implementation_task",
    "commit_release_authority",
    "product_authorization",
    "dispatch_authority",
    "self_validation",
    "transcript_truth",
]
RequiredNextReviewSurface = Literal[
    "v70_evidence_classification",
    "v70_adversarial_review",
    "future_family_review",
    "none_yet_deferred",
]
EventualFamilyHint = Literal[
    "v71_ratification",
    "v72_integration_review",
    "v73_outcome_review",
    "v74_operator_projection_review",
    "v75_dispatch_review",
    "v43_external_contest_branch",
    "none",
]

_FORBIDDEN_INTAKE_AUTHORITY_RE = re.compile(
    r"\b(authorizes?|adopts?|ratifies?|implements?|releases?|dispatches?|commits?|merges?|selects?)\b",
    re.IGNORECASE,
)
_FORBIDDEN_EVIDENCE_VERDICT_RE = re.compile(
    r"\b(evidence classification|classification verdict|evidence verdict|proves?|proved)\b",
    re.IGNORECASE,
)


def _non_authority_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    if _FORBIDDEN_INTAKE_AUTHORITY_RE.search(normalized):
        raise ValueError(f"{field_name} may not carry adoption, selection, or release authority")
    if _FORBIDDEN_EVIDENCE_VERDICT_RE.search(normalized):
        raise ValueError(f"{field_name} may not carry evidence classification verdict language")
    return normalized


def _require_forbidden_roles(
    *,
    forbidden_roles: set[ForbiddenRole],
    required_roles: set[ForbiddenRole],
    context: str,
) -> None:
    missing = sorted(required_roles - forbidden_roles)
    if missing:
        raise ValueError(f"{context} forbidden_roles must include {missing}")


def _validate_role_guardrail_requirements(row: RepoCandidateRoleGuardrailRow) -> None:
    forbidden_roles = set(row.forbidden_roles)
    admissible_roles = set(row.admissible_roles)
    if "schema_candidate" in admissible_roles:
        _require_forbidden_roles(
            forbidden_roles=forbidden_roles,
            required_roles={"released_schema"},
            context="schema_candidate",
        )
    if "product_projection_candidate" in admissible_roles:
        _require_forbidden_roles(
            forbidden_roles=forbidden_roles,
            required_roles={"product_authorization"},
            context="product_projection_candidate",
        )
    if "future_family_candidate" in admissible_roles:
        _require_forbidden_roles(
            forbidden_roles=forbidden_roles,
            required_roles={"implementation_task", "lock_authority"},
            context="future_family_candidate",
        )


class RepoCandidateSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    integration_note: str

    @model_validator(mode="after")
    def _validate_source(self) -> RepoCandidateSourceRow:
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self,
            "integration_note",
            _non_authority_note(self.integration_note, field_name="integration_note"),
        )
        if (
            self.source_status == "integrated_shaping_source"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("integrated candidate source rows must have presence posture present")
        if self.source_kind in {"support_doc", "review_input"} and self.authority_layer in {
            "lock",
            "schema",
        }:
            raise ValueError(
                "support and review sources cannot be lock or released schema authority"
            )
        if self.source_kind == "planning_doc" and self.authority_layer == "lock":
            raise ValueError("planning selector sources cannot be marked as lock authority")
        if (
            self.source_kind
            in {
                "operator_turn",
                "transcript_artifact",
                "model_output",
            }
            and self.authority_layer == "lock"
        ):
            raise ValueError("operator, transcript, and model sources are not lock authority")
        if self.source_ref.startswith("docs/support/") and self.authority_layer == "lock":
            raise ValueError("support-layer source cannot be marked as lock authority")
        return self


class RepoCandidateIntakeRow(_CartographyBase):
    candidate_ref: str
    candidate_label: str
    origin_class: CandidateOriginClass
    intake_posture: CandidateIntakePosture
    primary_odeu_lane: PrimaryOdeuLane
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    equivalence_posture: CandidateEquivalencePosture
    intake_note: str

    @model_validator(mode="after")
    def _validate_candidate(self) -> RepoCandidateIntakeRow:
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "candidate_label",
            _non_empty(self.candidate_label, field_name="candidate_label"),
        )
        object.__setattr__(
            self,
            "odeu_lanes",
            _sorted_unique(self.odeu_lanes, field_name="odeu_lanes"),
        )
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "intake_note",
            _non_authority_note(self.intake_note, field_name="intake_note"),
        )
        if self.primary_odeu_lane == "mixed" and len(self.odeu_lanes) < 2:
            raise ValueError("primary_odeu_lane=mixed requires at least two odeu_lanes")
        if self.primary_odeu_lane != "mixed" and self.primary_odeu_lane not in self.odeu_lanes:
            raise ValueError("primary_odeu_lane must be present in odeu_lanes")
        if (
            self.intake_posture == "intake_duplicate"
            and self.equivalence_posture != "equivalent_to_existing_candidate"
        ):
            raise ValueError(
                "duplicate candidates require equivalent_to_existing_candidate posture"
            )
        return self


class RepoCandidateRoleGuardrailRow(_CartographyBase):
    candidate_ref: str
    admissible_roles: list[AdmissibleRole] = Field(min_length=1)
    forbidden_roles: list[ForbiddenRole] = Field(min_length=1)
    required_next_review_surface: RequiredNextReviewSurface
    eventual_family_hint: EventualFamilyHint
    non_adoption_guardrail: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> RepoCandidateRoleGuardrailRow:
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "admissible_roles",
            _sorted_unique(self.admissible_roles, field_name="admissible_roles"),
        )
        object.__setattr__(
            self,
            "forbidden_roles",
            _sorted_unique(self.forbidden_roles, field_name="forbidden_roles"),
        )
        object.__setattr__(
            self,
            "non_adoption_guardrail",
            _non_authority_note(self.non_adoption_guardrail, field_name="non_adoption_guardrail"),
        )
        _validate_role_guardrail_requirements(self)
        return self


def _candidate_source_ref_set(source_rows: list[RepoCandidateSourceRow]) -> set[str]:
    return {row.source_ref for row in source_rows}


def _candidate_ref_set(candidate_rows: list[RepoCandidateIntakeRow]) -> set[str]:
    return {row.candidate_ref for row in candidate_rows}


def _require_known_refs(
    refs: list[str],
    *,
    known_refs: set[str],
    field_name: str,
) -> None:
    missing = sorted(set(refs) - known_refs)
    if missing:
        raise ValueError(f"{field_name} must reference known rows: {missing}")


def _validate_candidate_intake_bundle(
    *,
    source_rows: list[RepoCandidateSourceRow],
    candidate_rows: list[RepoCandidateIntakeRow],
    role_guardrail_rows: list[RepoCandidateRoleGuardrailRow],
) -> None:
    known_sources = _candidate_source_ref_set(source_rows)
    candidate_refs = _candidate_ref_set(candidate_rows)
    role_rows_by_candidate = {row.candidate_ref: row for row in role_guardrail_rows}
    source_rows_by_ref = {row.source_ref: row for row in source_rows}

    if set(role_rows_by_candidate) != candidate_refs:
        missing_roles = sorted(candidate_refs - set(role_rows_by_candidate))
        orphan_roles = sorted(set(role_rows_by_candidate) - candidate_refs)
        raise ValueError(
            "role_guardrail_rows must be one-to-one with candidate_rows: "
            f"missing_roles={missing_roles}, orphan_roles={orphan_roles}"
        )

    for row in candidate_rows:
        _require_known_refs(
            row.source_refs,
            known_refs=known_sources,
            field_name="candidate source_refs",
        )
        guardrail = role_rows_by_candidate[row.candidate_ref]
        forbidden_roles = set(guardrail.forbidden_roles)
        if (
            guardrail.eventual_family_hint != "none"
            and guardrail.required_next_review_surface == "none_yet_deferred"
        ):
            raise ValueError("eventual family hints require a review intermediary")
        if (
            row.intake_posture == "intake_candidate"
            and guardrail.required_next_review_surface == "none_yet_deferred"
        ):
            raise ValueError("intake_candidate rows require a next review surface")
        if row.origin_class == "model_output":
            _require_forbidden_roles(
                forbidden_roles=forbidden_roles,
                required_roles={"ratified_decision", "self_validation"},
                context="model_output candidate",
            )
        if row.origin_class == "operator_turn":
            _require_forbidden_roles(
                forbidden_roles=forbidden_roles,
                required_roles={"lock_authority", "transcript_truth"},
                context="operator_turn candidate",
            )
        source_kinds = {source_rows_by_ref[ref].source_kind for ref in row.source_refs}
        if row.origin_class == "model_output" and "model_output" not in source_kinds:
            raise ValueError("model_output candidates require a model_output source row")
        if row.origin_class == "operator_turn" and not (
            {"operator_turn", "transcript_artifact"} & source_kinds
        ):
            raise ValueError("operator_turn candidates require operator or transcript source rows")


class RepoRecursiveCandidateIntakeRecord(_CartographyBase):
    schema: Literal["repo_recursive_candidate_intake_record@1"] = (
        REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA
    )
    intake_id: str
    snapshot_id: str
    source_set_id: str
    coverage_horizon: str
    source_rows: list[RepoCandidateSourceRow] = Field(min_length=1)
    candidate_rows: list[RepoCandidateIntakeRow] = Field(min_length=1)
    role_guardrail_rows: list[RepoCandidateRoleGuardrailRow] = Field(min_length=1)
    non_adoption_summary: str

    @model_validator(mode="after")
    def _validate_intake_record(self) -> RepoRecursiveCandidateIntakeRecord:
        object.__setattr__(self, "intake_id", _non_empty(self.intake_id, field_name="intake_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self, "source_set_id", _non_empty(self.source_set_id, field_name="source_set_id")
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
            "candidate_rows",
            _sorted_unique_by_ref(
                self.candidate_rows, attr="candidate_ref", field_name="candidate_rows"
            ),
        )
        object.__setattr__(
            self,
            "role_guardrail_rows",
            _sorted_unique_by_ref(
                self.role_guardrail_rows,
                attr="candidate_ref",
                field_name="role_guardrail_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_adoption_summary",
            _non_authority_note(self.non_adoption_summary, field_name="non_adoption_summary"),
        )
        _validate_candidate_intake_bundle(
            source_rows=self.source_rows,
            candidate_rows=self.candidate_rows,
            role_guardrail_rows=self.role_guardrail_rows,
        )
        expected_id = compute_repo_recursive_candidate_intake_id(self.model_dump(mode="json"))
        if self.intake_id != expected_id:
            raise ValueError("intake_id must match canonical full payload hash identity")
        return self


class RepoCandidateSourceRegister(_CartographyBase):
    schema: Literal["repo_candidate_source_register@1"] = REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA
    source_register_id: str
    intake_id: str
    snapshot_id: str
    source_rows: list[RepoCandidateSourceRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_source_register(self) -> RepoCandidateSourceRegister:
        object.__setattr__(
            self,
            "source_register_id",
            _non_empty(self.source_register_id, field_name="source_register_id"),
        )
        object.__setattr__(self, "intake_id", _non_empty(self.intake_id, field_name="intake_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        return self


class RepoCandidateNonAdoptionGuardrail(_CartographyBase):
    schema: Literal["repo_candidate_non_adoption_guardrail@1"] = (
        REPO_CANDIDATE_NON_ADOPTION_GUARDRAIL_SCHEMA
    )
    guardrail_register_id: str
    intake_id: str
    snapshot_id: str
    role_guardrail_rows: list[RepoCandidateRoleGuardrailRow] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_guardrail_register(self) -> RepoCandidateNonAdoptionGuardrail:
        object.__setattr__(
            self,
            "guardrail_register_id",
            _non_empty(self.guardrail_register_id, field_name="guardrail_register_id"),
        )
        object.__setattr__(self, "intake_id", _non_empty(self.intake_id, field_name="intake_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "role_guardrail_rows",
            _sorted_unique_by_ref(
                self.role_guardrail_rows,
                attr="candidate_ref",
                field_name="role_guardrail_rows",
            ),
        )
        return self


def compute_repo_recursive_candidate_intake_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA)
    canonical_payload.pop("intake_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_recursive_candidate_intake_{digest[:24]}"


def materialize_repo_recursive_candidate_intake_payload(
    payload_without_intake_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_intake_id)
    payload.setdefault("schema", REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA)
    payload["intake_id"] = compute_repo_recursive_candidate_intake_id(payload)
    return RepoRecursiveCandidateIntakeRecord.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_recursive_candidate_intake_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoRecursiveCandidateIntakeRecord.model_validate(payload).model_dump(mode="json")
