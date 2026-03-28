from __future__ import annotations

import re
from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

ADEU_ARC_OBSERVATION_FRAME_SCHEMA = "adeu_arc_observation_frame@1"
ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA = "adeu_arc_hypothesis_frame@1"
V42B_V90_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS90.md#v42b_arc_observation_hypothesis_contract@1"
)

ArcEnvironmentAuthority = Literal["official_arc_toolkit"]
ArcModePosture = Literal["local_offline"]
ObservationMode = Literal["direct", "derived"]
ObservationResolutionPosture = Literal["resolved", "unresolved"]
HypothesisClaimPosture = Literal["observed", "inferred", "conjectural", "blocked"]
DeonticClass = Literal["allowed", "deferred", "forbidden"]
CoverageBasis = Literal["required_dimension_set"]
WorkingHypothesisPostureKind = Literal["non_committing_investigation"]
UtilityPressureKind = Literal[
    "task_success_alignment",
    "search_cost_pressure",
    "ambiguity_pressure",
]
UtilityPressureLevel = Literal["low", "medium", "high"]

_OBSERVATION_DIMENSIONS: tuple[str, ...] = (
    "ontology_register",
    "entity_inventory",
    "relation_inventory",
    "state_partition_register",
    "observation_entries",
    "unresolved_observation_entries",
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_FORBIDDEN_DERIVED_TERMS: tuple[str, ...] = (
    "governing rule",
    "candidate transform",
    "task rule",
    "intended transform",
    "should transform",
    "solution rule",
    "hypothesis",
)
_FORBIDDEN_IMPOSSIBILITY_TERMS: tuple[str, ...] = (
    "impossible",
    "cannot exist",
    "no solution",
    "unsat",
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
            raise ValueError(f"{field_name} may not contain forbidden interpretation term '{term}'")


class ArcOntologyUnit(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    unit_id: str
    unit_kind: str
    summary: str

    @model_validator(mode="after")
    def _validate_unit(self) -> ArcOntologyUnit:
        object.__setattr__(
            self, "unit_id", _assert_non_empty_text(self.unit_id, field_name="unit_id")
        )
        object.__setattr__(
            self,
            "unit_kind",
            _assert_non_empty_text(self.unit_kind, field_name="unit_kind"),
        )
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        return self


class ArcEntityRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    entity_id: str
    entity_kind: str
    source_observation_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entity(self) -> ArcEntityRecord:
        object.__setattr__(
            self, "entity_id", _assert_non_empty_text(self.entity_id, field_name="entity_id")
        )
        object.__setattr__(
            self,
            "entity_kind",
            _assert_non_empty_text(self.entity_kind, field_name="entity_kind"),
        )
        object.__setattr__(
            self,
            "source_observation_refs",
            _assert_sorted_unique(
                self.source_observation_refs,
                field_name="source_observation_refs",
            ),
        )
        return self


class ArcRelationRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    relation_id: str
    relation_kind: str
    endpoint_entity_ids: list[str] = Field(min_length=2)

    @model_validator(mode="after")
    def _validate_relation(self) -> ArcRelationRecord:
        object.__setattr__(
            self,
            "relation_id",
            _assert_non_empty_text(self.relation_id, field_name="relation_id"),
        )
        object.__setattr__(
            self,
            "relation_kind",
            _assert_non_empty_text(self.relation_kind, field_name="relation_kind"),
        )
        object.__setattr__(
            self,
            "endpoint_entity_ids",
            _assert_sorted_unique(
                self.endpoint_entity_ids,
                field_name="endpoint_entity_ids",
            ),
        )
        return self


class ArcStatePartitionRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    partition_id: str
    partition_kind: str
    covered_cell_ref_hash: str

    @model_validator(mode="after")
    def _validate_partition(self) -> ArcStatePartitionRecord:
        object.__setattr__(
            self,
            "partition_id",
            _assert_non_empty_text(self.partition_id, field_name="partition_id"),
        )
        object.__setattr__(
            self,
            "partition_kind",
            _assert_non_empty_text(self.partition_kind, field_name="partition_kind"),
        )
        object.__setattr__(
            self,
            "covered_cell_ref_hash",
            _assert_sha256_hex(
                self.covered_cell_ref_hash,
                field_name="covered_cell_ref_hash",
            ),
        )
        return self


class ArcOntologyUncertainty(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    uncertainty_id: str
    summary: str

    @model_validator(mode="after")
    def _validate_uncertainty(self) -> ArcOntologyUncertainty:
        object.__setattr__(
            self,
            "uncertainty_id",
            _assert_non_empty_text(self.uncertainty_id, field_name="uncertainty_id"),
        )
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        return self


class ArcObservationEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    observation_id: str
    observation_mode: ObservationMode
    structural_kind: str
    summary: str
    source_refs: list[str] = Field(min_length=1)
    evidence_refs: list[str] = Field(min_length=1)
    derived_from_observation_ids: list[str] = Field(default_factory=list)
    resolution_posture: ObservationResolutionPosture

    @model_validator(mode="after")
    def _validate_entry(self) -> ArcObservationEntry:
        object.__setattr__(
            self,
            "observation_id",
            _assert_non_empty_text(self.observation_id, field_name="observation_id"),
        )
        object.__setattr__(
            self,
            "structural_kind",
            _assert_non_empty_text(self.structural_kind, field_name="structural_kind"),
        )
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        object.__setattr__(
            self, "source_refs", _assert_sorted_unique(self.source_refs, field_name="source_refs")
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )
        object.__setattr__(
            self,
            "derived_from_observation_ids",
            _assert_sorted_unique(
                self.derived_from_observation_ids,
                field_name="derived_from_observation_ids",
            ),
        )
        if self.observation_mode == "derived":
            if not self.derived_from_observation_ids:
                raise ValueError("derived observations require derived_from_observation_ids")
            _assert_no_forbidden_terms(
                value=self.summary,
                field_name="summary",
                terms=_FORBIDDEN_DERIVED_TERMS,
            )
        elif self.derived_from_observation_ids:
            raise ValueError("direct observations may not include derived_from_observation_ids")
        return self


class AdeuArcObservationFrame(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_OBSERVATION_FRAME_SCHEMA] = ADEU_ARC_OBSERVATION_FRAME_SCHEMA
    observation_frame_id: str
    task_packet_id: str
    task_packet_ref: str
    environment_authority: ArcEnvironmentAuthority = "official_arc_toolkit"
    mode_posture: ArcModePosture = "local_offline"
    game_ref: str
    session_ref: str
    ontology_register: list[ArcOntologyUnit] = Field(min_length=1)
    entity_inventory: list[ArcEntityRecord] = Field(min_length=1)
    relation_inventory: list[ArcRelationRecord] = Field(min_length=1)
    state_partition_register: list[ArcStatePartitionRecord] = Field(min_length=1)
    ontology_uncertainty_register: list[ArcOntologyUncertainty]
    observation_entries: list[ArcObservationEntry] = Field(min_length=1)
    unresolved_observation_entries: list[str]
    decomposition_coverage: float = Field(ge=0.0, le=1.0)
    coverage_basis: CoverageBasis = "required_dimension_set"
    required_dimension_set: list[str] = Field(min_length=1)
    missing_dimension_register: list[str]

    @model_validator(mode="after")
    def _validate_frame(self) -> AdeuArcObservationFrame:
        object.__setattr__(
            self,
            "observation_frame_id",
            _assert_non_empty_text(self.observation_frame_id, field_name="observation_frame_id"),
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
            self, "game_ref", _assert_non_empty_text(self.game_ref, field_name="game_ref")
        )
        object.__setattr__(
            self, "session_ref", _assert_non_empty_text(self.session_ref, field_name="session_ref")
        )
        object.__setattr__(
            self,
            "required_dimension_set",
            _assert_sorted_unique(
                self.required_dimension_set,
                field_name="required_dimension_set",
            ),
        )
        object.__setattr__(
            self,
            "missing_dimension_register",
            _assert_sorted_unique(
                self.missing_dimension_register,
                field_name="missing_dimension_register",
            ),
        )

        required_set = set(self.required_dimension_set)
        allowed_set = set(_OBSERVATION_DIMENSIONS)
        if not required_set.issubset(allowed_set):
            raise ValueError("required_dimension_set contains unsupported decomposition dimension")
        missing_set = set(self.missing_dimension_register)
        if not missing_set.issubset(required_set):
            raise ValueError(
                "missing_dimension_register must be a subset of required_dimension_set"
            )
        expected_coverage = (len(required_set) - len(missing_set)) / len(required_set)
        if abs(self.decomposition_coverage - expected_coverage) > 1e-9:
            raise ValueError(
                "decomposition_coverage must match denominator-bound required-vs-missing dimensions"
            )

        entries_by_id = {entry.observation_id: entry for entry in self.observation_entries}
        if len(entries_by_id) != len(self.observation_entries):
            raise ValueError("observation_entries must use unique observation_id values")
        for entry in self.observation_entries:
            if entry.observation_mode == "derived":
                unknown = [
                    ref for ref in entry.derived_from_observation_ids if ref not in entries_by_id
                ]
                if unknown:
                    raise ValueError("derived observation references unknown observation ids")
        expected_unresolved = sorted(
            entry.observation_id
            for entry in self.observation_entries
            if entry.resolution_posture == "unresolved"
        )
        if self.unresolved_observation_entries != expected_unresolved:
            raise ValueError(
                "unresolved_observation_entries must exactly match unresolved observation ids"
            )

        payload_without_id = self.model_dump(mode="json", exclude_none=False)
        payload_without_id.pop("observation_frame_id", None)
        expected_id = compute_adeu_arc_observation_frame_id(payload_without_id)
        if self.observation_frame_id != expected_id:
            raise ValueError("observation_frame_id must match canonical full payload hash identity")
        return self


class ArcHypothesisCandidate(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    hypothesis_id: str
    summary: str
    supporting_observation_refs: list[str] = Field(min_length=1)
    claim_posture: HypothesisClaimPosture

    @model_validator(mode="after")
    def _validate_candidate(self) -> ArcHypothesisCandidate:
        object.__setattr__(
            self,
            "hypothesis_id",
            _assert_non_empty_text(self.hypothesis_id, field_name="hypothesis_id"),
        )
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        object.__setattr__(
            self,
            "supporting_observation_refs",
            _assert_sorted_unique(
                self.supporting_observation_refs,
                field_name="supporting_observation_refs",
            ),
        )
        _assert_no_forbidden_terms(
            value=self.summary,
            field_name="summary",
            terms=_FORBIDDEN_IMPOSSIBILITY_TERMS,
        )
        return self


class ArcAmbiguityRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    ambiguity_id: str
    summary: str
    related_hypothesis_ids: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_ambiguity(self) -> ArcAmbiguityRecord:
        object.__setattr__(
            self,
            "ambiguity_id",
            _assert_non_empty_text(self.ambiguity_id, field_name="ambiguity_id"),
        )
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        object.__setattr__(
            self,
            "related_hypothesis_ids",
            _assert_sorted_unique(
                self.related_hypothesis_ids,
                field_name="related_hypothesis_ids",
            ),
        )
        return self


class ArcClaimPostureRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    hypothesis_id: str
    claim_posture: HypothesisClaimPosture
    rationale: str

    @model_validator(mode="after")
    def _validate_posture(self) -> ArcClaimPostureRecord:
        object.__setattr__(
            self,
            "hypothesis_id",
            _assert_non_empty_text(self.hypothesis_id, field_name="hypothesis_id"),
        )
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        return self


class ArcDeonticAdmissibilityRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    hypothesis_id: str
    deontic_class: DeonticClass
    rationale: str
    source_legal_action_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_deontic(self) -> ArcDeonticAdmissibilityRecord:
        object.__setattr__(
            self,
            "hypothesis_id",
            _assert_non_empty_text(self.hypothesis_id, field_name="hypothesis_id"),
        )
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        object.__setattr__(
            self,
            "source_legal_action_refs",
            _assert_sorted_unique(
                self.source_legal_action_refs,
                field_name="source_legal_action_refs",
            ),
        )
        return self


class ArcUtilityPressureRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    pressure_id: str
    pressure_kind: UtilityPressureKind
    pressure_level: UtilityPressureLevel
    rationale: str

    @model_validator(mode="after")
    def _validate_pressure(self) -> ArcUtilityPressureRecord:
        object.__setattr__(
            self,
            "pressure_id",
            _assert_non_empty_text(self.pressure_id, field_name="pressure_id"),
        )
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        return self


class ArcWorkingHypothesisPosture(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    posture_kind: WorkingHypothesisPostureKind = "non_committing_investigation"
    active_hypothesis_ids: list[str] = Field(min_length=1)
    action_commitment_allowed: bool = False

    @model_validator(mode="after")
    def _validate_working_posture(self) -> ArcWorkingHypothesisPosture:
        object.__setattr__(
            self,
            "active_hypothesis_ids",
            _assert_sorted_unique(
                self.active_hypothesis_ids,
                field_name="active_hypothesis_ids",
            ),
        )
        if self.action_commitment_allowed:
            raise ValueError("working_hypothesis_posture may not allow action commitment in V42-B")
        return self


class AdeuArcHypothesisFrame(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA] = ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA
    hypothesis_frame_id: str
    task_packet_id: str
    task_packet_ref: str
    observation_frame_id: str
    observation_frame_ref: str
    hypothesis_register: list[ArcHypothesisCandidate] = Field(min_length=1)
    ambiguity_register: list[ArcAmbiguityRecord]
    claim_posture_register: list[ArcClaimPostureRecord] = Field(min_length=1)
    deontic_admissibility_register: list[ArcDeonticAdmissibilityRecord] = Field(min_length=1)
    utility_pressure_register: list[ArcUtilityPressureRecord] = Field(min_length=1)
    working_hypothesis_posture: ArcWorkingHypothesisPosture

    @model_validator(mode="after")
    def _validate_frame(self) -> AdeuArcHypothesisFrame:
        object.__setattr__(
            self,
            "hypothesis_frame_id",
            _assert_non_empty_text(self.hypothesis_frame_id, field_name="hypothesis_frame_id"),
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

        hypothesis_ids = [entry.hypothesis_id for entry in self.hypothesis_register]
        if hypothesis_ids != sorted(hypothesis_ids):
            raise ValueError("hypothesis_register must be sorted by hypothesis_id")
        if len(hypothesis_ids) != len(set(hypothesis_ids)):
            raise ValueError("hypothesis_register must use unique hypothesis_id values")
        hypothesis_id_set = set(hypothesis_ids)

        claim_ids = [entry.hypothesis_id for entry in self.claim_posture_register]
        if set(claim_ids) != hypothesis_id_set:
            raise ValueError("claim_posture_register must cover every hypothesis_id exactly once")
        if len(claim_ids) != len(set(claim_ids)):
            raise ValueError("claim_posture_register must not duplicate hypothesis_id")

        deontic_ids = [entry.hypothesis_id for entry in self.deontic_admissibility_register]
        if set(deontic_ids) != hypothesis_id_set:
            raise ValueError(
                "deontic_admissibility_register must cover every hypothesis_id exactly once"
            )
        if len(deontic_ids) != len(set(deontic_ids)):
            raise ValueError("deontic_admissibility_register must not duplicate hypothesis_id")

        ambiguity_refs = sorted(
            {
                hypothesis_id
                for entry in self.ambiguity_register
                for hypothesis_id in entry.related_hypothesis_ids
            }
        )
        unknown_ambiguity_refs = [ref for ref in ambiguity_refs if ref not in hypothesis_id_set]
        if unknown_ambiguity_refs:
            raise ValueError("ambiguity_register references unknown hypothesis ids")

        working_set = set(self.working_hypothesis_posture.active_hypothesis_ids)
        if not working_set.issubset(hypothesis_id_set):
            raise ValueError("working_hypothesis_posture references unknown hypothesis ids")

        payload_without_id = self.model_dump(mode="json", exclude_none=False)
        payload_without_id.pop("hypothesis_frame_id", None)
        expected_id = compute_adeu_arc_hypothesis_frame_id(payload_without_id)
        if self.hypothesis_frame_id != expected_id:
            raise ValueError("hypothesis_frame_id must match canonical full payload hash identity")
        return self


def compute_adeu_arc_observation_frame_id(payload_without_frame_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_frame_id)
    canonical_payload.setdefault("schema", ADEU_ARC_OBSERVATION_FRAME_SCHEMA)
    canonical_payload.pop("observation_frame_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_obs_{digest[:32]}"


def compute_adeu_arc_hypothesis_frame_id(payload_without_frame_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_frame_id)
    canonical_payload.setdefault("schema", ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA)
    canonical_payload.pop("hypothesis_frame_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_hyp_{digest[:32]}"


def canonicalize_adeu_arc_observation_frame_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcObservationFrame.model_validate(payload).model_dump(
        mode="json", exclude_none=False
    )


def canonicalize_adeu_arc_hypothesis_frame_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcHypothesisFrame.model_validate(payload).model_dump(
        mode="json", exclude_none=False
    )


def materialize_adeu_arc_observation_frame_payload(
    payload_without_observation_frame_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_observation_frame_id)
    payload.setdefault("schema", ADEU_ARC_OBSERVATION_FRAME_SCHEMA)
    payload["observation_frame_id"] = compute_adeu_arc_observation_frame_id(payload)
    return canonicalize_adeu_arc_observation_frame_payload(payload)


def materialize_adeu_arc_hypothesis_frame_payload(
    payload_without_hypothesis_frame_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_hypothesis_frame_id)
    payload.setdefault("schema", ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA)
    payload["hypothesis_frame_id"] = compute_adeu_arc_hypothesis_frame_id(payload)
    return canonicalize_adeu_arc_hypothesis_frame_payload(payload)


def derive_v42b_arc_observation_frame(
    *,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    ontology_register: list[dict[str, Any]],
    entity_inventory: list[dict[str, Any]],
    relation_inventory: list[dict[str, Any]],
    state_partition_register: list[dict[str, Any]],
    ontology_uncertainty_register: list[dict[str, Any]],
    observation_entries: list[dict[str, Any]],
    required_dimension_set: list[str] | None = None,
    missing_dimension_register: list[str] | None = None,
) -> dict[str, Any]:
    unresolved_entries = sorted(
        entry["observation_id"]
        for entry in observation_entries
        if entry.get("resolution_posture") == "unresolved"
    )
    dimensions = (
        list(_OBSERVATION_DIMENSIONS)
        if required_dimension_set is None
        else deepcopy(required_dimension_set)
    )
    missing_dimensions = (
        [] if missing_dimension_register is None else deepcopy(missing_dimension_register)
    )
    decomposition_coverage = (
        (len(dimensions) - len(missing_dimensions)) / len(dimensions) if dimensions else 0.0
    )
    payload_without_frame_id: dict[str, Any] = {
        "schema": ADEU_ARC_OBSERVATION_FRAME_SCHEMA,
        "task_packet_id": task_packet["task_packet_id"],
        "task_packet_ref": task_packet_ref,
        "environment_authority": task_packet["environment_authority"],
        "mode_posture": task_packet["mode_posture"],
        "game_ref": task_packet["game_ref"],
        "session_ref": task_packet["session_ref"],
        "ontology_register": deepcopy(ontology_register),
        "entity_inventory": deepcopy(entity_inventory),
        "relation_inventory": deepcopy(relation_inventory),
        "state_partition_register": deepcopy(state_partition_register),
        "ontology_uncertainty_register": deepcopy(ontology_uncertainty_register),
        "observation_entries": deepcopy(observation_entries),
        "unresolved_observation_entries": unresolved_entries,
        "decomposition_coverage": decomposition_coverage,
        "coverage_basis": "required_dimension_set",
        "required_dimension_set": dimensions,
        "missing_dimension_register": missing_dimensions,
    }
    return materialize_adeu_arc_observation_frame_payload(payload_without_frame_id)


def derive_v42b_arc_hypothesis_frame(
    *,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    observation_frame: dict[str, Any],
    observation_frame_ref: str,
    hypothesis_register: list[dict[str, Any]],
    ambiguity_register: list[dict[str, Any]],
    claim_posture_register: list[dict[str, Any]],
    deontic_admissibility_register: list[dict[str, Any]],
    utility_pressure_register: list[dict[str, Any]],
    working_hypothesis_posture: dict[str, Any],
) -> dict[str, Any]:
    payload_without_frame_id: dict[str, Any] = {
        "schema": ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA,
        "task_packet_id": task_packet["task_packet_id"],
        "task_packet_ref": task_packet_ref,
        "observation_frame_id": observation_frame["observation_frame_id"],
        "observation_frame_ref": observation_frame_ref,
        "hypothesis_register": deepcopy(hypothesis_register),
        "ambiguity_register": deepcopy(ambiguity_register),
        "claim_posture_register": deepcopy(claim_posture_register),
        "deontic_admissibility_register": deepcopy(deontic_admissibility_register),
        "utility_pressure_register": deepcopy(utility_pressure_register),
        "working_hypothesis_posture": deepcopy(working_hypothesis_posture),
    }
    return materialize_adeu_arc_hypothesis_frame_payload(payload_without_frame_id)
