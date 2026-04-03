from __future__ import annotations

import hashlib
import json
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator

ADEU_SEMANTIC_PARSE_PROFILE_SCHEMA = "adeu_semantic_parse_profile@1"
ADEU_SEMANTIC_STATEMENT_CORE_SCHEMA = "adeu_semantic_statement_core@1"
ADEU_SEMANTIC_NORMAL_FORM_SCHEMA = "adeu_semantic_normal_form@1"
ADEU_SEMANTIC_PARSE_RESULT_SCHEMA = "adeu_semantic_parse_result@1"
ADEU_SEMANTIC_TRANSFORM_CONTRACT_SCHEMA = "adeu_semantic_transform_contract@1"
ADEU_TASKPACK_BINDING_SPEC_SEED_SCHEMA = "adeu_taskpack_binding_spec_seed@1"

IDENTITY_FIELD_NAMES = ("relation_kind", "object_value")
PROJECTION_FIELD_NAMES = (
    "lane_tag",
    "object_kind",
    "evidence",
    "confidence_band",
    "uncertainty_notes",
)
MODEL_CONFIG = ConfigDict(extra="forbid", populate_by_name=True, protected_namespaces=())

SemanticDomainKind = Literal["repo_policy_work"]
ParseStatus = Literal[
    "resolved_singleton",
    "typed_alternatives",
    "clarification_required",
    "rejected_unsupported",
]
ConfidenceBand = Literal["high", "medium", "low"]
LaneTag = Literal["scope", "policy", "worker", "mutation", "constraint", "deliverable"]
RelationKind = Literal[
    "bind_scope_anchor",
    "bind_policy_anchor",
    "use_worker_subject",
    "set_mutation_posture",
    "allow_path",
    "forbid_path",
    "forbid_effect",
    "produce_artifact_kind",
]
ObjectKind = Literal[
    "scope_anchor",
    "policy_anchor",
    "worker_subject",
    "mutation_posture",
    "repo_rel_path",
    "effect_tag",
    "artifact_kind",
]
AmbiguityKind = Literal[
    "multiple_scope_anchor_matches",
    "multiple_policy_anchor_matches",
    "missing_required_anchor",
]
RejectedReasonCode = Literal["ASL-PARSE-UNSUPPORTED"]

_LANE_FOR_RELATION: dict[RelationKind, LaneTag] = {
    "bind_scope_anchor": "scope",
    "bind_policy_anchor": "policy",
    "use_worker_subject": "worker",
    "set_mutation_posture": "mutation",
    "allow_path": "constraint",
    "forbid_path": "constraint",
    "forbid_effect": "constraint",
    "produce_artifact_kind": "deliverable",
}
_OBJECT_KIND_FOR_RELATION: dict[RelationKind, ObjectKind] = {
    "bind_scope_anchor": "scope_anchor",
    "bind_policy_anchor": "policy_anchor",
    "use_worker_subject": "worker_subject",
    "set_mutation_posture": "mutation_posture",
    "allow_path": "repo_rel_path",
    "forbid_path": "repo_rel_path",
    "forbid_effect": "effect_tag",
    "produce_artifact_kind": "artifact_kind",
}


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def sha256_canonical_json(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


class AnchorAlias(BaseModel):
    model_config = MODEL_CONFIG

    alias: str = Field(min_length=1)
    alias_kind: Literal["exact_phrase", "normalized_phrase"] = "normalized_phrase"


class ScopeAnchor(BaseModel):
    model_config = MODEL_CONFIG

    anchor_id: str = Field(min_length=1)
    display_name: str = Field(min_length=1)
    resolved_scope_ref: str = Field(min_length=1)
    resolved_binding_entry_ref: str = Field(min_length=1)
    aliases: list[AnchorAlias] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "ScopeAnchor":
        self.aliases = sorted(
            {(alias.alias_kind, alias.alias): alias for alias in self.aliases}.values(),
            key=lambda alias: (alias.alias_kind, alias.alias),
        )
        if not self.aliases:
            raise ValueError("scope anchors must declare at least one alias")
        return self


class PolicyAnchor(BaseModel):
    model_config = MODEL_CONFIG

    anchor_id: str = Field(min_length=1)
    display_name: str = Field(min_length=1)
    resolved_clause_ref: str = Field(min_length=1)
    resolved_policy_consumer_ref: str = Field(min_length=1)
    aliases: list[AnchorAlias] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "PolicyAnchor":
        self.aliases = sorted(
            {(alias.alias_kind, alias.alias): alias for alias in self.aliases}.values(),
            key=lambda alias: (alias.alias_kind, alias.alias),
        )
        if not self.aliases:
            raise ValueError("policy anchors must declare at least one alias")
        return self


class WorkerAnchor(BaseModel):
    model_config = MODEL_CONFIG

    anchor_id: str = Field(min_length=1)
    resolved_worker_subject_ref: str = Field(min_length=1)
    aliases: list[AnchorAlias] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "WorkerAnchor":
        self.aliases = sorted(
            {(alias.alias_kind, alias.alias): alias for alias in self.aliases}.values(),
            key=lambda alias: (alias.alias_kind, alias.alias),
        )
        return self


class SemanticLexiconEntry(BaseModel):
    model_config = MODEL_CONFIG

    canonical_value: str = Field(min_length=1)
    aliases: list[AnchorAlias] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "SemanticLexiconEntry":
        self.aliases = sorted(
            {(alias.alias_kind, alias.alias): alias for alias in self.aliases}.values(),
            key=lambda alias: (alias.alias_kind, alias.alias),
        )
        return self


class SemanticParseProfile(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SEMANTIC_PARSE_PROFILE_SCHEMA] = Field(
        default=ADEU_SEMANTIC_PARSE_PROFILE_SCHEMA,
        alias="schema",
    )
    profile_id: str = Field(min_length=1)
    domain_kind: SemanticDomainKind = "repo_policy_work"
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    scope_anchors: list[ScopeAnchor] = Field(default_factory=list)
    policy_anchors: list[PolicyAnchor] = Field(default_factory=list)
    worker_anchors: list[WorkerAnchor] = Field(default_factory=list)
    mutation_lexicon: list[SemanticLexiconEntry] = Field(default_factory=list)
    artifact_kind_lexicon: list[SemanticLexiconEntry] = Field(default_factory=list)
    effect_lexicon: list[SemanticLexiconEntry] = Field(default_factory=list)
    unsupported_patterns: list[str] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SemanticParseProfile":
        self.scope_anchors = sorted(self.scope_anchors, key=lambda anchor: anchor.anchor_id)
        self.policy_anchors = sorted(self.policy_anchors, key=lambda anchor: anchor.anchor_id)
        self.worker_anchors = sorted(self.worker_anchors, key=lambda anchor: anchor.anchor_id)
        self.mutation_lexicon = sorted(
            self.mutation_lexicon, key=lambda entry: entry.canonical_value
        )
        self.artifact_kind_lexicon = sorted(
            self.artifact_kind_lexicon, key=lambda entry: entry.canonical_value
        )
        self.effect_lexicon = sorted(self.effect_lexicon, key=lambda entry: entry.canonical_value)
        self.unsupported_patterns = sorted(dict.fromkeys(self.unsupported_patterns))
        basis = self.model_dump(
            mode="json",
            by_alias=True,
            exclude={"semantic_hash"},
            exclude_none=True,
        )
        self.semantic_hash = sha256_canonical_json(basis)
        return self


class SemanticStatementCore(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SEMANTIC_STATEMENT_CORE_SCHEMA] = Field(
        default=ADEU_SEMANTIC_STATEMENT_CORE_SCHEMA,
        alias="schema",
    )
    relation_kind: RelationKind
    object_value: str = Field(min_length=1)
    lane_tag: LaneTag
    object_kind: ObjectKind
    evidence: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SemanticStatementCore":
        expected_lane = _LANE_FOR_RELATION[self.relation_kind]
        expected_object_kind = _OBJECT_KIND_FOR_RELATION[self.relation_kind]
        if self.lane_tag != expected_lane:
            raise ValueError(
                f"{self.relation_kind} requires lane_tag={expected_lane}, got {self.lane_tag}"
            )
        if self.object_kind != expected_object_kind:
            raise ValueError(
                (
                    f"{self.relation_kind} requires "
                    f"object_kind={expected_object_kind}, got {self.object_kind}"
                )
            )
        self.evidence = sorted(dict.fromkeys(self.evidence))
        return self

    def identity_basis(self) -> dict[str, str]:
        return {
            "relation_kind": self.relation_kind,
            "object_value": self.object_value,
        }


class SemanticNormalForm(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SEMANTIC_NORMAL_FORM_SCHEMA] = Field(
        default=ADEU_SEMANTIC_NORMAL_FORM_SCHEMA,
        alias="schema",
    )
    normal_form_id: str = Field(min_length=1)
    profile_id: str = Field(min_length=1)
    domain_kind: SemanticDomainKind = "repo_policy_work"
    statement_cores: list[SemanticStatementCore] = Field(default_factory=list)
    identity_field_names: list[Literal["relation_kind", "object_value"]] = Field(
        default_factory=lambda: list(IDENTITY_FIELD_NAMES)
    )
    projection_field_names: list[
        Literal[
            "lane_tag",
            "object_kind",
            "evidence",
            "confidence_band",
            "uncertainty_notes",
        ]
    ] = Field(default_factory=lambda: list(PROJECTION_FIELD_NAMES))
    semantic_hash: str = Field(min_length=1)
    confidence_band: ConfidenceBand = "medium"
    uncertainty_notes: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SemanticNormalForm":
        if tuple(self.identity_field_names) != IDENTITY_FIELD_NAMES:
            raise ValueError("identity_field_names must match the frozen V49-A identity law")
        if tuple(self.projection_field_names) != PROJECTION_FIELD_NAMES:
            raise ValueError(
                "projection_field_names must match the frozen V49-A projection field set"
            )

        sorted_cores = sorted(
            self.statement_cores,
            key=lambda core: (core.relation_kind, core.object_value),
        )
        deduped: list[SemanticStatementCore] = []
        seen: dict[tuple[str, str], SemanticStatementCore] = {}
        for core in sorted_cores:
            key = (core.relation_kind, core.object_value)
            if key in seen:
                seen[key].evidence = sorted(set(seen[key].evidence) | set(core.evidence))
                continue
            seen[key] = core
            deduped.append(core)
        self.statement_cores = deduped
        self.uncertainty_notes = sorted(dict.fromkeys(self.uncertainty_notes))

        basis = {
            "schema": self.schema,
            "profile_id": self.profile_id,
            "domain_kind": self.domain_kind,
            "statement_cores": [core.identity_basis() for core in self.statement_cores],
        }
        self.semantic_hash = sha256_canonical_json(basis)
        self.normal_form_id = f"snf:{self.semantic_hash[:16]}"
        return self


class ParseAmbiguity(BaseModel):
    model_config = MODEL_CONFIG

    ambiguity_id: str = Field(min_length=1)
    ambiguity_kind: AmbiguityKind
    alternatives: list[str] = Field(default_factory=list)
    notes: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate(self) -> "ParseAmbiguity":
        self.alternatives = sorted(dict.fromkeys(self.alternatives))
        return self


class SemanticParseCandidate(BaseModel):
    model_config = MODEL_CONFIG

    candidate_id: str = Field(min_length=1)
    candidate_rank: int = Field(ge=1)
    normal_form: SemanticNormalForm
    evidence_summary: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "SemanticParseCandidate":
        self.evidence_summary = sorted(dict.fromkeys(self.evidence_summary))
        self.candidate_id = f"candidate:{self.candidate_rank}:{self.normal_form.semantic_hash[:16]}"
        return self


class SemanticParseResult(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SEMANTIC_PARSE_RESULT_SCHEMA] = Field(
        default=ADEU_SEMANTIC_PARSE_RESULT_SCHEMA,
        alias="schema",
    )
    parse_result_id: str = Field(min_length=1)
    profile_id: str = Field(min_length=1)
    input_kind: Literal["natural_language"] = "natural_language"
    input_text: str = Field(min_length=1)
    input_text_hash: str = Field(min_length=1)
    parse_status: ParseStatus
    candidates: list[SemanticParseCandidate] = Field(default_factory=list)
    ambiguities: list[ParseAmbiguity] = Field(default_factory=list)
    rejected_reason_codes: list[RejectedReasonCode] = Field(default_factory=list)
    notices: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @field_validator("rejected_reason_codes")
    @classmethod
    def _dedupe_rejected_reason_codes(
        cls, value: list[RejectedReasonCode]
    ) -> list[RejectedReasonCode]:
        return sorted(dict.fromkeys(value))

    @model_validator(mode="after")
    def _validate(self) -> "SemanticParseResult":
        self.candidates = sorted(
            self.candidates,
            key=lambda candidate: (candidate.candidate_rank, candidate.normal_form.semantic_hash),
        )
        self.ambiguities = sorted(self.ambiguities, key=lambda ambiguity: ambiguity.ambiguity_id)
        self.notices = sorted(dict.fromkeys(self.notices))
        self.input_text_hash = sha256_canonical_json({"input_text": self.input_text})
        self.parse_result_id = f"parse:{self.input_text_hash[:16]}"

        if self.parse_status == "resolved_singleton":
            if len(self.candidates) != 1 or self.ambiguities or self.rejected_reason_codes:
                raise ValueError(
                    "resolved_singleton requires exactly one candidate and no ambiguities "
                    "or rejected reasons"
                )
        elif self.parse_status == "typed_alternatives":
            unique_hashes = {candidate.normal_form.semantic_hash for candidate in self.candidates}
            if len(self.candidates) < 2 or len(unique_hashes) < 2 or not self.ambiguities:
                raise ValueError(
                    "typed_alternatives requires at least two distinct candidates and at "
                    "least one ambiguity"
                )
            if self.rejected_reason_codes:
                raise ValueError("typed_alternatives may not carry rejected_reason_codes")
        elif self.parse_status == "clarification_required":
            if self.candidates or not self.ambiguities or self.rejected_reason_codes:
                raise ValueError(
                    "clarification_required requires no candidates, at least one "
                    "ambiguity, and no rejected reasons"
                )
        elif self.parse_status == "rejected_unsupported":
            if self.candidates or self.ambiguities or not self.rejected_reason_codes:
                raise ValueError(
                    "rejected_unsupported requires no candidates, no ambiguities, and "
                    "at least one rejected reason"
                )

        return self


class SemanticTransformContract(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SEMANTIC_TRANSFORM_CONTRACT_SCHEMA] = Field(
        default=ADEU_SEMANTIC_TRANSFORM_CONTRACT_SCHEMA,
        alias="schema",
    )
    contract_id: str = Field(min_length=1)
    source_schema: Literal[ADEU_SEMANTIC_NORMAL_FORM_SCHEMA] = ADEU_SEMANTIC_NORMAL_FORM_SCHEMA
    target_schema: Literal[ADEU_TASKPACK_BINDING_SPEC_SEED_SCHEMA] = (
        ADEU_TASKPACK_BINDING_SPEC_SEED_SCHEMA
    )
    profile_id: str = Field(min_length=1)
    required_singleton_relations: list[RelationKind] = Field(default_factory=list)
    supported_multi_relations: list[RelationKind] = Field(default_factory=list)
    fixed_defaults: dict[str, str] = Field(default_factory=dict)
    unsupported_relation_kinds: list[str] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SemanticTransformContract":
        self.required_singleton_relations = sorted(dict.fromkeys(self.required_singleton_relations))
        self.supported_multi_relations = sorted(dict.fromkeys(self.supported_multi_relations))
        self.unsupported_relation_kinds = sorted(dict.fromkeys(self.unsupported_relation_kinds))
        if set(self.required_singleton_relations) & set(self.supported_multi_relations):
            raise ValueError(
                "required_singleton_relations and supported_multi_relations must be disjoint"
            )
        basis = self.model_dump(
            mode="json",
            by_alias=True,
            exclude={"semantic_hash"},
            exclude_none=True,
        )
        self.semantic_hash = sha256_canonical_json(basis)
        return self
