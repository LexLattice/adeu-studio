from __future__ import annotations

import hashlib
import json
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def sha256_canonical_json(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


SemanticDomainKind = Literal["repo_policy_work"]
ParseStatus = Literal["resolved_singleton", "typed_alternatives", "clarification_required", "rejected_unsupported"]
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
TransformStatus = Literal[
    "transformed",
    "blocked_ambiguity",
    "blocked_missing_required_relation",
    "blocked_unsupported_relation",
    "blocked_resolution_failure",
]


def clause_lane_for(relation_kind: RelationKind) -> LaneTag:
    return {
        "bind_scope_anchor": "scope",
        "bind_policy_anchor": "policy",
        "use_worker_subject": "worker",
        "set_mutation_posture": "mutation",
        "allow_path": "constraint",
        "forbid_path": "constraint",
        "forbid_effect": "constraint",
        "produce_artifact_kind": "deliverable",
    }[relation_kind]


def object_kind_for(relation_kind: RelationKind) -> ObjectKind:
    return {
        "bind_scope_anchor": "scope_anchor",
        "bind_policy_anchor": "policy_anchor",
        "use_worker_subject": "worker_subject",
        "set_mutation_posture": "mutation_posture",
        "allow_path": "repo_rel_path",
        "forbid_path": "repo_rel_path",
        "forbid_effect": "effect_tag",
        "produce_artifact_kind": "artifact_kind",
    }[relation_kind]


class AnchorAlias(BaseModel):
    model_config = ConfigDict(extra="forbid")

    alias: str = Field(min_length=1)
    alias_kind: Literal["exact_phrase", "normalized_phrase"] = "normalized_phrase"


class ScopeAnchor(BaseModel):
    model_config = ConfigDict(extra="forbid")

    anchor_id: str = Field(min_length=1)
    display_name: str = Field(min_length=1)
    resolved_scope_ref: str = Field(min_length=1)
    resolved_binding_entry_ref: str = Field(min_length=1)
    aliases: list[AnchorAlias] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "ScopeAnchor":
        if not self.aliases:
            raise ValueError("scope anchors must declare at least one alias")
        return self


class PolicyAnchor(BaseModel):
    model_config = ConfigDict(extra="forbid")

    anchor_id: str = Field(min_length=1)
    display_name: str = Field(min_length=1)
    resolved_clause_ref: str = Field(min_length=1)
    resolved_policy_consumer_ref: str = Field(min_length=1)
    aliases: list[AnchorAlias] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "PolicyAnchor":
        if not self.aliases:
            raise ValueError("policy anchors must declare at least one alias")
        return self


class WorkerAnchor(BaseModel):
    model_config = ConfigDict(extra="forbid")

    anchor_id: str = Field(min_length=1)
    resolved_worker_subject_ref: str = Field(min_length=1)
    aliases: list[AnchorAlias] = Field(default_factory=list)


class SemanticLexiconEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    canonical_value: str = Field(min_length=1)
    aliases: list[AnchorAlias] = Field(default_factory=list)


class SemanticParseProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_semantic_parse_profile@1"] = "adeu_semantic_parse_profile@1"
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

    @model_validator(mode="after")
    def _validate(self) -> "SemanticParseProfile":
        payload = self.model_dump(mode="json", exclude={"semantic_hash"}, exclude_none=True)
        self.semantic_hash = sha256_canonical_json(payload)
        return self


class SemanticClause(BaseModel):
    model_config = ConfigDict(extra="forbid")

    relation_kind: RelationKind
    object_value: str = Field(min_length=1)
    lane_tag: LaneTag
    object_kind: ObjectKind
    evidence: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "SemanticClause":
        expected_lane = clause_lane_for(self.relation_kind)
        expected_object_kind = object_kind_for(self.relation_kind)
        if self.lane_tag != expected_lane:
            raise ValueError(
                f"{self.relation_kind} requires lane_tag={expected_lane}, got {self.lane_tag}"
            )
        if self.object_kind != expected_object_kind:
            raise ValueError(
                f"{self.relation_kind} requires object_kind={expected_object_kind}, got {self.object_kind}"
            )
        self.evidence = sorted(dict.fromkeys(self.evidence))
        return self

    def semantic_basis(self) -> dict[str, Any]:
        return {
            "relation_kind": self.relation_kind,
            "object_value": self.object_value,
        }


class SemanticNormalForm(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_semantic_normal_form@1"] = "adeu_semantic_normal_form@1"
    normal_form_id: str = Field(min_length=1)
    profile_id: str = Field(min_length=1)
    domain_kind: SemanticDomainKind = "repo_policy_work"
    clauses: list[SemanticClause] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)
    confidence_band: ConfidenceBand = "medium"
    uncertainty_notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "SemanticNormalForm":
        sorted_clauses = sorted(
            self.clauses,
            key=lambda clause: (
                clause.relation_kind,
                clause.object_value,
            ),
        )
        # dedupe identical semantic clauses while preserving canonical evidence union
        deduped: list[SemanticClause] = []
        seen: dict[tuple[str, str], SemanticClause] = {}
        for clause in sorted_clauses:
            key = (clause.relation_kind, clause.object_value)
            if key in seen:
                merged = sorted(set(seen[key].evidence) | set(clause.evidence))
                seen[key].evidence = merged
                continue
            seen[key] = clause
            deduped.append(clause)
        self.clauses = deduped
        basis = {
            "schema": self.schema,
            "profile_id": self.profile_id,
            "domain_kind": self.domain_kind,
            "clauses": [clause.semantic_basis() for clause in self.clauses],
        }
        self.semantic_hash = sha256_canonical_json(basis)
        self.normal_form_id = f"snf:{self.semantic_hash[:16]}"
        return self


class ParseAmbiguity(BaseModel):
    model_config = ConfigDict(extra="forbid")

    ambiguity_id: str = Field(min_length=1)
    ambiguity_kind: Literal["multiple_scope_anchor_matches", "multiple_policy_anchor_matches", "missing_required_anchor"]
    alternatives: list[str] = Field(default_factory=list)
    notes: str = Field(min_length=1)


class SemanticParseCandidate(BaseModel):
    model_config = ConfigDict(extra="forbid")

    candidate_id: str = Field(min_length=1)
    candidate_rank: int = Field(ge=0)
    normal_form: SemanticNormalForm
    evidence_summary: list[str] = Field(default_factory=list)


class SemanticParseResult(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_semantic_parse_result@1"] = "adeu_semantic_parse_result@1"
    parse_result_id: str = Field(min_length=1)
    profile_id: str = Field(min_length=1)
    input_kind: Literal["natural_language"] = "natural_language"
    input_text: str = Field(min_length=1)
    input_text_hash: str = Field(min_length=1)
    parse_status: ParseStatus
    candidates: list[SemanticParseCandidate] = Field(default_factory=list)
    ambiguities: list[ParseAmbiguity] = Field(default_factory=list)
    rejected_reason_codes: list[str] = Field(default_factory=list)
    notices: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "SemanticParseResult":
        self.input_text_hash = sha256_canonical_json({"input_text": self.input_text})
        self.parse_result_id = f"parse:{self.input_text_hash[:16]}"
        return self


class TaskpackBindingSpecSeed(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_taskpack_binding_spec_seed@1"] = "adeu_taskpack_binding_spec_seed@1"
    seed_id: str = Field(min_length=1)
    profile_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    binding_subject_id: str = Field(min_length=1)
    scope_anchor_id: str = Field(min_length=1)
    scope_source_ref: str = Field(min_length=1)
    scope_binding_entry_ref: str = Field(min_length=1)
    policy_anchor_id: str = Field(min_length=1)
    policy_source_ref: str = Field(min_length=1)
    policy_authority_clause_ref: str = Field(min_length=1)
    worker_subject_ref: str = Field(min_length=1)
    mutation_posture: Literal["read_only"] = "read_only"
    allowlist_projection: list[str] = Field(default_factory=list)
    forbidden_projection: dict[str, list[str]] = Field(default_factory=dict)
    prompt_projection_posture: Literal["projection_only_non_authoritative"] = "projection_only_non_authoritative"
    lineage_resolution_posture: Literal["fail_closed_on_unresolved_or_stale_lineage"] = "fail_closed_on_unresolved_or_stale_lineage"
    unsupported_mapping_posture: Literal["fail_closed"] = "fail_closed"
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate(self) -> "TaskpackBindingSpecSeed":
        self.allowlist_projection = sorted(dict.fromkeys(self.allowlist_projection))
        self.forbidden_projection = {
            "forbidden_paths": sorted(dict.fromkeys(self.forbidden_projection.get("forbidden_paths", []))),
            "forbidden_effects": sorted(dict.fromkeys(self.forbidden_projection.get("forbidden_effects", []))),
        }
        basis = self.model_dump(mode="json", exclude={"semantic_hash", "seed_id"}, exclude_none=True)
        self.semantic_hash = sha256_canonical_json(basis)
        self.seed_id = f"seed:{self.semantic_hash[:16]}"
        return self


class SemanticTransformContract(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_semantic_transform_contract@1"] = "adeu_semantic_transform_contract@1"
    contract_id: str = Field(min_length=1)
    source_schema: str = Field(min_length=1)
    target_schema: str = Field(min_length=1)
    profile_id: str = Field(min_length=1)
    required_singleton_relations: list[RelationKind] = Field(default_factory=list)
    supported_multi_relations: list[RelationKind] = Field(default_factory=list)
    fixed_defaults: dict[str, str] = Field(default_factory=dict)
    unsupported_relation_kinds: list[str] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate(self) -> "SemanticTransformContract":
        self.required_singleton_relations = sorted(dict.fromkeys(self.required_singleton_relations))
        self.supported_multi_relations = sorted(dict.fromkeys(self.supported_multi_relations))
        self.unsupported_relation_kinds = sorted(dict.fromkeys(self.unsupported_relation_kinds))
        basis = self.model_dump(mode="json", exclude={"semantic_hash"}, exclude_none=True)
        self.semantic_hash = sha256_canonical_json(basis)
        return self


class BlockingIssue(BaseModel):
    model_config = ConfigDict(extra="forbid")

    code: str = Field(min_length=1)
    message: str = Field(min_length=1)
    details: dict[str, Any] = Field(default_factory=dict)


class SemanticTransformResult(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_semantic_transform_result@1"] = "adeu_semantic_transform_result@1"
    transform_result_id: str = Field(min_length=1)
    contract_id: str = Field(min_length=1)
    source_semantic_hash: str = Field(min_length=1)
    target_schema: str = Field(min_length=1)
    transform_status: TransformStatus
    blocking_issues: list[BlockingIssue] = Field(default_factory=list)
    target_payload: dict[str, Any] | None = None
    target_semantic_hash: str | None = None

    @model_validator(mode="after")
    def _validate(self) -> "SemanticTransformResult":
        basis = {
            "contract_id": self.contract_id,
            "source_semantic_hash": self.source_semantic_hash,
            "target_schema": self.target_schema,
            "transform_status": self.transform_status,
            "target_semantic_hash": self.target_semantic_hash,
        }
        self.transform_result_id = f"transform:{sha256_canonical_json(basis)[:16]}"
        return self
