from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator

from .analysis_request import (
    ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA,
    AdeuArchitectureAnalysisRequest,
    AuthorityBoundaryPolicyPin,
    _assert_non_empty_text,
    _assert_sorted_unique,
    _dump_json_payload,
    _normalize_repo_relative_path,
    _resolve_repository_root,
)

ADEU_ARCHITECTURE_ANALYSIS_SETTLEMENT_FRAME_SCHEMA = (
    "adeu_architecture_analysis_settlement_frame@1"
)
V41B_V84_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS84.md#v41b_practical_analysis_settlement_contract@1"
)

DeonticClass = Literal[
    "required",
    "forbidden",
    "permitted",
    "optional_hint",
    "fallback_affordance",
]
AffordanceDecisionClass = Literal["used", "deferred", "intentionally_declined"]
ClaimPostureClass = Literal[
    "observed",
    "inferred",
    "conjectural",
    "unentitled_negative_claim",
]
SupportLimitClass = Literal[
    "search_absence",
    "proof_not_attempted",
    "ambiguity_dependent",
    "assumption_pressure",
]
CompileEntitlement = Literal["entitled", "blocked"]
EscalationTriggerId = Literal[
    "unresolved_high_impact_ambiguity",
    "silent_semantic_assumption_needed",
    "impossibility_claim_without_proof",
    "externalized_search_or_check_required",
]

_REQUIRED_ESCALATION_TRIGGERS = sorted(
    {
        "unresolved_high_impact_ambiguity",
        "silent_semantic_assumption_needed",
        "impossibility_claim_without_proof",
        "externalized_search_or_check_required",
    }
)
_AFFORDANCE_DEONTIC_CLASSES = {"permitted", "optional_hint", "fallback_affordance"}
_ADVISORY_NOTE_FORBIDDEN_PREFIXES = (
    "interpretation:",
    "deontic_class:",
    "claim_posture:",
    "trigger_id:",
    "source_ref:",
    "blocking_reason:",
)


def _validation_context(
    repository_root: Path | None = None,
    **extra: Any,
) -> dict[str, Any]:
    context = {"repository_root": repository_root}
    context.update(extra)
    return context


def _normalize_ref(raw_ref: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(raw_ref, field_name=field_name)
    if "#" not in normalized:
        return _normalize_repo_relative_path(normalized, field_name=field_name)
    path_part, fragment = normalized.split("#", 1)
    if not fragment.strip():
        raise ValueError(f"{field_name} must not end with an empty fragment")
    normalized_path = _normalize_repo_relative_path(path_part, field_name=field_name)
    return f"{normalized_path}#{fragment.strip()}"


def _sort_unique_ref_list(values: list[str], *, field_name: str) -> list[str]:
    normalized = {_normalize_ref(value, field_name=field_name) for value in values}
    return sorted(normalized)


def _request_ref_path(ref: str) -> str:
    return ref.split("#", 1)[0]


def _load_analysis_request_from_ref(
    analysis_request_ref: str,
    *,
    repository_root: Path,
) -> AdeuArchitectureAnalysisRequest:
    request_path = repository_root / _request_ref_path(analysis_request_ref)
    if not request_path.is_file():
        raise ValueError(
            "analysis_request_ref does not exist: "
            f"{_request_ref_path(analysis_request_ref)}"
        )
    payload = json.loads(request_path.read_text(encoding="utf-8"))
    if payload.get("schema") != ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA:
        raise ValueError(
            "analysis_request_ref must resolve to "
            "adeu_architecture_analysis_request@1"
        )
    return AdeuArchitectureAnalysisRequest.model_validate(
        payload,
        context={"repository_root": repository_root},
    )


def _request_named_refs(
    request: AdeuArchitectureAnalysisRequest,
    *,
    analysis_request_ref: str,
) -> set[str]:
    refs = {analysis_request_ref}
    refs.update(item.path for item in request.source_set.items)
    refs.update(request.maintainer_brief_refs)
    refs.update(request.accepted_doc_refs)
    refs.update(item.input_ref for item in request.captured_inputs)
    if request.authority_boundary_policy.policy_ref is not None:
        refs.add(request.authority_boundary_policy.policy_ref)
    if request.settlement_frame_ref is not None:
        refs.add(request.settlement_frame_ref)
    return refs


def _ref_resolves_to_request_boundary(
    ref: str,
    *,
    request: AdeuArchitectureAnalysisRequest,
    analysis_request_ref: str,
) -> bool:
    direct_refs = _request_named_refs(request, analysis_request_ref=analysis_request_ref)
    if ref in direct_refs:
        return True
    ref_path = _request_ref_path(ref)
    if ref_path in {_request_ref_path(candidate) for candidate in direct_refs}:
        return True
    return False


def _typed_refs_from_frame(frame: "AdeuArchitectureAnalysisSettlementFrame") -> set[str]:
    refs = {frame.analysis_request_ref}
    for entry in frame.interpretation_register:
        refs.update(entry.support_refs)
        refs.update(entry.linked_ambiguity_refs)
    for entry in frame.deontic_typing_register:
        refs.add(entry.target_ref)
    for entry in frame.affordance_decisions:
        refs.add(entry.target_ref)
    for entry in frame.claim_posture_register:
        refs.add(entry.claim_ref)
    refs.update(frame.unresolved_high_impact_ambiguity_refs)
    for entry in frame.active_escalation_records:
        refs.update(entry.supporting_refs)
    for entry in frame.blocking_lineage:
        refs.update(entry.supporting_refs)
    if frame.authority_boundary_policy.policy_ref is not None:
        refs.add(frame.authority_boundary_policy.policy_ref)
    return refs


class InterpretationEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    interpretation_id: str
    summary: str
    support_refs: list[str]
    linked_ambiguity_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_entry(self) -> InterpretationEntry:
        object.__setattr__(
            self,
            "interpretation_id",
            _assert_non_empty_text(self.interpretation_id, field_name="interpretation_id"),
        )
        object.__setattr__(
            self,
            "summary",
            _assert_non_empty_text(self.summary, field_name="summary"),
        )
        support_refs = _sort_unique_ref_list(self.support_refs, field_name="support_refs")
        if not support_refs:
            raise ValueError("support_refs must not be empty")
        object.__setattr__(self, "support_refs", support_refs)
        object.__setattr__(
            self,
            "linked_ambiguity_refs",
            _sort_unique_ref_list(
                self.linked_ambiguity_refs,
                field_name="linked_ambiguity_refs",
            ),
        )
        return self


class DeonticTypingEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    typing_id: str
    target_ref: str
    target_kind: str
    deontic_class: DeonticClass
    rationale: str

    @model_validator(mode="after")
    def _validate_entry(self) -> DeonticTypingEntry:
        object.__setattr__(
            self,
            "typing_id",
            _assert_non_empty_text(self.typing_id, field_name="typing_id"),
        )
        object.__setattr__(
            self,
            "target_ref",
            _normalize_ref(self.target_ref, field_name="target_ref"),
        )
        object.__setattr__(
            self,
            "target_kind",
            _assert_non_empty_text(self.target_kind, field_name="target_kind"),
        )
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        return self


class AffordanceDecisionEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    decision_id: str
    target_ref: str
    decision_class: AffordanceDecisionClass
    rationale: str

    @model_validator(mode="after")
    def _validate_entry(self) -> AffordanceDecisionEntry:
        object.__setattr__(
            self,
            "decision_id",
            _assert_non_empty_text(self.decision_id, field_name="decision_id"),
        )
        object.__setattr__(
            self,
            "target_ref",
            _normalize_ref(self.target_ref, field_name="target_ref"),
        )
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        return self


class ClaimPostureEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    claim_id: str
    claim_ref: str
    posture_class: ClaimPostureClass
    rationale: str
    support_limit_class: SupportLimitClass | None = None

    @model_validator(mode="after")
    def _validate_entry(self) -> ClaimPostureEntry:
        object.__setattr__(
            self,
            "claim_id",
            _assert_non_empty_text(self.claim_id, field_name="claim_id"),
        )
        object.__setattr__(
            self,
            "claim_ref",
            _normalize_ref(self.claim_ref, field_name="claim_ref"),
        )
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        if self.posture_class == "unentitled_negative_claim":
            if self.support_limit_class is None:
                raise ValueError(
                    "unentitled_negative_claim entries require support_limit_class"
                )
        elif self.support_limit_class is not None:
            raise ValueError("support_limit_class is allowed only for unentitled_negative_claim")
        return self


class EscalationTriggerPolicy(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    trigger_ids: list[EscalationTriggerId]

    @model_validator(mode="after")
    def _validate_policy(self) -> EscalationTriggerPolicy:
        trigger_ids = sorted(set(self.trigger_ids))
        if trigger_ids != _REQUIRED_ESCALATION_TRIGGERS:
            raise ValueError(
                "escalation_trigger_policy.trigger_ids must exactly match the frozen starter set"
            )
        object.__setattr__(self, "trigger_ids", trigger_ids)
        return self


class ActiveEscalationRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    trigger_id: EscalationTriggerId
    supporting_refs: list[str]

    @model_validator(mode="after")
    def _validate_record(self) -> ActiveEscalationRecord:
        supporting_refs = _sort_unique_ref_list(
            self.supporting_refs,
            field_name="supporting_refs",
        )
        if not supporting_refs:
            raise ValueError("supporting_refs must not be empty")
        object.__setattr__(self, "supporting_refs", supporting_refs)
        return self


class BlockingLineageEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    blocking_ref_id: str
    blocking_kind: str
    supporting_refs: list[str]

    @model_validator(mode="after")
    def _validate_entry(self) -> BlockingLineageEntry:
        object.__setattr__(
            self,
            "blocking_ref_id",
            _assert_non_empty_text(self.blocking_ref_id, field_name="blocking_ref_id"),
        )
        object.__setattr__(
            self,
            "blocking_kind",
            _assert_non_empty_text(self.blocking_kind, field_name="blocking_kind"),
        )
        supporting_refs = _sort_unique_ref_list(
            self.supporting_refs,
            field_name="supporting_refs",
        )
        if not supporting_refs:
            raise ValueError("supporting_refs must not be empty")
        object.__setattr__(self, "supporting_refs", supporting_refs)
        return self


class AdeuArchitectureAnalysisSettlementFrame(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_ANALYSIS_SETTLEMENT_FRAME_SCHEMA]
    settlement_frame_id: str
    analysis_request_id: str
    analysis_request_ref: str
    source_set_hash: str
    authority_boundary_policy: AuthorityBoundaryPolicyPin
    interpretation_register: list[InterpretationEntry]
    chosen_interpretation_id: str
    unresolved_high_impact_ambiguity_refs: list[str] = Field(default_factory=list)
    deontic_typing_register: list[DeonticTypingEntry] = Field(default_factory=list)
    claim_posture_register: list[ClaimPostureEntry] = Field(default_factory=list)
    affordance_decisions: list[AffordanceDecisionEntry] = Field(default_factory=list)
    escalation_trigger_policy: EscalationTriggerPolicy
    active_escalation_records: list[ActiveEscalationRecord] = Field(default_factory=list)
    compile_entitlement: CompileEntitlement
    blocking_lineage: list[BlockingLineageEntry] = Field(default_factory=list)
    advisory_notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_frame(
        self,
        info: ValidationInfo,
    ) -> "AdeuArchitectureAnalysisSettlementFrame":
        object.__setattr__(
            self,
            "settlement_frame_id",
            _assert_non_empty_text(self.settlement_frame_id, field_name="settlement_frame_id"),
        )
        object.__setattr__(
            self,
            "analysis_request_id",
            _assert_non_empty_text(self.analysis_request_id, field_name="analysis_request_id"),
        )
        analysis_request_ref = _normalize_ref(
            self.analysis_request_ref,
            field_name="analysis_request_ref",
        )
        object.__setattr__(self, "analysis_request_ref", analysis_request_ref)
        object.__setattr__(
            self,
            "source_set_hash",
            _assert_non_empty_text(self.source_set_hash, field_name="source_set_hash"),
        )
        object.__setattr__(
            self,
            "chosen_interpretation_id",
            _assert_non_empty_text(
                self.chosen_interpretation_id,
                field_name="chosen_interpretation_id",
            ),
        )
        object.__setattr__(
            self,
            "unresolved_high_impact_ambiguity_refs",
            _sort_unique_ref_list(
                self.unresolved_high_impact_ambiguity_refs,
                field_name="unresolved_high_impact_ambiguity_refs",
            ),
        )
        object.__setattr__(
            self,
            "advisory_notes",
            _assert_sorted_unique(self.advisory_notes, field_name="advisory_notes"),
        )

        interpretation_by_id = {
            entry.interpretation_id: entry for entry in self.interpretation_register
        }
        if len(interpretation_by_id) != len(self.interpretation_register):
            raise ValueError("interpretation_register must not contain duplicate interpretation_id")
        if not interpretation_by_id:
            raise ValueError("interpretation_register must not be empty")
        if self.chosen_interpretation_id not in interpretation_by_id:
            raise ValueError("chosen_interpretation_id must resolve inside interpretation_register")
        object.__setattr__(
            self,
            "interpretation_register",
            [interpretation_by_id[key] for key in sorted(interpretation_by_id)],
        )

        deontic_by_id = {entry.typing_id: entry for entry in self.deontic_typing_register}
        if len(deontic_by_id) != len(self.deontic_typing_register):
            raise ValueError("deontic_typing_register must not contain duplicate typing_id")
        object.__setattr__(
            self,
            "deontic_typing_register",
            [deontic_by_id[key] for key in sorted(deontic_by_id)],
        )

        decision_by_id = {entry.decision_id: entry for entry in self.affordance_decisions}
        if len(decision_by_id) != len(self.affordance_decisions):
            raise ValueError("affordance_decisions must not contain duplicate decision_id")
        object.__setattr__(
            self,
            "affordance_decisions",
            [decision_by_id[key] for key in sorted(decision_by_id)],
        )

        claim_by_id = {entry.claim_id: entry for entry in self.claim_posture_register}
        if len(claim_by_id) != len(self.claim_posture_register):
            raise ValueError("claim_posture_register must not contain duplicate claim_id")
        object.__setattr__(
            self,
            "claim_posture_register",
            [claim_by_id[key] for key in sorted(claim_by_id)],
        )

        escalation_by_id = {
            entry.trigger_id: entry for entry in self.active_escalation_records
        }
        if len(escalation_by_id) != len(self.active_escalation_records):
            raise ValueError("active_escalation_records must not contain duplicate trigger_id")
        object.__setattr__(
            self,
            "active_escalation_records",
            [escalation_by_id[key] for key in sorted(escalation_by_id)],
        )

        blocking_by_id = {entry.blocking_ref_id: entry for entry in self.blocking_lineage}
        if len(blocking_by_id) != len(self.blocking_lineage):
            raise ValueError("blocking_lineage must not contain duplicate blocking_ref_id")
        object.__setattr__(
            self,
            "blocking_lineage",
            [blocking_by_id[key] for key in sorted(blocking_by_id)],
        )

        repository_root = None
        request = None
        if info.context:
            repository_root = info.context.get("repository_root")
            request = info.context.get("analysis_request")
        if request is None and repository_root is not None:
            request = _load_analysis_request_from_ref(
                analysis_request_ref,
                repository_root=repository_root,
            )
        if request is not None:
            if self.analysis_request_id != request.analysis_request_id:
                raise ValueError("analysis_request_id must match released V41-A request boundary")
            if self.source_set_hash != request.source_set_hash:
                raise ValueError("source_set_hash must match released V41-A request boundary")
            if (
                self.authority_boundary_policy.model_dump(mode="json", exclude_none=False)
                != request.authority_boundary_policy.model_dump(mode="json", exclude_none=False)
            ):
                raise ValueError(
                    "authority_boundary_policy must match released V41-A request boundary"
                )

            refs_to_check = _typed_refs_from_frame(self)
            for ref in sorted(refs_to_check):
                if not _ref_resolves_to_request_boundary(
                    ref,
                    request=request,
                    analysis_request_ref=analysis_request_ref,
                ):
                    raise ValueError(
                        f"ref {ref!r} must resolve to the released V41-A request "
                        "or to an explicit artifact named by that request"
                    )

        affordance_targets = {
            entry.target_ref
            for entry in self.deontic_typing_register
            if entry.deontic_class in _AFFORDANCE_DEONTIC_CLASSES
        }
        decided_targets = {entry.target_ref for entry in self.affordance_decisions}
        missing_affordance_targets = sorted(affordance_targets - decided_targets)
        if missing_affordance_targets:
            raise ValueError(
                "request-bound affordances surfaced by deontic typing require "
                "affordance_decisions"
            )

        declared_triggers = set(self.escalation_trigger_policy.trigger_ids)
        for record in self.active_escalation_records:
            if record.trigger_id not in declared_triggers:
                raise ValueError(
                    f"active escalation trigger {record.trigger_id!r} is not declared "
                    "by escalation_trigger_policy"
                )

        has_unentitled_negative_claim = any(
            entry.posture_class == "unentitled_negative_claim"
            for entry in self.claim_posture_register
        )
        if self.compile_entitlement == "entitled":
            if self.unresolved_high_impact_ambiguity_refs:
                raise ValueError(
                    "compile_entitlement=entitled requires no unresolved_high_impact_ambiguity_refs"
                )
            if self.active_escalation_records:
                raise ValueError(
                    "compile_entitlement=entitled requires no active_escalation_records"
                )
            if has_unentitled_negative_claim:
                raise ValueError(
                    "compile_entitlement=entitled is illegal while "
                    "unentitled_negative_claim remains"
                )
            if self.blocking_lineage:
                raise ValueError("compile_entitlement=entitled must not carry blocking_lineage")
        elif not self.blocking_lineage:
            raise ValueError("compile_entitlement=blocked requires blocking_lineage")

        for note in self.advisory_notes:
            lowered = note.lower()
            if any(lowered.startswith(prefix) for prefix in _ADVISORY_NOTE_FORBIDDEN_PREFIXES):
                raise ValueError(
                    "advisory_notes may not introduce load-bearing settlement semantics"
                )

        return self


def canonicalize_adeu_architecture_analysis_settlement_frame_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest | None = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    request = analysis_request_payload
    if request is not None and not isinstance(request, AdeuArchitectureAnalysisRequest):
        request = AdeuArchitectureAnalysisRequest.model_validate(
            request,
            context={"repository_root": root},
        )
    return _dump_json_payload(
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context=_validation_context(root, analysis_request=request),
        )
    )


def materialize_adeu_architecture_analysis_settlement_frame_payload(
    payload_without_request_carry: dict[str, Any],
    *,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest,
    analysis_request_ref: str,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    request = analysis_request_payload
    if not isinstance(request, AdeuArchitectureAnalysisRequest):
        request = AdeuArchitectureAnalysisRequest.model_validate(
            request,
            context={"repository_root": root},
        )
    payload = deepcopy(payload_without_request_carry)
    payload["analysis_request_id"] = request.analysis_request_id
    payload["analysis_request_ref"] = analysis_request_ref
    payload["source_set_hash"] = request.source_set_hash
    payload["authority_boundary_policy"] = request.authority_boundary_policy.model_dump(
        mode="json",
        exclude_none=False,
    )
    payload.setdefault("unresolved_high_impact_ambiguity_refs", [])
    payload.setdefault("deontic_typing_register", [])
    payload.setdefault("claim_posture_register", [])
    payload.setdefault("affordance_decisions", [])
    payload.setdefault("active_escalation_records", [])
    payload.setdefault("blocking_lineage", [])
    payload.setdefault("advisory_notes", [])
    return canonicalize_adeu_architecture_analysis_settlement_frame_payload(
        payload,
        repository_root=root,
        analysis_request_payload=request,
    )
