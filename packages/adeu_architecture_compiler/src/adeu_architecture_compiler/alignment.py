from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from adeu_architecture_ir import (
    ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA,
    ADEU_ARCHITECTURE_ANALYSIS_SETTLEMENT_FRAME_SCHEMA,
    AdeuArchitectureAnalysisRequest,
    AdeuArchitectureAnalysisSettlementFrame,
    AdeuArchitectureSemanticIR,
)
from adeu_architecture_ir.analysis_request import AuthorityBoundaryPolicyPin
from pydantic import BaseModel, ConfigDict, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .conformance import (
    _assert_non_empty_text,
    _assert_sorted_unique,
    _load_repo_json,
    _normalize_repo_relative_path,
    _resolve_repository_root,
)
from .intended import _root_policy_from_request
from .observation import (
    ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA,
    AdeuArchitectureObservationFrame,
)

ADEU_ARCHITECTURE_ALIGNMENT_REPORT_SCHEMA = "adeu_architecture_alignment_report@1"
V41E_V87_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS87.md#v87-continuation-contract-machine-checkable"
)

AlignmentMismatchClass = Literal[
    "declared_not_observed",
    "observed_not_declared",
    "authority_boundary_drift",
    "workflow_or_state_drift",
    "evidence_or_observability_gap",
    "unresolved_unknown",
]
AlignmentSeverity = Literal["advisory", "warning", "blocking"]
AlignmentPosture = Literal["aligned", "drifted", "blocked"]
AlignmentBasisKind = Literal[
    "contradictory_evidence",
    "missing_observation",
    "missing_intended_declaration",
    "authority_mismatch",
    "unresolved_upstream_unknown",
]

_MISMATCH_PREFIX = {
    "declared_not_observed": "ALIGN-DNO-",
    "observed_not_declared": "ALIGN-OND-",
    "authority_boundary_drift": "ALIGN-ABD-",
    "workflow_or_state_drift": "ALIGN-WSD-",
    "evidence_or_observability_gap": "ALIGN-EOG-",
    "unresolved_unknown": "ALIGN-UNK-",
}
_HEX_64_RE = re.compile(r"^[0-9a-f]{64}$")
_PATHISH_PREFIXES = ("apps/", "artifacts/", "docs/", "packages/", "spec/")


def _validation_context(
    repository_root: Path | None = None,
    **extra: Any,
) -> dict[str, Any]:
    context = {"repository_root": repository_root}
    context.update(extra)
    return context


def _normalize_artifact_ref(raw_ref: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(raw_ref, field_name=field_name)
    if "#" not in normalized:
        return _normalize_repo_relative_path(normalized, field_name=field_name)
    path_part, fragment = normalized.split("#", 1)
    if not fragment.strip():
        raise ValueError(f"{field_name} must not end with an empty fragment")
    normalized_path = _normalize_repo_relative_path(path_part, field_name=field_name)
    return f"{normalized_path}#{fragment.strip()}"


def _artifact_ref_path(ref: str) -> str:
    return ref.split("#", 1)[0]


def _normalize_support_ref(raw_ref: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(raw_ref, field_name=field_name)
    if normalized.startswith(_PATHISH_PREFIXES) or "#" in normalized:
        return _normalize_artifact_ref(normalized, field_name=field_name)
    return normalized


def _sort_unique_artifact_refs(values: list[str], *, field_name: str) -> list[str]:
    normalized = {_normalize_artifact_ref(value, field_name=field_name) for value in values}
    return sorted(normalized)


def _sort_unique_support_refs(values: list[str], *, field_name: str) -> list[str]:
    normalized = {_normalize_support_ref(value, field_name=field_name) for value in values}
    return sorted(normalized)


def _normalize_evidence_requirement_id(value: str) -> str:
    normalized = _assert_non_empty_text(value, field_name="evidence_id")
    return normalized.removeprefix("ev_")


def _support_hash_payload(finding: "AlignmentFinding") -> dict[str, Any]:
    return {
        "mismatch_class": finding.mismatch_class,
        "basis_kind": finding.basis_kind,
        "intended_refs": finding.intended_refs,
        "observed_refs": finding.observed_refs,
        "request_support_refs": finding.request_support_refs,
        "settlement_support_refs": finding.settlement_support_refs,
    }


def _expected_finding_id(finding: "AlignmentFinding") -> str:
    digest = sha256_canonical_json(_support_hash_payload(finding))[:8]
    return f"{_MISMATCH_PREFIX[finding.mismatch_class]}{digest}"


def _canonical_policy_pin(
    policy: AuthorityBoundaryPolicyPin,
) -> dict[str, Any]:
    return policy.model_dump(mode="json", exclude_none=False)


def _semantic_source_map(semantic_ir: AdeuArchitectureSemanticIR) -> dict[str, str]:
    return {item.path: item.sha256 for item in semantic_ir.source_set.sources}


def _request_source_map(request: AdeuArchitectureAnalysisRequest) -> dict[str, str]:
    return {item.path: item.sha256 for item in request.source_set.items}


def _request_support_allowed_refs(
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


def _settlement_support_allowed_refs(
    settlement: AdeuArchitectureAnalysisSettlementFrame,
) -> set[str]:
    refs = {
        settlement.analysis_request_ref,
        settlement.chosen_interpretation_id,
        *settlement.unresolved_high_impact_ambiguity_refs,
        *settlement.escalation_trigger_policy.trigger_ids,
    }
    if settlement.authority_boundary_policy.policy_ref is not None:
        refs.add(settlement.authority_boundary_policy.policy_ref)
    for entry in settlement.interpretation_register:
        refs.add(entry.interpretation_id)
        refs.update(entry.support_refs)
        refs.update(entry.linked_ambiguity_refs)
    for entry in settlement.deontic_typing_register:
        refs.add(entry.typing_id)
        refs.add(entry.target_ref)
    for entry in settlement.affordance_decisions:
        refs.add(entry.decision_id)
        refs.add(entry.target_ref)
    for entry in settlement.claim_posture_register:
        refs.add(entry.claim_id)
        refs.add(entry.claim_ref)
    for entry in settlement.active_escalation_records:
        refs.add(entry.trigger_id)
        refs.update(entry.supporting_refs)
    for entry in settlement.blocking_lineage:
        refs.add(entry.blocking_ref_id)
        refs.update(entry.supporting_refs)
    return refs


def _observation_ref_ids(observation: AdeuArchitectureObservationFrame) -> set[str]:
    return {
        *(item.authority_source_id for item in observation.observed_authority_sources),
        *(item.boundary_id for item in observation.observed_boundaries),
        *(item.evidence_hook_id for item in observation.observed_evidence_hooks),
        *(item.observability_hook_id for item in observation.observed_observability_hooks),
        *(item.unit_id for item in observation.observed_units),
        *(item.workflow_id for item in observation.observed_workflows),
        *(item.observation_id for item in observation.unresolved_observations),
    }


def _semantic_ref_ids(semantic_ir: AdeuArchitectureSemanticIR) -> set[str]:
    return {
        *(item.source_ref_id for item in semantic_ir.source_set.sources),
        *(item.actor_id for item in semantic_ir.ontology.actors),
        *(item.surface_id for item in semantic_ir.ontology.surfaces),
        *(item.object_id for item in semantic_ir.ontology.data_objects),
        *(item.boundary_id for item in semantic_ir.ontology.boundaries),
        *(item.capability_id for item in semantic_ir.ontology.capabilities),
        *(item.workflow_id for item in semantic_ir.ontology.workflows),
        *(item.step_id for item in semantic_ir.ontology.flow_steps),
        *(item.state_id for item in semantic_ir.ontology.states),
        *(item.transition_id for item in semantic_ir.ontology.transitions),
        *(item.decision_id for item in semantic_ir.ontology.decisions),
        *(item.failure_mode_id for item in semantic_ir.ontology.failure_modes),
        *(item.evidence_id for item in semantic_ir.epistemics.evidence_requirements),
        *(item.hook_id for item in semantic_ir.epistemics.observability_hooks),
        *(item.fact_id for item in semantic_ir.epistemics.facts),
        *(item.assumption_id for item in semantic_ir.epistemics.assumptions),
        *(item.ambiguity_id for item in semantic_ir.epistemics.ambiguities),
        *(item.annotation_id for item in semantic_ir.epistemics.annotations),
        *(item.obligation_id for item in semantic_ir.deontics.obligations),
        *(item.prohibition_id for item in semantic_ir.deontics.prohibitions),
        *(item.permission_id for item in semantic_ir.deontics.permissions),
        *(item.gate_id for item in semantic_ir.deontics.gates),
        *(item.invariant_id for item in semantic_ir.deontics.invariants),
        *(item.rule_id for item in semantic_ir.deontics.escalation_rules),
        *(item.goal_id for item in semantic_ir.utility.goals),
        *(item.metric_id for item in semantic_ir.utility.metrics),
        *(item.priority_id for item in semantic_ir.utility.priority_rules),
        *(item.tradeoff_id for item in semantic_ir.utility.tradeoffs),
    }


def _load_analysis_request_from_ref(
    analysis_request_ref: str,
    *,
    repository_root: Path,
) -> AdeuArchitectureAnalysisRequest:
    payload = _load_repo_json(
        _artifact_ref_path(analysis_request_ref),
        repository_root=repository_root,
    )
    if payload.get("schema") != ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA:
        raise ValueError(
            "analysis_request_ref must resolve to adeu_architecture_analysis_request@1"
        )
    return AdeuArchitectureAnalysisRequest.model_validate(
        payload,
        context={"repository_root": repository_root},
    )


def _load_settlement_from_ref(
    settlement_frame_ref: str,
    *,
    repository_root: Path,
    request: AdeuArchitectureAnalysisRequest,
) -> AdeuArchitectureAnalysisSettlementFrame:
    payload = _load_repo_json(
        _artifact_ref_path(settlement_frame_ref),
        repository_root=repository_root,
    )
    if payload.get("schema") != ADEU_ARCHITECTURE_ANALYSIS_SETTLEMENT_FRAME_SCHEMA:
        raise ValueError(
            "settlement_frame_ref must resolve to "
            "adeu_architecture_analysis_settlement_frame@1"
        )
    return AdeuArchitectureAnalysisSettlementFrame.model_validate(
        payload,
        context=_validation_context(repository_root, analysis_request=request),
    )


def _load_observation_from_ref(
    observation_frame_ref: str,
    *,
    repository_root: Path,
    request: AdeuArchitectureAnalysisRequest,
    settlement: AdeuArchitectureAnalysisSettlementFrame,
) -> AdeuArchitectureObservationFrame:
    payload = _load_repo_json(
        _artifact_ref_path(observation_frame_ref),
        repository_root=repository_root,
    )
    if payload.get("schema") != ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA:
        raise ValueError(
            "observation_frame_ref must resolve to adeu_architecture_observation_frame@1"
        )
    return AdeuArchitectureObservationFrame.model_validate(
        payload,
        context=_validation_context(
            repository_root,
            analysis_request=request,
            analysis_settlement=settlement,
        ),
    )


def _slug(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", value.lower()).strip("_")


@dataclass(frozen=True)
class V41EValidatedInputs:
    analysis_request: AdeuArchitectureAnalysisRequest
    analysis_request_ref: str
    settlement_frame: AdeuArchitectureAnalysisSettlementFrame
    settlement_frame_ref: str
    observation_frame: AdeuArchitectureObservationFrame
    observation_frame_ref: str
    semantic_ir: AdeuArchitectureSemanticIR
    repository_root: Path


class AlignmentSeverityCounts(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    advisory: int
    warning: int
    blocking: int

    @model_validator(mode="after")
    def _validate_counts(self) -> "AlignmentSeverityCounts":
        for field_name in ("advisory", "warning", "blocking"):
            value = getattr(self, field_name)
            if value < 0:
                raise ValueError(f"severity_counts.{field_name} must be non-negative")
        return self


class AlignmentFinding(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    finding_id: str
    mismatch_class: AlignmentMismatchClass
    basis_kind: AlignmentBasisKind
    severity: AlignmentSeverity
    summary: str
    intended_refs: list[str]
    observed_refs: list[str]
    request_support_refs: list[str]
    settlement_support_refs: list[str]

    @model_validator(mode="after")
    def _validate_finding(self, info: ValidationInfo) -> "AlignmentFinding":
        object.__setattr__(
            self,
            "finding_id",
            _assert_non_empty_text(self.finding_id, field_name="finding_id"),
        )
        object.__setattr__(
            self,
            "summary",
            _assert_non_empty_text(self.summary, field_name="summary"),
        )
        object.__setattr__(
            self,
            "intended_refs",
            _assert_sorted_unique(self.intended_refs, field_name="intended_refs"),
        )
        object.__setattr__(
            self,
            "observed_refs",
            _assert_sorted_unique(self.observed_refs, field_name="observed_refs"),
        )
        object.__setattr__(
            self,
            "request_support_refs",
            _sort_unique_artifact_refs(
                self.request_support_refs,
                field_name="request_support_refs",
            ),
        )
        object.__setattr__(
            self,
            "settlement_support_refs",
            _sort_unique_support_refs(
                self.settlement_support_refs,
                field_name="settlement_support_refs",
            ),
        )
        if not (
            self.intended_refs
            or self.observed_refs
            or self.request_support_refs
            or self.settlement_support_refs
        ):
            raise ValueError(
                "findings must resolve to at least one typed intended, observed, request, "
                "or settlement support ref"
            )
        expected_finding_id = _expected_finding_id(self)
        if self.finding_id != expected_finding_id:
            raise ValueError("finding_id must match the canonical support-tuple hash")
        if info.context:
            intended_ref_ids = info.context.get("intended_ref_ids")
            if intended_ref_ids is not None and not set(self.intended_refs).issubset(
                intended_ref_ids
            ):
                raise ValueError("intended_refs must resolve to consumed intended semantic refs")
            observed_ref_ids = info.context.get("observed_ref_ids")
            if observed_ref_ids is not None and not set(self.observed_refs).issubset(
                observed_ref_ids
            ):
                raise ValueError("observed_refs must resolve to consumed observation refs")
            request_allowed = info.context.get("request_support_allowed_refs")
            if request_allowed is not None and not set(self.request_support_refs).issubset(
                request_allowed
            ):
                raise ValueError(
                    "request_support_refs must resolve inside the consumed request boundary"
                )
            settlement_allowed = info.context.get("settlement_support_allowed_refs")
            if settlement_allowed is not None and not set(self.settlement_support_refs).issubset(
                settlement_allowed
            ):
                raise ValueError(
                    "settlement_support_refs must resolve inside the consumed settlement frame"
                )
        return self


class AdeuArchitectureAlignmentReport(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_ALIGNMENT_REPORT_SCHEMA]
    alignment_report_id: str
    analysis_request_id: str
    analysis_request_ref: str
    settlement_frame_id: str
    settlement_frame_ref: str
    observation_frame_id: str
    observation_frame_ref: str
    architecture_id: str
    semantic_hash: str
    source_set_hash: str
    authority_boundary_policy: AuthorityBoundaryPolicyPin
    alignment_posture: AlignmentPosture
    blocking_finding_ids: list[str]
    severity_counts: AlignmentSeverityCounts
    findings: list[AlignmentFinding]

    @model_validator(mode="after")
    def _validate_report(self, info: ValidationInfo) -> "AdeuArchitectureAlignmentReport":
        object.__setattr__(
            self,
            "alignment_report_id",
            _assert_non_empty_text(self.alignment_report_id, field_name="alignment_report_id"),
        )
        object.__setattr__(
            self,
            "analysis_request_id",
            _assert_non_empty_text(self.analysis_request_id, field_name="analysis_request_id"),
        )
        object.__setattr__(
            self,
            "analysis_request_ref",
            _normalize_artifact_ref(
                self.analysis_request_ref,
                field_name="analysis_request_ref",
            ),
        )
        object.__setattr__(
            self,
            "settlement_frame_id",
            _assert_non_empty_text(self.settlement_frame_id, field_name="settlement_frame_id"),
        )
        object.__setattr__(
            self,
            "settlement_frame_ref",
            _normalize_artifact_ref(
                self.settlement_frame_ref,
                field_name="settlement_frame_ref",
            ),
        )
        object.__setattr__(
            self,
            "observation_frame_id",
            _assert_non_empty_text(self.observation_frame_id, field_name="observation_frame_id"),
        )
        object.__setattr__(
            self,
            "observation_frame_ref",
            _normalize_artifact_ref(
                self.observation_frame_ref,
                field_name="observation_frame_ref",
            ),
        )
        object.__setattr__(
            self,
            "architecture_id",
            _assert_non_empty_text(self.architecture_id, field_name="architecture_id"),
        )
        semantic_hash = _assert_non_empty_text(self.semantic_hash, field_name="semantic_hash")
        if not _HEX_64_RE.fullmatch(semantic_hash):
            raise ValueError("semantic_hash must be a 64-character lowercase hex sha256")
        object.__setattr__(self, "semantic_hash", semantic_hash)
        source_set_hash = _assert_non_empty_text(
            self.source_set_hash,
            field_name="source_set_hash",
        )
        if not _HEX_64_RE.fullmatch(source_set_hash):
            raise ValueError("source_set_hash must be a 64-character lowercase hex sha256")
        object.__setattr__(self, "source_set_hash", source_set_hash)
        object.__setattr__(
            self,
            "blocking_finding_ids",
            _assert_sorted_unique(
                self.blocking_finding_ids,
                field_name="blocking_finding_ids",
            ),
        )

        deduplicated: dict[str, AlignmentFinding] = {}
        for finding in self.findings:
            support_hash = _expected_finding_id(finding)
            existing = deduplicated.get(support_hash)
            if existing is not None:
                if existing.model_dump(mode="json") != finding.model_dump(mode="json"):
                    raise ValueError(
                        "duplicate findings with the same canonical support tuple must "
                        "collapse before report materialization"
                    )
                continue
            deduplicated[support_hash] = finding
        ordered_findings = [deduplicated[key] for key in sorted(deduplicated)]
        object.__setattr__(self, "findings", ordered_findings)

        expected_blocking = sorted(
            finding.finding_id
            for finding in ordered_findings
            if finding.severity == "blocking"
        )
        if self.blocking_finding_ids != expected_blocking:
            raise ValueError(
                "blocking_finding_ids must match the canonical set of blocking findings"
            )

        expected_counts = {
            "advisory": sum(1 for finding in ordered_findings if finding.severity == "advisory"),
            "warning": sum(1 for finding in ordered_findings if finding.severity == "warning"),
            "blocking": sum(1 for finding in ordered_findings if finding.severity == "blocking"),
        }
        if self.severity_counts.model_dump(mode="json") != expected_counts:
            raise ValueError(
                "severity_counts must be derived from the canonical deduplicated finding set"
            )

        if not ordered_findings:
            expected_posture: AlignmentPosture = "aligned"
        elif expected_blocking:
            expected_posture = "blocked"
        else:
            expected_posture = "drifted"
        if self.alignment_posture != expected_posture:
            raise ValueError(
                "alignment_posture must match the canonical deduplicated finding set"
            )

        if info.context:
            request = info.context.get("analysis_request")
            settlement = info.context.get("analysis_settlement")
            observation = info.context.get("observation_frame")
            semantic_ir = info.context.get("semantic_ir")
            if request is not None:
                if self.analysis_request_id != request.analysis_request_id:
                    raise ValueError(
                        "analysis_request_id must match the consumed analysis request"
                    )
                if self.source_set_hash != request.source_set_hash:
                    raise ValueError(
                        "source_set_hash must match the consumed analysis request"
                    )
                expected_policy = _canonical_policy_pin(request.authority_boundary_policy)
                if (
                    self.authority_boundary_policy.model_dump(
                        mode="json",
                        exclude_none=False,
                    )
                    != expected_policy
                ):
                    raise ValueError(
                        "authority_boundary_policy must match the consumed request boundary"
                    )
            if settlement is not None:
                if self.settlement_frame_id != settlement.settlement_frame_id:
                    raise ValueError(
                        "settlement_frame_id must match the consumed settlement frame"
                    )
                if self.analysis_request_ref != settlement.analysis_request_ref:
                    raise ValueError(
                        "analysis_request_ref must match the consumed settlement frame lineage"
                    )
            if observation is not None:
                if self.observation_frame_id != observation.observation_frame_id:
                    raise ValueError(
                        "observation_frame_id must match the consumed observation frame"
                    )
                if self.analysis_request_ref != observation.analysis_request_ref:
                    raise ValueError(
                        "analysis_request_ref must match the consumed observation frame lineage"
                    )
                if self.settlement_frame_ref != observation.settlement_frame_ref:
                    raise ValueError(
                        "settlement_frame_ref must match the consumed observation frame lineage"
                    )
            if semantic_ir is not None:
                if self.architecture_id != semantic_ir.architecture_id:
                    raise ValueError("architecture_id must match the consumed semantic root")
                if self.semantic_hash != semantic_ir.semantic_hash:
                    raise ValueError("semantic_hash must match the consumed semantic root")
        return self


def canonicalize_adeu_architecture_alignment_report_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest | None = None,
    analysis_settlement_payload: (
        dict[str, Any] | AdeuArchitectureAnalysisSettlementFrame | None
    ) = None,
    observation_frame_payload: dict[str, Any] | AdeuArchitectureObservationFrame | None = None,
    semantic_ir_payload: dict[str, Any] | AdeuArchitectureSemanticIR | None = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    request = analysis_request_payload
    if request is not None and not isinstance(request, AdeuArchitectureAnalysisRequest):
        request = AdeuArchitectureAnalysisRequest.model_validate(
            request,
            context={"repository_root": root},
        )
    settlement = analysis_settlement_payload
    if settlement is not None and not isinstance(
        settlement,
        AdeuArchitectureAnalysisSettlementFrame,
    ):
        settlement = AdeuArchitectureAnalysisSettlementFrame.model_validate(
            settlement,
            context=_validation_context(root, analysis_request=request),
        )
    observation = observation_frame_payload
    if observation is not None and not isinstance(observation, AdeuArchitectureObservationFrame):
        observation = AdeuArchitectureObservationFrame.model_validate(
            observation,
            context=_validation_context(
                root,
                analysis_request=request,
                analysis_settlement=settlement,
            ),
        )
    semantic_ir = semantic_ir_payload
    if semantic_ir is not None and not isinstance(semantic_ir, AdeuArchitectureSemanticIR):
        semantic_ir = AdeuArchitectureSemanticIR.model_validate(
            semantic_ir,
            context={"repository_root": root},
        )

    request_allowed: set[str] | None = None
    settlement_allowed: set[str] | None = None
    observed_ref_ids: set[str] | None = None
    intended_ref_ids: set[str] | None = None
    if request is not None:
        request_ref = payload.get("analysis_request_ref")
        if isinstance(request_ref, str):
            request_allowed = _request_support_allowed_refs(
                request,
                analysis_request_ref=_normalize_artifact_ref(
                    request_ref,
                    field_name="analysis_request_ref",
                ),
            )
    if settlement is not None:
        settlement_allowed = _settlement_support_allowed_refs(settlement)
    if observation is not None:
        observed_ref_ids = _observation_ref_ids(observation)
    if semantic_ir is not None:
        intended_ref_ids = _semantic_ref_ids(semantic_ir)

    return AdeuArchitectureAlignmentReport.model_validate(
        payload,
        context=_validation_context(
            root,
            analysis_request=request,
            analysis_settlement=settlement,
            observation_frame=observation,
            semantic_ir=semantic_ir,
            request_support_allowed_refs=request_allowed,
            settlement_support_allowed_refs=settlement_allowed,
            observed_ref_ids=observed_ref_ids,
            intended_ref_ids=intended_ref_ids,
        ),
    ).model_dump(mode="json", exclude_none=True)


def _validate_v41e_inputs(
    *,
    analysis_request_payload: dict[str, Any],
    analysis_request_path: str,
    settlement_frame_payload: dict[str, Any],
    settlement_frame_path: str,
    observation_frame_payload: dict[str, Any],
    observation_frame_path: str,
    semantic_ir_payload: dict[str, Any],
    repository_root: Path | None = None,
) -> V41EValidatedInputs:
    root = _resolve_repository_root(repository_root)
    normalized_request_ref = _normalize_artifact_ref(
        analysis_request_path,
        field_name="analysis_request_path",
    )
    normalized_settlement_ref = _normalize_artifact_ref(
        settlement_frame_path,
        field_name="settlement_frame_path",
    )
    normalized_observation_ref = _normalize_artifact_ref(
        observation_frame_path,
        field_name="observation_frame_path",
    )

    request = AdeuArchitectureAnalysisRequest.model_validate(
        analysis_request_payload,
        context={"repository_root": root},
    )
    settlement = AdeuArchitectureAnalysisSettlementFrame.model_validate(
        settlement_frame_payload,
        context=_validation_context(root, analysis_request=request),
    )
    if settlement.compile_entitlement != "entitled":
        raise ValueError("V41-E alignment requires released compile_entitlement=entitled")
    if settlement.blocking_lineage:
        raise ValueError("entitled V41-E settlement must not carry blocking_lineage")
    observation = AdeuArchitectureObservationFrame.model_validate(
        observation_frame_payload,
        context=_validation_context(
            root,
            analysis_request=request,
            analysis_settlement=settlement,
        ),
    )
    semantic_ir = AdeuArchitectureSemanticIR.model_validate(
        semantic_ir_payload,
        context={"repository_root": root},
    )

    if settlement.analysis_request_ref != normalized_request_ref:
        raise ValueError(
            "settlement_frame.analysis_request_ref must match the consumed analysis_request_path"
        )
    if observation.analysis_request_ref != normalized_request_ref:
        raise ValueError(
            "observation_frame.analysis_request_ref must match the consumed analysis_request_path"
        )
    if observation.settlement_frame_ref != normalized_settlement_ref:
        raise ValueError(
            "observation_frame.settlement_frame_ref must match the consumed settlement_frame_path"
        )
    if observation.upstream_compile_entitlement != "entitled":
        raise ValueError(
            "observation_frame must carry through upstream_compile_entitlement=entitled"
        )
    if observation.upstream_blocking_refs:
        raise ValueError("entitled V41-E observation_frame must not carry upstream_blocking_refs")
    if settlement.analysis_request_id != request.analysis_request_id:
        raise ValueError("settlement_frame analysis_request_id must match the consumed request")
    if observation.analysis_request_id != request.analysis_request_id:
        raise ValueError("observation_frame analysis_request_id must match the consumed request")
    if observation.settlement_frame_id != settlement.settlement_frame_id:
        raise ValueError("observation_frame settlement_frame_id must match settlement_frame")
    if settlement.source_set_hash != request.source_set_hash:
        raise ValueError("settlement_frame source_set_hash must match the consumed request")
    if observation.source_set_hash != request.source_set_hash:
        raise ValueError("observation_frame source_set_hash must match the consumed request")
    if _canonical_policy_pin(settlement.authority_boundary_policy) != _canonical_policy_pin(
        request.authority_boundary_policy
    ):
        raise ValueError(
            "settlement_frame authority_boundary_policy must match the consumed request"
        )
    if _canonical_policy_pin(observation.authority_boundary_policy) != _canonical_policy_pin(
        request.authority_boundary_policy
    ):
        raise ValueError(
            "observation_frame authority_boundary_policy must match the consumed request"
        )
    expected_semantic_policy = _root_policy_from_request(request)
    if (
        semantic_ir.authority_boundary_policy.model_dump(mode="json", exclude_none=False)
        != expected_semantic_policy
    ):
        raise ValueError(
            "semantic_ir authority_boundary_policy must match the request-bound intended policy"
        )
    if _semantic_source_map(semantic_ir) != _request_source_map(request):
        raise ValueError(
            "semantic_ir source_set must match the consumed request source_set exactly"
        )

    return V41EValidatedInputs(
        analysis_request=request,
        analysis_request_ref=normalized_request_ref,
        settlement_frame=settlement,
        settlement_frame_ref=normalized_settlement_ref,
        observation_frame=observation,
        observation_frame_ref=normalized_observation_ref,
        semantic_ir=semantic_ir,
        repository_root=root,
    )


def _default_alignment_report_id(request: AdeuArchitectureAnalysisRequest) -> str:
    scope_slug = _slug(request.request_scope.subtree_root)
    return f"v41e_v87_{scope_slug}_alignment_report"


def _matching_ambiguity_ids(
    observation_id: str,
    *,
    semantic_ir: AdeuArchitectureSemanticIR,
) -> list[str]:
    matches: list[str] = []
    for ambiguity in semantic_ir.epistemics.ambiguities:
        if observation_id in ambiguity.ambiguity_id or observation_id in ambiguity.question:
            matches.append(ambiguity.ambiguity_id)
    return sorted(set(matches))


def _default_request_support_refs(
    request: AdeuArchitectureAnalysisRequest,
) -> list[str]:
    refs = [*request.accepted_doc_refs, *request.maintainer_brief_refs]
    return _sort_unique_artifact_refs(refs, field_name="request_support_refs")


def _request_support_refs_for_paths(
    refs: list[str],
    *,
    request: AdeuArchitectureAnalysisRequest,
) -> list[str]:
    request_paths = {item.path for item in request.source_set.items}
    resolved = sorted({ref for ref in refs if ref in request_paths})
    if resolved:
        return _sort_unique_artifact_refs(resolved, field_name="request_support_refs")
    return _default_request_support_refs(request)


def _blocking_summary(observation_id: str) -> str:
    return (
        f"Upstream unresolved observation {observation_id} remains unresolved in the "
        "released intended/observed comparison world and must stay explicit in the "
        "alignment report."
    )


def _make_finding(
    *,
    mismatch_class: AlignmentMismatchClass,
    basis_kind: AlignmentBasisKind,
    severity: AlignmentSeverity,
    summary: str,
    intended_refs: list[str],
    observed_refs: list[str],
    request_support_refs: list[str],
    settlement_support_refs: list[str],
    context: dict[str, Any],
) -> AlignmentFinding:
    prototype = AlignmentFinding.model_construct(
        finding_id="pending",
        mismatch_class=mismatch_class,
        basis_kind=basis_kind,
        severity=severity,
        summary=summary,
        intended_refs=_assert_sorted_unique(intended_refs, field_name="intended_refs"),
        observed_refs=_assert_sorted_unique(observed_refs, field_name="observed_refs"),
        request_support_refs=_sort_unique_artifact_refs(
            request_support_refs,
            field_name="request_support_refs",
        ),
        settlement_support_refs=_sort_unique_support_refs(
            settlement_support_refs,
            field_name="settlement_support_refs",
        ),
    )
    finding_id = _expected_finding_id(prototype)
    payload = prototype.model_dump(mode="json")
    payload["finding_id"] = finding_id
    return AlignmentFinding.model_validate(payload, context=context)


def _finding_context(validated: V41EValidatedInputs) -> dict[str, Any]:
    return _validation_context(
        validated.repository_root,
        intended_ref_ids=_semantic_ref_ids(validated.semantic_ir),
        observed_ref_ids=_observation_ref_ids(validated.observation_frame),
        request_support_allowed_refs=_request_support_allowed_refs(
            validated.analysis_request,
            analysis_request_ref=validated.analysis_request_ref,
        ),
        settlement_support_allowed_refs=_settlement_support_allowed_refs(
            validated.settlement_frame
        ),
    )


def _derive_unresolved_unknown_findings(
    validated: V41EValidatedInputs,
    *,
    context: dict[str, Any],
) -> list[AlignmentFinding]:
    findings: list[AlignmentFinding] = []
    settlement_support_refs = [validated.settlement_frame.chosen_interpretation_id]
    for unresolved in validated.observation_frame.unresolved_observations:
        findings.append(
            _make_finding(
                mismatch_class="unresolved_unknown",
                basis_kind="unresolved_upstream_unknown",
                severity="blocking",
                summary=_blocking_summary(unresolved.observation_id),
                intended_refs=_matching_ambiguity_ids(
                    unresolved.observation_id,
                    semantic_ir=validated.semantic_ir,
                ),
                observed_refs=[unresolved.observation_id],
                request_support_refs=_request_support_refs_for_paths(
                    unresolved.source_refs,
                    request=validated.analysis_request,
                ),
                settlement_support_refs=settlement_support_refs,
                context=context,
            )
        )
    return findings


def _derive_observability_gap_findings(
    validated: V41EValidatedInputs,
    *,
    context: dict[str, Any],
) -> list[AlignmentFinding]:
    findings: list[AlignmentFinding] = []
    observed_by_kind = {
        hook.observable_kind: hook.observability_hook_id
        for hook in validated.observation_frame.observed_observability_hooks
    }
    intended_by_kind: dict[str, list[str]] = {}
    for hook in validated.semantic_ir.epistemics.observability_hooks:
        intended_by_kind.setdefault(hook.observable_kind, []).append(hook.hook_id)
    settlement_support_refs = [validated.settlement_frame.chosen_interpretation_id]
    for observable_kind, intended_refs in sorted(intended_by_kind.items()):
        if observable_kind in observed_by_kind:
            continue
        request_support_refs = _request_support_refs_for_paths(
            [
                item.path
                for item in validated.analysis_request.source_set.items
                if observable_kind in item.path.lower()
            ],
            request=validated.analysis_request,
        )
        findings.append(
            _make_finding(
                mismatch_class="evidence_or_observability_gap",
                basis_kind="missing_observation",
                severity="warning",
                summary=(
                    f"Intended observability kind {observable_kind!r} is declared in the "
                    "released semantic root but no matching observed hook is present."
                ),
                intended_refs=intended_refs,
                observed_refs=[],
                request_support_refs=request_support_refs,
                settlement_support_refs=settlement_support_refs,
                context=context,
            )
        )
    return findings


def _derive_evidence_hook_findings(
    validated: V41EValidatedInputs,
    *,
    context: dict[str, Any],
) -> list[AlignmentFinding]:
    findings: list[AlignmentFinding] = []
    observed_hooks = {
        hook.evidence_hook_id: hook
        for hook in validated.observation_frame.observed_evidence_hooks
    }
    observed_ids = set(observed_hooks)
    intended_ids = {
        _normalize_evidence_requirement_id(evidence.evidence_id): evidence.evidence_id
        for evidence in validated.semantic_ir.epistemics.evidence_requirements
    }
    settlement_support_refs = [validated.settlement_frame.chosen_interpretation_id]

    for normalized_id, evidence_id in sorted(intended_ids.items()):
        if normalized_id in observed_ids:
            continue
        findings.append(
            _make_finding(
                mismatch_class="declared_not_observed",
                basis_kind="missing_observation",
                severity="warning",
                summary=(
                    f"Intended evidence requirement {evidence_id} is declared but no matching "
                    "observed evidence hook is present."
                ),
                intended_refs=[evidence_id],
                observed_refs=[],
                request_support_refs=_default_request_support_refs(validated.analysis_request),
                settlement_support_refs=settlement_support_refs,
                context=context,
            )
        )

    for observed_id in sorted(observed_ids - set(intended_ids)):
        hook = observed_hooks[observed_id]
        findings.append(
            _make_finding(
                mismatch_class="observed_not_declared",
                basis_kind="missing_intended_declaration",
                severity="warning",
                summary=(
                    f"Observed evidence hook {observed_id} is not declared in the released "
                    "intended semantic root."
                ),
                intended_refs=[],
                observed_refs=[observed_id],
                request_support_refs=_request_support_refs_for_paths(
                    hook.source_refs,
                    request=validated.analysis_request,
                ),
                settlement_support_refs=settlement_support_refs,
                context=context,
            )
        )
    return findings


def derive_v41e_alignment_report(
    *,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest,
    analysis_request_path: str,
    settlement_frame_payload: dict[str, Any] | AdeuArchitectureAnalysisSettlementFrame,
    settlement_frame_path: str,
    observation_frame_payload: dict[str, Any] | AdeuArchitectureObservationFrame,
    observation_frame_path: str,
    semantic_ir_payload: dict[str, Any] | AdeuArchitectureSemanticIR,
    alignment_report_id: str | None = None,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    validated = _validate_v41e_inputs(
        analysis_request_payload=(
            analysis_request_payload.model_dump(mode="json")
            if isinstance(analysis_request_payload, AdeuArchitectureAnalysisRequest)
            else analysis_request_payload
        ),
        analysis_request_path=analysis_request_path,
        settlement_frame_payload=(
            settlement_frame_payload.model_dump(mode="json")
            if isinstance(settlement_frame_payload, AdeuArchitectureAnalysisSettlementFrame)
            else settlement_frame_payload
        ),
        settlement_frame_path=settlement_frame_path,
        observation_frame_payload=(
            observation_frame_payload.model_dump(mode="json")
            if isinstance(observation_frame_payload, AdeuArchitectureObservationFrame)
            else observation_frame_payload
        ),
        observation_frame_path=observation_frame_path,
        semantic_ir_payload=(
            semantic_ir_payload.model_dump(mode="json")
            if isinstance(semantic_ir_payload, AdeuArchitectureSemanticIR)
            else semantic_ir_payload
        ),
        repository_root=repository_root,
    )
    context = _finding_context(validated)
    findings = [
        *_derive_unresolved_unknown_findings(validated, context=context),
        *_derive_observability_gap_findings(validated, context=context),
        *_derive_evidence_hook_findings(validated, context=context),
    ]
    blocking_finding_ids = sorted(
        finding.finding_id for finding in findings if finding.severity == "blocking"
    )
    severity_counts = {
        "advisory": sum(1 for finding in findings if finding.severity == "advisory"),
        "warning": sum(1 for finding in findings if finding.severity == "warning"),
        "blocking": sum(1 for finding in findings if finding.severity == "blocking"),
    }
    if not findings:
        alignment_posture: AlignmentPosture = "aligned"
    elif blocking_finding_ids:
        alignment_posture = "blocked"
    else:
        alignment_posture = "drifted"

    payload = {
        "schema": ADEU_ARCHITECTURE_ALIGNMENT_REPORT_SCHEMA,
        "alignment_report_id": alignment_report_id
        or _default_alignment_report_id(validated.analysis_request),
        "analysis_request_id": validated.analysis_request.analysis_request_id,
        "analysis_request_ref": validated.analysis_request_ref,
        "settlement_frame_id": validated.settlement_frame.settlement_frame_id,
        "settlement_frame_ref": validated.settlement_frame_ref,
        "observation_frame_id": validated.observation_frame.observation_frame_id,
        "observation_frame_ref": validated.observation_frame_ref,
        "architecture_id": validated.semantic_ir.architecture_id,
        "semantic_hash": validated.semantic_ir.semantic_hash,
        "source_set_hash": validated.analysis_request.source_set_hash,
        "authority_boundary_policy": (
            validated.analysis_request.authority_boundary_policy.model_dump(
                mode="json",
                exclude_none=False,
            )
        ),
        "alignment_posture": alignment_posture,
        "blocking_finding_ids": blocking_finding_ids,
        "severity_counts": severity_counts,
        "findings": [finding.model_dump(mode="json") for finding in findings],
    }
    return canonicalize_adeu_architecture_alignment_report_payload(
        payload,
        repository_root=validated.repository_root,
        analysis_request_payload=validated.analysis_request,
        analysis_settlement_payload=validated.settlement_frame,
        observation_frame_payload=validated.observation_frame,
        semantic_ir_payload=validated.semantic_ir,
    )


__all__ = [
    "ADEU_ARCHITECTURE_ALIGNMENT_REPORT_SCHEMA",
    "V41E_V87_CONTRACT_SOURCE",
    "AdeuArchitectureAlignmentReport",
    "AlignmentFinding",
    "AlignmentSeverityCounts",
    "canonicalize_adeu_architecture_alignment_report_payload",
    "derive_v41e_alignment_report",
]
