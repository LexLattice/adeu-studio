from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from adeu_architecture_ir import (
    AdeuArchitectureAnalysisRequest,
    AdeuArchitectureAnalysisSettlementFrame,
    AdeuArchitectureSemanticIR,
    canonicalize_adeu_architecture_analysis_request_payload,
    canonicalize_adeu_architecture_analysis_settlement_frame_payload,
    materialize_adeu_architecture_analysis_request_payload,
    materialize_adeu_architecture_analysis_settlement_frame_payload,
)
from adeu_architecture_ir.analysis_request import AuthorityBoundaryPolicyPin
from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .alignment import (
    AdeuArchitectureAlignmentReport,
    derive_v41e_alignment_report,
)
from .conformance import (
    _assert_non_empty_text,
    _normalize_repo_relative_path,
    _resolve_repository_root,
)
from .intended import derive_v41d_semantic_ir
from .observation import (
    AdeuArchitectureObservationFrame,
    _normalize_artifact_ref,
    derive_v41c_observation_frame,
)

ADEU_ARCHITECTURE_ANALYSIS_RUN_MANIFEST_SCHEMA = (
    "adeu_architecture_analysis_run_manifest@1"
)
V41F_V88_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS88.md#v88-continuation-contract-machine-checkable"
)

AnalysisRunOutcome = Literal["completed", "blocked"]
AnalysisRunStopReasonKind = Literal["none", "settlement_blocked"]
AnalysisRunTerminalAlignmentPosture = Literal["none", "aligned", "drifted", "blocked"]
AnalysisRunStageId = Literal[
    "request",
    "settlement",
    "observation",
    "intended",
    "alignment",
    "manifest",
]
AnalysisRunStageState = Literal["completed", "not_run"]

_RUNNER_NAME = "adeu_architecture_compiler.v41f"
_RUNNER_MODE = "cli_first"
_CANONICAL_STAGE_IDS: tuple[AnalysisRunStageId, ...] = (
    "request",
    "settlement",
    "observation",
    "intended",
    "alignment",
    "manifest",
)
_ABSENT_MARKER = "__absent__"


def _validation_context(
    repository_root: Path | None = None,
    **extra: Any,
) -> dict[str, Any]:
    context = {"repository_root": repository_root}
    context.update(extra)
    return context


def _normalize_optional_artifact_ref(
    value: str | None,
    *,
    field_name: str,
) -> str | None:
    if value is None:
        return None
    return _normalize_artifact_ref(value, field_name=field_name)


def _normalize_output_root(raw_path: str, *, field_name: str) -> str:
    return _normalize_repo_relative_path(raw_path, field_name=field_name)


def _runner_identity_payload(runner: "ArchitectureAnalysisRunner") -> dict[str, str]:
    return {
        "name": runner.name,
        "version": runner.version,
        "mode": runner.mode,
    }


def _expected_run_id(
    *,
    analysis_request_id: str,
    settlement_frame_id: str,
    observation_frame_id: str,
    semantic_ir_id: str | None,
    alignment_report_id: str | None,
    runner: "ArchitectureAnalysisRunner",
) -> str:
    digest = sha256_canonical_json(
        {
            "analysis_request_id": analysis_request_id,
            "settlement_frame_id": settlement_frame_id,
            "observation_frame_id": observation_frame_id,
            "semantic_ir_id": semantic_ir_id or _ABSENT_MARKER,
            "alignment_report_id": alignment_report_id or _ABSENT_MARKER,
            "runner": _runner_identity_payload(runner),
        }
    )[:16]
    return f"run_v88_{digest}"


def _expected_stage_statuses(
    outcome: AnalysisRunOutcome,
) -> list[dict[str, str]]:
    if outcome == "blocked":
        states: dict[AnalysisRunStageId, AnalysisRunStageState] = {
            "request": "completed",
            "settlement": "completed",
            "observation": "completed",
            "intended": "not_run",
            "alignment": "not_run",
            "manifest": "completed",
        }
    else:
        states = {stage_id: "completed" for stage_id in _CANONICAL_STAGE_IDS}
    return [
        {"stage_id": stage_id, "stage_state": states[stage_id]}
        for stage_id in _CANONICAL_STAGE_IDS
    ]


def _expected_emitted_artifact_refs(
    *,
    analysis_request_ref: str,
    settlement_frame_ref: str,
    observation_frame_ref: str,
    semantic_ir_ref: str | None,
    alignment_report_ref: str | None,
) -> list[str]:
    refs = [analysis_request_ref, settlement_frame_ref, observation_frame_ref]
    if semantic_ir_ref is not None:
        refs.append(semantic_ir_ref)
    if alignment_report_ref is not None:
        refs.append(alignment_report_ref)
    return refs


def _default_output_root_ref(run_id: str) -> str:
    return f"artifacts/practical_analysis/v41f/runs/{run_id}/outputs"


def _default_runtime_evidence_root_ref(run_id: str) -> str:
    return f"artifacts/practical_analysis/v41f/runs/{run_id}/runtime"


def _request_source_set_present(payload: dict[str, Any]) -> bool:
    return "source_set" in payload and "source_set_hash" in payload


def _settlement_request_carry_present(payload: dict[str, Any]) -> bool:
    required = (
        "analysis_request_id",
        "analysis_request_ref",
        "source_set_hash",
        "authority_boundary_policy",
    )
    return all(field in payload for field in required)


class ArchitectureAnalysisRunner(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    name: Literal[_RUNNER_NAME] = _RUNNER_NAME
    version: str = "1"
    mode: Literal[_RUNNER_MODE] = _RUNNER_MODE
    contract_source: str = V41F_V88_CONTRACT_SOURCE

    @model_validator(mode="after")
    def _validate_runner(self) -> "ArchitectureAnalysisRunner":
        object.__setattr__(
            self,
            "version",
            _assert_non_empty_text(self.version, field_name="runner.version"),
        )
        object.__setattr__(
            self,
            "contract_source",
            _assert_non_empty_text(
                self.contract_source,
                field_name="runner.contract_source",
            ),
        )
        return self


class ArchitectureAnalysisRunStageStatus(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    stage_id: AnalysisRunStageId
    stage_state: AnalysisRunStageState


class AdeuArchitectureAnalysisRunManifest(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_ANALYSIS_RUN_MANIFEST_SCHEMA] = (
        ADEU_ARCHITECTURE_ANALYSIS_RUN_MANIFEST_SCHEMA
    )
    run_id: str
    runner: ArchitectureAnalysisRunner
    repo_root_ref: str
    output_root_ref: str
    runtime_evidence_root_ref: str
    analysis_request_id: str
    analysis_request_ref: str
    settlement_frame_id: str
    settlement_frame_ref: str
    observation_frame_id: str
    observation_frame_ref: str
    semantic_ir_id: str | None = None
    semantic_ir_ref: str | None = None
    alignment_report_id: str | None = None
    alignment_report_ref: str | None = None
    architecture_id: str | None = None
    semantic_hash: str | None = None
    source_set_hash: str
    authority_boundary_policy: AuthorityBoundaryPolicyPin
    run_outcome: AnalysisRunOutcome
    stop_reason_kind: AnalysisRunStopReasonKind
    terminal_alignment_posture: AnalysisRunTerminalAlignmentPosture
    stage_statuses: list[ArchitectureAnalysisRunStageStatus] = Field(default_factory=list)
    emitted_artifact_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_manifest(self, info: ValidationInfo) -> "AdeuArchitectureAnalysisRunManifest":
        object.__setattr__(self, "run_id", _assert_non_empty_text(self.run_id, field_name="run_id"))
        if self.repo_root_ref != ".":
            raise ValueError("repo_root_ref must be '.' in this first V41-F baseline")
        object.__setattr__(
            self,
            "output_root_ref",
            _normalize_output_root(self.output_root_ref, field_name="output_root_ref"),
        )
        object.__setattr__(
            self,
            "runtime_evidence_root_ref",
            _normalize_output_root(
                self.runtime_evidence_root_ref,
                field_name="runtime_evidence_root_ref",
            ),
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
            "source_set_hash",
            _assert_non_empty_text(self.source_set_hash, field_name="source_set_hash"),
        )
        if self.semantic_ir_id is None:
            if self.semantic_ir_ref is not None:
                raise ValueError("semantic_ir_ref requires semantic_ir_id")
            if self.architecture_id is not None:
                raise ValueError("architecture_id requires semantic_ir_id")
            if self.semantic_hash is not None:
                raise ValueError("semantic_hash requires semantic_ir_id")
        else:
            object.__setattr__(
                self,
                "semantic_ir_id",
                _assert_non_empty_text(self.semantic_ir_id, field_name="semantic_ir_id"),
            )
            if self.semantic_ir_ref is None:
                raise ValueError("semantic_ir_id requires semantic_ir_ref")
            object.__setattr__(
                self,
                "semantic_ir_ref",
                _normalize_artifact_ref(self.semantic_ir_ref, field_name="semantic_ir_ref"),
            )
            architecture_id = _assert_non_empty_text(
                self.architecture_id or "",
                field_name="architecture_id",
            )
            if architecture_id != self.semantic_ir_id:
                raise ValueError("architecture_id must match semantic_ir_id in this first baseline")
            object.__setattr__(self, "architecture_id", architecture_id)
            object.__setattr__(
                self,
                "semantic_hash",
                _assert_non_empty_text(self.semantic_hash or "", field_name="semantic_hash"),
            )
        if self.alignment_report_id is None:
            if self.alignment_report_ref is not None:
                raise ValueError("alignment_report_ref requires alignment_report_id")
        else:
            object.__setattr__(
                self,
                "alignment_report_id",
                _assert_non_empty_text(
                    self.alignment_report_id,
                    field_name="alignment_report_id",
                ),
            )
            if self.alignment_report_ref is None:
                raise ValueError("alignment_report_id requires alignment_report_ref")
            object.__setattr__(
                self,
                "alignment_report_ref",
                _normalize_artifact_ref(
                    self.alignment_report_ref,
                    field_name="alignment_report_ref",
                ),
            )

        stage_ids = [entry.stage_id for entry in self.stage_statuses]
        if stage_ids != list(_CANONICAL_STAGE_IDS):
            raise ValueError("stage_statuses must appear in canonical stage order")
        expected_stage_statuses = _expected_stage_statuses(self.run_outcome)
        stage_status_payloads = [
            entry.model_dump(mode="json") for entry in self.stage_statuses
        ]
        if stage_status_payloads != expected_stage_statuses:
            raise ValueError(
                "stage_statuses must match the canonical ledger for the runner outcome"
            )

        object.__setattr__(
            self,
            "emitted_artifact_refs",
            [
                _normalize_artifact_ref(ref, field_name="emitted_artifact_refs")
                for ref in self.emitted_artifact_refs
            ],
        )
        expected_emitted = _expected_emitted_artifact_refs(
            analysis_request_ref=self.analysis_request_ref,
            settlement_frame_ref=self.settlement_frame_ref,
            observation_frame_ref=self.observation_frame_ref,
            semantic_ir_ref=self.semantic_ir_ref,
            alignment_report_ref=self.alignment_report_ref,
        )
        if self.emitted_artifact_refs != expected_emitted:
            raise ValueError(
                "emitted_artifact_refs must match the canonically ordered emitted artifact set"
            )

        expected_run_id = _expected_run_id(
            analysis_request_id=self.analysis_request_id,
            settlement_frame_id=self.settlement_frame_id,
            observation_frame_id=self.observation_frame_id,
            semantic_ir_id=self.semantic_ir_id,
            alignment_report_id=self.alignment_report_id,
            runner=self.runner,
        )
        if self.run_id != expected_run_id:
            raise ValueError("run_id must match the canonical runner input hash")

        if self.run_outcome == "blocked":
            if self.stop_reason_kind != "settlement_blocked":
                raise ValueError("blocked runs require stop_reason_kind=settlement_blocked")
            if self.terminal_alignment_posture != "none":
                raise ValueError("blocked runs require terminal_alignment_posture=none")
            if self.semantic_ir_id is not None or self.alignment_report_id is not None:
                raise ValueError(
                    "blocked runs may not emit intended semantic IR or alignment report refs"
                )
        else:
            if self.stop_reason_kind != "none":
                raise ValueError("completed runs require stop_reason_kind=none")
            if self.semantic_ir_id is None or self.alignment_report_id is None:
                raise ValueError(
                    "completed runs require emitted semantic_ir and alignment_report refs"
                )
            if self.terminal_alignment_posture == "none":
                raise ValueError(
                    "completed runs must carry the consumed terminal alignment posture"
                )

        if info.context:
            request = info.context.get("analysis_request")
            settlement = info.context.get("analysis_settlement")
            observation = info.context.get("observation_frame")
            semantic_ir = info.context.get("semantic_ir")
            alignment_report = info.context.get("alignment_report")
            if request is not None:
                if self.analysis_request_id != request.analysis_request_id:
                    raise ValueError(
                        "analysis_request_id must match the consumed analysis request"
                    )
                if self.source_set_hash != request.source_set_hash:
                    raise ValueError(
                        "source_set_hash must match the consumed analysis request"
                    )
                expected_policy = request.authority_boundary_policy.model_dump(
                    mode="json",
                    exclude_none=False,
                )
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
                        "analysis_request_ref must match the consumed settlement lineage"
                    )
                settlement_blocked = (
                    settlement.compile_entitlement == "blocked" or bool(settlement.blocking_lineage)
                )
                if self.run_outcome == "blocked" and not settlement_blocked:
                    raise ValueError(
                        "runner-level blocked is legal only over a settlement-blocked world"
                    )
                if self.run_outcome == "completed" and settlement_blocked:
                    raise ValueError(
                        "completed runs require compile_entitlement=entitled with no blockers"
                    )
            if observation is not None:
                if self.observation_frame_id != observation.observation_frame_id:
                    raise ValueError(
                        "observation_frame_id must match the consumed observation frame"
                    )
                if self.analysis_request_ref != observation.analysis_request_ref:
                    raise ValueError(
                        "analysis_request_ref must match the consumed observation lineage"
                    )
                if self.settlement_frame_ref != observation.settlement_frame_ref:
                    raise ValueError(
                        "settlement_frame_ref must match the consumed observation lineage"
                    )
                if self.run_outcome == "blocked":
                    if observation.upstream_compile_entitlement != "blocked":
                        raise ValueError(
                            "blocked runs require an observation frame carried through "
                            "a blocked settlement"
                        )
                else:
                    if observation.upstream_compile_entitlement != "entitled":
                        raise ValueError(
                            "completed runs require an observation frame carried "
                            "through an entitled settlement"
                        )
            if semantic_ir is not None:
                if self.semantic_ir_id != semantic_ir.architecture_id:
                    raise ValueError("semantic_ir_id must match the consumed semantic root")
                if self.architecture_id != semantic_ir.architecture_id:
                    raise ValueError("architecture_id must match the consumed semantic root")
                if self.semantic_hash != semantic_ir.semantic_hash:
                    raise ValueError("semantic_hash must match the consumed semantic root")
            if alignment_report is not None:
                if self.alignment_report_id != alignment_report.alignment_report_id:
                    raise ValueError(
                        "alignment_report_id must match the consumed alignment report"
                    )
                if self.terminal_alignment_posture != alignment_report.alignment_posture:
                    raise ValueError(
                        "terminal_alignment_posture must match the consumed alignment report"
                    )

        return self


@dataclass(frozen=True)
class V41FPracticalAnalysisRunBundle:
    analysis_request_payload: dict[str, Any]
    analysis_request_ref: str
    settlement_frame_payload: dict[str, Any]
    settlement_frame_ref: str
    observation_frame_payload: dict[str, Any]
    observation_frame_ref: str
    semantic_ir_payload: dict[str, Any] | None
    semantic_ir_ref: str | None
    alignment_report_payload: dict[str, Any] | None
    alignment_report_ref: str | None
    run_manifest_payload: dict[str, Any]


def canonicalize_adeu_architecture_analysis_run_manifest_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest | None = None,
    analysis_settlement_payload: (
        dict[str, Any] | AdeuArchitectureAnalysisSettlementFrame | None
    ) = None,
    observation_frame_payload: dict[str, Any] | AdeuArchitectureObservationFrame | None = None,
    semantic_ir_payload: dict[str, Any] | AdeuArchitectureSemanticIR | None = None,
    alignment_report_payload: dict[str, Any] | AdeuArchitectureAlignmentReport | None = None,
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
    alignment_report = alignment_report_payload
    if alignment_report is not None and not isinstance(
        alignment_report,
        AdeuArchitectureAlignmentReport,
    ):
        alignment_report = AdeuArchitectureAlignmentReport.model_validate(alignment_report)
    return AdeuArchitectureAnalysisRunManifest.model_validate(
        payload,
        context=_validation_context(
            root,
            analysis_request=request,
            analysis_settlement=settlement,
            observation_frame=observation,
            semantic_ir=semantic_ir,
            alignment_report=alignment_report,
        ),
    ).model_dump(mode="json", exclude_none=True)


def _materialize_or_validate_request(
    *,
    payload: dict[str, Any] | AdeuArchitectureAnalysisRequest,
    analysis_request_ref: str,
    settlement_frame_ref: str,
    repository_root: Path,
) -> dict[str, Any]:
    normalized_settlement_ref = _normalize_artifact_ref(
        settlement_frame_ref,
        field_name="settlement_frame_ref",
    )
    if isinstance(payload, AdeuArchitectureAnalysisRequest):
        request_payload = payload.model_dump(mode="json", exclude_none=False)
    else:
        request_payload = dict(payload)
    if _request_source_set_present(request_payload):
        existing = request_payload.get("settlement_frame_ref")
        if existing != normalized_settlement_ref:
            raise ValueError(
                "analysis_request.settlement_frame_ref must match the runner settlement_frame_ref"
            )
        return canonicalize_adeu_architecture_analysis_request_payload(
            request_payload,
            repository_root=repository_root,
        )
    request_payload["settlement_frame_ref"] = normalized_settlement_ref
    return materialize_adeu_architecture_analysis_request_payload(
        request_payload,
        repository_root=repository_root,
    )


def _materialize_or_validate_settlement(
    *,
    payload: dict[str, Any] | AdeuArchitectureAnalysisSettlementFrame,
    analysis_request_payload: dict[str, Any],
    analysis_request_ref: str,
    settlement_frame_ref: str,
    repository_root: Path,
) -> dict[str, Any]:
    normalized_request_ref = _normalize_artifact_ref(
        analysis_request_ref,
        field_name="analysis_request_ref",
    )
    normalized_settlement_ref = _normalize_artifact_ref(
        settlement_frame_ref,
        field_name="settlement_frame_ref",
    )
    if isinstance(payload, AdeuArchitectureAnalysisSettlementFrame):
        settlement_payload = payload.model_dump(mode="json", exclude_none=False)
    else:
        settlement_payload = dict(payload)
    if _settlement_request_carry_present(settlement_payload):
        if settlement_payload.get("analysis_request_ref") != normalized_request_ref:
            raise ValueError(
                "settlement_frame.analysis_request_ref must match analysis_request_ref"
            )
        canonical = canonicalize_adeu_architecture_analysis_settlement_frame_payload(
            settlement_payload,
            repository_root=repository_root,
            analysis_request_payload=analysis_request_payload,
        )
    else:
        canonical = materialize_adeu_architecture_analysis_settlement_frame_payload(
            settlement_payload,
            analysis_request_payload=analysis_request_payload,
            analysis_request_ref=normalized_request_ref,
            repository_root=repository_root,
        )
    if canonical["analysis_request_ref"] != normalized_request_ref:
        raise ValueError("settlement_frame.analysis_request_ref must match analysis_request_ref")
    if analysis_request_payload["settlement_frame_ref"] != normalized_settlement_ref:
        raise ValueError(
            "analysis_request.settlement_frame_ref must match settlement_frame_ref"
        )
    return canonical


def derive_v41f_analysis_run_manifest(
    *,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest,
    analysis_request_ref: str,
    settlement_frame_payload: dict[str, Any] | AdeuArchitectureAnalysisSettlementFrame,
    settlement_frame_ref: str,
    observation_frame_payload: dict[str, Any] | AdeuArchitectureObservationFrame,
    observation_frame_ref: str,
    semantic_ir_payload: dict[str, Any] | AdeuArchitectureSemanticIR | None = None,
    semantic_ir_ref: str | None = None,
    alignment_report_payload: dict[str, Any] | AdeuArchitectureAlignmentReport | None = None,
    alignment_report_ref: str | None = None,
    output_root_ref: str | None = None,
    runtime_evidence_root_ref: str | None = None,
    runner: dict[str, Any] | ArchitectureAnalysisRunner | None = None,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    request = analysis_request_payload
    if not isinstance(request, AdeuArchitectureAnalysisRequest):
        request = AdeuArchitectureAnalysisRequest.model_validate(
            analysis_request_payload,
            context={"repository_root": root},
        )
    settlement = settlement_frame_payload
    if not isinstance(settlement, AdeuArchitectureAnalysisSettlementFrame):
        settlement = AdeuArchitectureAnalysisSettlementFrame.model_validate(
            settlement_frame_payload,
            context=_validation_context(root, analysis_request=request),
        )
    observation = observation_frame_payload
    if not isinstance(observation, AdeuArchitectureObservationFrame):
        observation = AdeuArchitectureObservationFrame.model_validate(
            observation_frame_payload,
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
    alignment_report = alignment_report_payload
    if alignment_report is not None and not isinstance(
        alignment_report,
        AdeuArchitectureAlignmentReport,
    ):
        alignment_report = AdeuArchitectureAlignmentReport.model_validate(alignment_report)

    runner_model = (
        runner
        if isinstance(runner, ArchitectureAnalysisRunner)
        else ArchitectureAnalysisRunner.model_validate(runner or {})
    )
    run_outcome: AnalysisRunOutcome
    stop_reason_kind: AnalysisRunStopReasonKind
    terminal_alignment_posture: AnalysisRunTerminalAlignmentPosture
    semantic_ir_id: str | None
    architecture_id: str | None
    semantic_hash: str | None
    alignment_report_id: str | None
    normalized_semantic_ref = _normalize_optional_artifact_ref(
        semantic_ir_ref,
        field_name="semantic_ir_ref",
    )
    normalized_alignment_ref = _normalize_optional_artifact_ref(
        alignment_report_ref,
        field_name="alignment_report_ref",
    )
    settlement_blocked = (
        settlement.compile_entitlement == "blocked" or bool(settlement.blocking_lineage)
    )
    if settlement_blocked:
        if semantic_ir is not None or alignment_report is not None:
            raise ValueError(
                "settlement-blocked runs may not consume emitted semantic_ir or alignment_report"
            )
        if normalized_semantic_ref is not None or normalized_alignment_ref is not None:
            raise ValueError(
                "settlement-blocked runs may not supply semantic_ir_ref or alignment_report_ref"
            )
        run_outcome = "blocked"
        stop_reason_kind = "settlement_blocked"
        terminal_alignment_posture = "none"
        semantic_ir_id = None
        architecture_id = None
        semantic_hash = None
        alignment_report_id = None
    else:
        if semantic_ir is None or alignment_report is None:
            raise ValueError(
                "completed runs require consumed semantic_ir_payload and alignment_report_payload"
            )
        if normalized_semantic_ref is None or normalized_alignment_ref is None:
            raise ValueError(
                "completed runs require semantic_ir_ref and alignment_report_ref"
            )
        run_outcome = "completed"
        stop_reason_kind = "none"
        terminal_alignment_posture = alignment_report.alignment_posture
        semantic_ir_id = semantic_ir.architecture_id
        architecture_id = semantic_ir.architecture_id
        semantic_hash = semantic_ir.semantic_hash
        alignment_report_id = alignment_report.alignment_report_id

    run_id = _expected_run_id(
        analysis_request_id=request.analysis_request_id,
        settlement_frame_id=settlement.settlement_frame_id,
        observation_frame_id=observation.observation_frame_id,
        semantic_ir_id=semantic_ir_id,
        alignment_report_id=alignment_report_id,
        runner=runner_model,
    )
    normalized_output_root = _normalize_output_root(
        output_root_ref or _default_output_root_ref(run_id),
        field_name="output_root_ref",
    )
    normalized_runtime_root = _normalize_output_root(
        runtime_evidence_root_ref or _default_runtime_evidence_root_ref(run_id),
        field_name="runtime_evidence_root_ref",
    )

    payload = {
        "schema": ADEU_ARCHITECTURE_ANALYSIS_RUN_MANIFEST_SCHEMA,
        "run_id": run_id,
        "runner": runner_model.model_dump(mode="json"),
        "repo_root_ref": ".",
        "output_root_ref": normalized_output_root,
        "runtime_evidence_root_ref": normalized_runtime_root,
        "analysis_request_id": request.analysis_request_id,
        "analysis_request_ref": _normalize_artifact_ref(
            analysis_request_ref,
            field_name="analysis_request_ref",
        ),
        "settlement_frame_id": settlement.settlement_frame_id,
        "settlement_frame_ref": _normalize_artifact_ref(
            settlement_frame_ref,
            field_name="settlement_frame_ref",
        ),
        "observation_frame_id": observation.observation_frame_id,
        "observation_frame_ref": _normalize_artifact_ref(
            observation_frame_ref,
            field_name="observation_frame_ref",
        ),
        "semantic_ir_id": semantic_ir_id,
        "semantic_ir_ref": normalized_semantic_ref,
        "alignment_report_id": alignment_report_id,
        "alignment_report_ref": normalized_alignment_ref,
        "architecture_id": architecture_id,
        "semantic_hash": semantic_hash,
        "source_set_hash": request.source_set_hash,
        "authority_boundary_policy": request.authority_boundary_policy.model_dump(
            mode="json",
            exclude_none=False,
        ),
        "run_outcome": run_outcome,
        "stop_reason_kind": stop_reason_kind,
        "terminal_alignment_posture": terminal_alignment_posture,
        "stage_statuses": _expected_stage_statuses(run_outcome),
        "emitted_artifact_refs": _expected_emitted_artifact_refs(
            analysis_request_ref=_normalize_artifact_ref(
                analysis_request_ref,
                field_name="analysis_request_ref",
            ),
            settlement_frame_ref=_normalize_artifact_ref(
                settlement_frame_ref,
                field_name="settlement_frame_ref",
            ),
            observation_frame_ref=_normalize_artifact_ref(
                observation_frame_ref,
                field_name="observation_frame_ref",
            ),
            semantic_ir_ref=normalized_semantic_ref,
            alignment_report_ref=normalized_alignment_ref,
        ),
    }
    return canonicalize_adeu_architecture_analysis_run_manifest_payload(
        payload,
        repository_root=root,
        analysis_request_payload=request,
        analysis_settlement_payload=settlement,
        observation_frame_payload=observation,
        semantic_ir_payload=semantic_ir,
        alignment_report_payload=alignment_report,
    )


def derive_v41f_practical_analysis_run_bundle(
    *,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest,
    analysis_request_ref: str,
    settlement_frame_payload: dict[str, Any] | AdeuArchitectureAnalysisSettlementFrame,
    settlement_frame_ref: str,
    observation_frame_ref: str,
    semantic_ir_ref: str | None = None,
    alignment_report_ref: str | None = None,
    output_root_ref: str | None = None,
    runtime_evidence_root_ref: str | None = None,
    runner: dict[str, Any] | ArchitectureAnalysisRunner | None = None,
    repository_root: Path | None = None,
) -> V41FPracticalAnalysisRunBundle:
    root = _resolve_repository_root(repository_root)
    normalized_request_ref = _normalize_artifact_ref(
        analysis_request_ref,
        field_name="analysis_request_ref",
    )
    normalized_settlement_ref = _normalize_artifact_ref(
        settlement_frame_ref,
        field_name="settlement_frame_ref",
    )
    normalized_observation_ref = _normalize_artifact_ref(
        observation_frame_ref,
        field_name="observation_frame_ref",
    )

    request_payload = _materialize_or_validate_request(
        payload=analysis_request_payload,
        analysis_request_ref=normalized_request_ref,
        settlement_frame_ref=normalized_settlement_ref,
        repository_root=root,
    )
    settlement_payload = _materialize_or_validate_settlement(
        payload=settlement_frame_payload,
        analysis_request_payload=request_payload,
        analysis_request_ref=normalized_request_ref,
        settlement_frame_ref=normalized_settlement_ref,
        repository_root=root,
    )
    observation_payload = derive_v41c_observation_frame(
        analysis_request_payload=request_payload,
        analysis_request_path=normalized_request_ref,
        settlement_frame_payload=settlement_payload,
        settlement_frame_path=normalized_settlement_ref,
        repository_root=root,
    )
    settlement = AdeuArchitectureAnalysisSettlementFrame.model_validate(
        settlement_payload,
        context=_validation_context(
            root,
            analysis_request=AdeuArchitectureAnalysisRequest.model_validate(
                request_payload,
                context={"repository_root": root},
            ),
        ),
    )

    semantic_ir_payload_out: dict[str, Any] | None = None
    alignment_report_payload_out: dict[str, Any] | None = None
    normalized_semantic_ref = _normalize_optional_artifact_ref(
        semantic_ir_ref,
        field_name="semantic_ir_ref",
    )
    normalized_alignment_ref = _normalize_optional_artifact_ref(
        alignment_report_ref,
        field_name="alignment_report_ref",
    )
    if settlement.compile_entitlement == "entitled" and not settlement.blocking_lineage:
        if normalized_semantic_ref is None or normalized_alignment_ref is None:
            raise ValueError(
                "completed runs require semantic_ir_ref and alignment_report_ref"
            )
        semantic_ir_payload_out = derive_v41d_semantic_ir(
            analysis_request_payload=request_payload,
            analysis_request_path=normalized_request_ref,
            settlement_frame_payload=settlement_payload,
            settlement_frame_path=normalized_settlement_ref,
            observation_frame_payload=observation_payload,
            observation_frame_path=normalized_observation_ref,
            repository_root=root,
        )
        alignment_report_payload_out = derive_v41e_alignment_report(
            analysis_request_payload=request_payload,
            analysis_request_path=normalized_request_ref,
            settlement_frame_payload=settlement_payload,
            settlement_frame_path=normalized_settlement_ref,
            observation_frame_payload=observation_payload,
            observation_frame_path=normalized_observation_ref,
            semantic_ir_payload=semantic_ir_payload_out,
            repository_root=root,
        )
    else:
        if normalized_semantic_ref is not None or normalized_alignment_ref is not None:
            raise ValueError(
                "settlement-blocked runs may not supply semantic_ir_ref or alignment_report_ref"
            )

    run_manifest_payload = derive_v41f_analysis_run_manifest(
        analysis_request_payload=request_payload,
        analysis_request_ref=normalized_request_ref,
        settlement_frame_payload=settlement_payload,
        settlement_frame_ref=normalized_settlement_ref,
        observation_frame_payload=observation_payload,
        observation_frame_ref=normalized_observation_ref,
        semantic_ir_payload=semantic_ir_payload_out,
        semantic_ir_ref=normalized_semantic_ref,
        alignment_report_payload=alignment_report_payload_out,
        alignment_report_ref=normalized_alignment_ref,
        output_root_ref=output_root_ref,
        runtime_evidence_root_ref=runtime_evidence_root_ref,
        runner=runner,
        repository_root=root,
    )
    return V41FPracticalAnalysisRunBundle(
        analysis_request_payload=request_payload,
        analysis_request_ref=normalized_request_ref,
        settlement_frame_payload=settlement_payload,
        settlement_frame_ref=normalized_settlement_ref,
        observation_frame_payload=observation_payload,
        observation_frame_ref=normalized_observation_ref,
        semantic_ir_payload=semantic_ir_payload_out,
        semantic_ir_ref=normalized_semantic_ref,
        alignment_report_payload=alignment_report_payload_out,
        alignment_report_ref=normalized_alignment_ref,
        run_manifest_payload=run_manifest_payload,
    )


__all__ = [
    "ADEU_ARCHITECTURE_ANALYSIS_RUN_MANIFEST_SCHEMA",
    "V41F_V88_CONTRACT_SOURCE",
    "AdeuArchitectureAnalysisRunManifest",
    "ArchitectureAnalysisRunner",
    "ArchitectureAnalysisRunStageStatus",
    "V41FPracticalAnalysisRunBundle",
    "canonicalize_adeu_architecture_analysis_run_manifest_payload",
    "derive_v41f_analysis_run_manifest",
    "derive_v41f_practical_analysis_run_bundle",
]
