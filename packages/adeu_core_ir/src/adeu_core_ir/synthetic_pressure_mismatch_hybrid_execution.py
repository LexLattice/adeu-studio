from __future__ import annotations

from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator

from .synthetic_pressure_mismatch import (
    SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA,
    SyntheticPressureMismatchAllowedAction,
    SyntheticPressureMismatchEvidenceRegime,
    SyntheticPressureMismatchHarmKind,
    SyntheticPressureMismatchResolutionRoute,
    SyntheticPressureMismatchRule,
    SyntheticPressureMismatchRuleRegistry,
    SyntheticPressureMismatchSignalKind,
    SyntheticPressureMismatchSubjectKind,
    canonicalize_synthetic_pressure_mismatch_rule_registry_payload,
)
from .synthetic_pressure_mismatch_fix_plan import (
    SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_SCHEMA,
    SyntheticPressureMismatchFixPlan,
    SyntheticPressureMismatchProjectedPlanItem,
    _source_finding_id_from_parts,
    canonicalize_synthetic_pressure_mismatch_fix_plan_payload,
)
from .synthetic_pressure_mismatch_observation import (
    SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA,
    SyntheticPressureMismatchConformanceReport,
    SyntheticPressureMismatchObservationPacket,
    _assert_non_empty_text,
    _assert_sorted_unique,
    _canonical_json_hash,
    _load_repo_json_object,
    _normalize_repo_relative_path,
    _resolve_repository_root,
    _sha256_repo_file,
    _sha256_text,
    _validation_context,
    canonicalize_synthetic_pressure_mismatch_conformance_report_payload,
    canonicalize_synthetic_pressure_mismatch_observation_packet_payload,
)

SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_SCHEMA = (
    "synthetic_pressure_mismatch_oracle_request@1"
)
SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_SCHEMA = (
    "synthetic_pressure_mismatch_oracle_resolution@1"
)
SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_SCHEMA = (
    "synthetic_pressure_mismatch_checkpoint_trace@1"
)
V39E_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md"
    "#v39e_synthetic_pressure_mismatch_hybrid_execution_contract@1"
)
V39E_SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_EVALUATOR_ID = (
    "adeu_core_ir.synthetic_pressure_mismatch_hybrid_execution"
    ".derive_v39e_oracle_request@1"
)
V39E_SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_EVALUATOR_ID = (
    "adeu_core_ir.synthetic_pressure_mismatch_hybrid_execution"
    ".derive_v39e_oracle_resolution@1"
)
V39E_SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_EVALUATOR_ID = (
    "adeu_core_ir.synthetic_pressure_mismatch_hybrid_execution"
    ".derive_v39e_checkpoint_trace@1"
)
DEFAULT_V39E_FIX_PLAN_REFERENCE_FIXTURE_PATH = (
    "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus75/"
    "synthetic_pressure_mismatch_fix_plan_v75_reference.json"
)
DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH = (
    "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
    "local_hybrid_fixture_v76_narrative_comment.json"
)
DEFAULT_V39E_LOCAL_HYBRID_HUMAN_FIXTURE_PATH = (
    "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
    "local_hybrid_fixture_v76_mirrored_branch.json"
)
_DEFAULT_V39E_POLICY_SOURCE_PATHS = (
    "AGENTS.md",
    "docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md",
)
_LOCAL_HYBRID_FIXTURE_GLOB = "local_hybrid_fixture_v76_*.json"

SyntheticPressureMismatchOracleRequestSchemaVersion = Literal[
    "synthetic_pressure_mismatch_oracle_request@1"
]
SyntheticPressureMismatchOracleResolutionSchemaVersion = Literal[
    "synthetic_pressure_mismatch_oracle_resolution@1"
]
SyntheticPressureMismatchCheckpointTraceSchemaVersion = Literal[
    "synthetic_pressure_mismatch_checkpoint_trace@1"
]
SyntheticPressureMismatchHybridSourceKind = Literal[
    "released_conformance_finding",
    "released_fix_plan_projection",
    "local_hybrid_fixture",
]
SyntheticPressureMismatchCheckpointClass = Literal[
    "deterministic_pass",
    "deterministic_fail",
    "oracle_needed",
    "human_needed",
]
SyntheticPressureMismatchFinalAdjudication = Literal[
    "resolved_pass",
    "resolved_fail",
    "escalated_human",
]
SyntheticPressureMismatchOracleDisposition = Literal[
    "advisory_support",
    "advisory_reject",
    "inconclusive",
    "contradictory",
]
SyntheticPressureMismatchOracleResolutionOrigin = Literal[
    "fresh_model_output",
    "cache_replay",
]
SyntheticPressureMismatchReasoningEffort = Literal["low", "medium", "high", "xhigh"]
SyntheticPressureMismatchHybridFixtureLanguage = Literal["python", "text"]


def _checkpoint_id(
    *,
    source_kind: SyntheticPressureMismatchHybridSourceKind,
    source_binding_id: str,
    rule_id: str,
    subject_ref: str,
    local_subject_anchor: str,
) -> str:
    digest = _canonical_json_hash(
        {
            "local_subject_anchor": local_subject_anchor,
            "rule_id": rule_id,
            "source_binding_id": source_binding_id,
            "source_kind": source_kind,
            "subject_ref": subject_ref,
        }
    )[:16]
    return f"v39e_v76_checkpoint_{digest}"


def _trace_id(
    *,
    source_kind: SyntheticPressureMismatchHybridSourceKind,
    source_reference_fixture: str,
    checkpoint_ids: list[str],
    oracle_request_id: str | None,
    oracle_resolution_id: str | None,
) -> str:
    digest = _canonical_json_hash(
        {
            "checkpoint_ids": checkpoint_ids,
            "oracle_request_id": oracle_request_id,
            "oracle_resolution_id": oracle_resolution_id,
            "source_kind": source_kind,
            "source_reference_fixture": source_reference_fixture,
        }
    )[:16]
    return f"v39e_v76_trace_{digest}"


def _oracle_request_id(
    *,
    checkpoint_id: str,
    replay_identity: dict[str, Any],
    interpretation_prompt: str,
    bounded_context: str,
) -> str:
    digest = _canonical_json_hash(
        {
            "bounded_context": bounded_context,
            "checkpoint_id": checkpoint_id,
            "interpretation_prompt": interpretation_prompt,
            "replay_identity": replay_identity,
        }
    )[:16]
    return f"v39e_v76_oracle_request_{digest}"


def _oracle_resolution_id(
    *,
    oracle_request_id: str,
    resolution_disposition: SyntheticPressureMismatchOracleDisposition,
    resolution_origin: SyntheticPressureMismatchOracleResolutionOrigin,
    raw_output_sha256: str,
    model_id: str,
    model_version: str,
    reasoning_effort: SyntheticPressureMismatchReasoningEffort,
) -> str:
    digest = _canonical_json_hash(
        {
            "model_id": model_id,
            "model_version": model_version,
            "oracle_request_id": oracle_request_id,
            "raw_output_sha256": raw_output_sha256,
            "reasoning_effort": reasoning_effort,
            "resolution_disposition": resolution_disposition,
            "resolution_origin": resolution_origin,
        }
    )[:16]
    return f"v39e_v76_oracle_resolution_{digest}"


def _parse_source_finding_id(source_finding_id: str) -> tuple[str, str, str]:
    parts = source_finding_id.split("::")
    if len(parts) != 3 or any(not part for part in parts):
        raise ValueError(
            "source_finding_id must use observation_packet_id::rule_id::local_observation_locator"
        )
    observation_packet_id, rule_id, local_observation_locator = parts
    return observation_packet_id, rule_id, local_observation_locator


def _policy_source_paths() -> tuple[str, ...]:
    return _DEFAULT_V39E_POLICY_SOURCE_PATHS


def _expected_policy_source_paths() -> list[str]:
    return sorted(_policy_source_paths())


def _replay_identity_sha256(payload: dict[str, Any]) -> str:
    return _canonical_json_hash(payload)


def _load_validated_registry(
    registry_reference_fixture_path: str,
    *,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchRuleRegistry:
    payload = _load_repo_json_object(
        registry_reference_fixture_path,
        field_name="registry_reference_fixture",
        repository_root=repository_root,
    )
    canonical_payload = canonicalize_synthetic_pressure_mismatch_rule_registry_payload(payload)
    return SyntheticPressureMismatchRuleRegistry.model_validate(
        canonical_payload,
        context=_validation_context(repository_root),
    )


def _load_validated_conformance_report(
    conformance_report_reference_fixture_path: str,
    *,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchConformanceReport:
    payload = _load_repo_json_object(
        conformance_report_reference_fixture_path,
        field_name="conformance_report_reference_fixture",
        repository_root=repository_root,
    )
    canonical_payload = canonicalize_synthetic_pressure_mismatch_conformance_report_payload(
        payload,
        repository_root=repository_root,
    )
    return SyntheticPressureMismatchConformanceReport.model_validate(
        canonical_payload,
        context=_validation_context(repository_root),
    )


def _load_validated_fix_plan(
    fix_plan_reference_fixture_path: str,
    *,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchFixPlan:
    payload = _load_repo_json_object(
        fix_plan_reference_fixture_path,
        field_name="fix_plan_reference_fixture",
        repository_root=repository_root,
    )
    canonical_payload = canonicalize_synthetic_pressure_mismatch_fix_plan_payload(
        payload,
        repository_root=repository_root,
    )
    return SyntheticPressureMismatchFixPlan.model_validate(
        canonical_payload,
        context=_validation_context(repository_root),
    )


class SyntheticPressureMismatchLocalHybridFixture(BaseModel):
    model_config = ConfigDict(extra="forbid")

    fixture_id: str = Field(min_length=1)
    rule_id: str = Field(min_length=1)
    subject_kind: SyntheticPressureMismatchSubjectKind
    subject_ref: str = Field(min_length=1)
    local_subject_anchor: str = Field(min_length=1)
    language: SyntheticPressureMismatchHybridFixtureLanguage = "text"
    content: str = Field(min_length=1)
    content_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchLocalHybridFixture":
        _assert_non_empty_text(self.fixture_id, field_name="fixture_id")
        _assert_non_empty_text(self.rule_id, field_name="rule_id")
        _assert_non_empty_text(self.subject_ref, field_name="subject_ref")
        _assert_non_empty_text(
            self.local_subject_anchor,
            field_name="local_subject_anchor",
        )
        _assert_non_empty_text(self.content, field_name="content")
        if self.content_sha256 != _sha256_text(self.content):
            raise ValueError("content_sha256 must match content bytes")
        return self


def _load_local_hybrid_fixture(
    local_hybrid_fixture_reference: str,
    *,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchLocalHybridFixture:
    payload = _load_repo_json_object(
        local_hybrid_fixture_reference,
        field_name="local_hybrid_fixture_reference",
        repository_root=repository_root,
    )
    return SyntheticPressureMismatchLocalHybridFixture.model_validate(payload)


def _find_observation_packet_fixture_by_id(
    observation_packet_id: str,
    *,
    repository_root: Path | None = None,
) -> tuple[str, SyntheticPressureMismatchObservationPacket]:
    root = repository_root or _resolve_repository_root()
    fixtures_root = root / "apps" / "api" / "fixtures" / "synthetic_pressure_mismatch"
    matches: list[tuple[str, SyntheticPressureMismatchObservationPacket]] = []
    for path in fixtures_root.rglob("synthetic_pressure_mismatch_observation_packet*.json"):
        relative_path = path.relative_to(root).as_posix()
        payload = _load_repo_json_object(
            relative_path,
            field_name="observation_packet_reference_fixture",
            repository_root=root,
        )
        if payload.get("observation_packet_id") != observation_packet_id:
            continue
        canonical_payload = canonicalize_synthetic_pressure_mismatch_observation_packet_payload(
            payload,
            repository_root=root,
        )
        packet = SyntheticPressureMismatchObservationPacket.model_validate(
            canonical_payload,
            context=_validation_context(root),
        )
        matches.append((relative_path, packet))
    if not matches:
        raise ValueError(
            f"unable to resolve released observation packet fixture for "
            f"observation_packet_id {observation_packet_id}"
        )
    if len(matches) > 1:
        raise ValueError(
            f"observation_packet_id {observation_packet_id} resolved to multiple fixtures"
        )
    return matches[0]


def _rule_index(
    registry: SyntheticPressureMismatchRuleRegistry,
) -> dict[str, SyntheticPressureMismatchRule]:
    return {rule.rule_id: rule for rule in registry.rules}


def _find_projection_by_id(
    plan: SyntheticPressureMismatchFixPlan,
    projected_item_id: str,
) -> SyntheticPressureMismatchProjectedPlanItem:
    matches = [
        item
        for item in (plan.forward_agent_projections + plan.post_optimizer_projections)
        if item.projected_item_id == projected_item_id
    ]
    if not matches:
        raise ValueError(
            "source_projected_item_id must match a released V39-D projection"
        )
    if len(matches) > 1:
        raise ValueError("source_projected_item_id must resolve to exactly one projection")
    return matches[0]


def _find_conformance_source_finding(
    report: SyntheticPressureMismatchConformanceReport,
    source_finding_id: str,
) -> str:
    category_map: dict[str, str] = {}
    for refs, category_name in (
        (report.safe_autofix_candidates, "safe_autofix_candidates"),
        (
            report.deterministic_high_severity_findings,
            "deterministic_high_severity_findings",
        ),
        (report.review_only_findings, "review_only_findings"),
        (report.meta_governance_findings, "meta_governance_findings"),
    ):
        for ref in refs:
            category_map[
                _source_finding_id_from_parts(
                    observation_packet_id=ref.observation_packet_id,
                    rule_id=ref.rule_id,
                    local_observation_locator=ref.local_observation_locator,
                )
            ] = category_name
    try:
        return category_map[source_finding_id]
    except KeyError as exc:
        raise ValueError(
            "source_finding_id must match a released V39-C conformance finding"
        ) from exc


def _expected_final_adjudication_for_checkpoint_class(
    checkpoint_class: SyntheticPressureMismatchCheckpointClass,
) -> SyntheticPressureMismatchFinalAdjudication | None:
    mapping: dict[
        SyntheticPressureMismatchCheckpointClass,
        SyntheticPressureMismatchFinalAdjudication | None,
    ] = {
        "deterministic_pass": "resolved_pass",
        "deterministic_fail": "resolved_fail",
        "oracle_needed": None,
        "human_needed": "escalated_human",
    }
    return mapping[checkpoint_class]


def _expected_final_adjudication_for_resolution(
    resolution_disposition: SyntheticPressureMismatchOracleDisposition,
) -> SyntheticPressureMismatchFinalAdjudication:
    mapping: dict[
        SyntheticPressureMismatchOracleDisposition,
        SyntheticPressureMismatchFinalAdjudication,
    ] = {
        "advisory_support": "resolved_fail",
        "advisory_reject": "resolved_pass",
        "inconclusive": "escalated_human",
        "contradictory": "escalated_human",
    }
    return mapping[resolution_disposition]


def _policy_source_snapshots(
    *,
    repository_root: Path | None = None,
) -> list[dict[str, str]]:
    root = repository_root or _resolve_repository_root()
    snapshots = [
        {
            "path": path_text,
            "sha256": _sha256_repo_file(
                path_text,
                field_name="policy_sources.path",
                repository_root=root,
            ),
        }
        for path_text in _policy_source_paths()
    ]
    snapshots.sort(key=lambda entry: entry["path"])
    return snapshots


class SyntheticPressureMismatchPolicySourceSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid")

    path: str = Field(min_length=1)
    sha256: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(
        self,
        info: ValidationInfo,
    ) -> "SyntheticPressureMismatchPolicySourceSnapshot":
        repository_root = _resolve_repository_root(info)
        self.path = _normalize_repo_relative_path(self.path, field_name="policy_sources.path")
        if self.sha256 != _sha256_repo_file(
            self.path,
            field_name="policy_sources.path",
            repository_root=repository_root,
        ):
            raise ValueError("policy_sources.sha256 must match policy source bytes")
        return self


class SyntheticPressureMismatchOracleReplayIdentity(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_kind: SyntheticPressureMismatchHybridSourceKind
    source_binding_id: str = Field(min_length=1)
    source_fixture_path: str = Field(min_length=1)
    source_fixture_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    policy_sources: list[SyntheticPressureMismatchPolicySourceSnapshot] = Field(min_length=1)
    model_id: str = Field(min_length=1)
    model_version: str = Field(min_length=1)
    reasoning_effort: SyntheticPressureMismatchReasoningEffort
    evaluator_version: Literal["1"] = "1"

    @model_validator(mode="after")
    def _validate_contract(
        self,
        info: ValidationInfo,
    ) -> "SyntheticPressureMismatchOracleReplayIdentity":
        repository_root = _resolve_repository_root(info)
        self.source_fixture_path = _normalize_repo_relative_path(
            self.source_fixture_path,
            field_name="replay_identity.source_fixture_path",
        )
        if self.source_fixture_sha256 != _sha256_repo_file(
            self.source_fixture_path,
            field_name="replay_identity.source_fixture_path",
            repository_root=repository_root,
        ):
            raise ValueError(
                "replay_identity.source_fixture_sha256 must match source fixture bytes"
            )
        _assert_non_empty_text(
            self.source_binding_id,
            field_name="replay_identity.source_binding_id",
        )
        _assert_non_empty_text(self.model_id, field_name="replay_identity.model_id")
        _assert_non_empty_text(
            self.model_version,
            field_name="replay_identity.model_version",
        )
        _assert_sorted_unique(
            [entry.path for entry in self.policy_sources],
            field_name="replay_identity.policy_sources.path",
            allow_empty=False,
        )
        actual_policy_paths = [entry.path for entry in self.policy_sources]
        if actual_policy_paths != _expected_policy_source_paths():
            raise ValueError(
                "replay_identity.policy_sources.path must match the full V39-E policy "
                "source set"
            )
        return self


class SyntheticPressureMismatchOracleRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: SyntheticPressureMismatchOracleRequestSchemaVersion = (
        SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_SCHEMA
    )
    target_arc: Literal["vNext+76"] = "vNext+76"
    target_path: Literal["V39-E"] = "V39-E"
    contract_source: Literal[
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md"
        "#v39e_synthetic_pressure_mismatch_hybrid_execution_contract@1"
    ] = V39E_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE
    oracle_request_id: str = Field(min_length=1)
    checkpoint_id: str = Field(min_length=1)
    registry_schema: Literal["synthetic_pressure_mismatch_rule_registry@1"] = (
        SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA
    )
    registry_id: str = Field(min_length=1)
    registry_reference_fixture: str = Field(min_length=1)
    source_kind: SyntheticPressureMismatchHybridSourceKind
    conformance_report_schema: (
        Literal["synthetic_pressure_mismatch_conformance_report@1"] | None
    ) = None
    conformance_report_reference_fixture: str | None = None
    fix_plan_schema: Literal["synthetic_pressure_mismatch_fix_plan@1"] | None = None
    fix_plan_reference_fixture: str | None = None
    local_hybrid_fixture_reference: str | None = None
    source_finding_id: str | None = None
    source_projected_item_id: str | None = None
    local_hybrid_fixture_id: str | None = None
    rule_id: str = Field(min_length=1)
    signal_kind: SyntheticPressureMismatchSignalKind
    harm_kind: SyntheticPressureMismatchHarmKind
    evidence_regime: SyntheticPressureMismatchEvidenceRegime
    allowed_action: SyntheticPressureMismatchAllowedAction
    resolution_route: SyntheticPressureMismatchResolutionRoute
    subject_kind: SyntheticPressureMismatchSubjectKind
    subject_ref: str = Field(min_length=1)
    local_subject_anchor: str = Field(min_length=1)
    interpretation_prompt: str = Field(min_length=1)
    bounded_context: str = Field(min_length=1)
    replay_identity: SyntheticPressureMismatchOracleReplayIdentity

    @model_validator(mode="after")
    def _validate_contract(
        self,
        info: ValidationInfo,
    ) -> "SyntheticPressureMismatchOracleRequest":
        repository_root = _resolve_repository_root(info)
        _assert_non_empty_text(self.oracle_request_id, field_name="oracle_request_id")
        _assert_non_empty_text(self.checkpoint_id, field_name="checkpoint_id")
        _assert_non_empty_text(self.registry_id, field_name="registry_id")
        _assert_non_empty_text(self.rule_id, field_name="rule_id")
        _assert_non_empty_text(self.subject_ref, field_name="subject_ref")
        _assert_non_empty_text(
            self.local_subject_anchor,
            field_name="local_subject_anchor",
        )
        _assert_non_empty_text(
            self.interpretation_prompt,
            field_name="interpretation_prompt",
        )
        _assert_non_empty_text(self.bounded_context, field_name="bounded_context")
        self.registry_reference_fixture = _normalize_repo_relative_path(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
        )
        registry = _load_validated_registry(
            self.registry_reference_fixture,
            repository_root=repository_root,
        )
        if registry.registry_id != self.registry_id:
            raise ValueError("registry_id must match the referenced released registry fixture")
        rules_by_id = _rule_index(registry)
        try:
            rule = rules_by_id[self.rule_id]
        except KeyError as exc:
            raise ValueError("rule_id must reference a released registry rule") from exc
        if rule.signal_kind != self.signal_kind:
            raise ValueError("signal_kind must match the referenced registry rule")
        if rule.harm_kind != self.harm_kind:
            raise ValueError("harm_kind must match the referenced registry rule")
        if rule.evidence_regime != self.evidence_regime:
            raise ValueError("evidence_regime must match the referenced registry rule")
        if rule.allowed_action != self.allowed_action:
            raise ValueError("allowed_action must match the referenced registry rule")
        if rule.resolution_route != self.resolution_route:
            raise ValueError("resolution_route must match the referenced registry rule")
        if self.resolution_route != "oracle_assisted":
            raise ValueError("oracle requests may be emitted only for oracle_assisted routes")

        source_binding_id: str
        source_fixture_path: str
        if self.source_kind == "local_hybrid_fixture":
            if self.local_hybrid_fixture_reference is None:
                raise ValueError(
                    "local_hybrid_fixture_reference is required for local_hybrid_fixture sources"
                )
            self.local_hybrid_fixture_reference = _normalize_repo_relative_path(
                self.local_hybrid_fixture_reference,
                field_name="local_hybrid_fixture_reference",
            )
            fixture = _load_local_hybrid_fixture(
                self.local_hybrid_fixture_reference,
                repository_root=repository_root,
            )
            if self.local_hybrid_fixture_id != fixture.fixture_id:
                raise ValueError(
                    "local_hybrid_fixture_id must match the referenced local hybrid fixture"
                )
            if fixture.rule_id != self.rule_id:
                raise ValueError("local hybrid fixture rule_id must match rule_id")
            if fixture.subject_kind != self.subject_kind:
                raise ValueError("subject_kind must match the local hybrid fixture")
            if fixture.subject_ref != self.subject_ref:
                raise ValueError("subject_ref must match the local hybrid fixture")
            if fixture.local_subject_anchor != self.local_subject_anchor:
                raise ValueError(
                    "local_subject_anchor must match the local hybrid fixture"
                )
            if fixture.content != self.bounded_context:
                raise ValueError(
                    "bounded_context must match the referenced local hybrid fixture content"
                )
            source_binding_id = fixture.fixture_id
            source_fixture_path = self.local_hybrid_fixture_reference
            if self.source_finding_id is not None or self.source_projected_item_id is not None:
                raise ValueError(
                    "local_hybrid_fixture sources must not carry released source ids"
                )
        elif self.source_kind == "released_fix_plan_projection":
            if self.fix_plan_reference_fixture is None:
                raise ValueError(
                    "fix_plan_reference_fixture is required for released_fix_plan_projection"
                )
            if self.source_projected_item_id is None or self.source_finding_id is None:
                raise ValueError(
                    "released_fix_plan_projection requests require source_projected_item_id "
                    "and source_finding_id"
                )
            self.fix_plan_reference_fixture = _normalize_repo_relative_path(
                self.fix_plan_reference_fixture,
                field_name="fix_plan_reference_fixture",
            )
            plan = _load_validated_fix_plan(
                self.fix_plan_reference_fixture,
                repository_root=repository_root,
            )
            if plan.registry_id != self.registry_id:
                raise ValueError("fix plan registry_id must match registry_id")
            projection = _find_projection_by_id(plan, self.source_projected_item_id)
            if projection.source_finding_id != self.source_finding_id:
                raise ValueError(
                    "source_finding_id must match the released fix-plan projection"
                )
            if projection.rule_id != self.rule_id:
                raise ValueError("rule_id must match the released fix-plan projection")
            if projection.signal_kind != self.signal_kind:
                raise ValueError(
                    "signal_kind must match the released fix-plan projection"
                )
            if projection.harm_kind != self.harm_kind:
                raise ValueError("harm_kind must match the released fix-plan projection")
            if projection.allowed_action != self.allowed_action:
                raise ValueError(
                    "allowed_action must match the released fix-plan projection"
                )
            if projection.resolution_route != self.resolution_route:
                raise ValueError(
                    "resolution_route must match the released fix-plan projection"
                )
            observation_packet_id, _, local_locator = _parse_source_finding_id(
                self.source_finding_id
            )
            _, packet = _find_observation_packet_fixture_by_id(
                observation_packet_id,
                repository_root=repository_root,
            )
            if packet.subject_kind != self.subject_kind:
                raise ValueError(
                    "subject_kind must match the released source observation packet"
                )
            if packet.subject_ref != self.subject_ref:
                raise ValueError(
                    "subject_ref must match the released source observation packet"
                )
            if local_locator != self.local_subject_anchor:
                raise ValueError(
                    "local_subject_anchor must match the released source finding locator"
                )
            source_binding_id = self.source_projected_item_id
            source_fixture_path = self.fix_plan_reference_fixture
        else:
            if self.conformance_report_reference_fixture is None:
                raise ValueError(
                    "conformance_report_reference_fixture is required for "
                    "released_conformance_finding"
                )
            if self.source_finding_id is None:
                raise ValueError(
                    "released_conformance_finding requests require source_finding_id"
                )
            self.conformance_report_reference_fixture = _normalize_repo_relative_path(
                self.conformance_report_reference_fixture,
                field_name="conformance_report_reference_fixture",
            )
            report = _load_validated_conformance_report(
                self.conformance_report_reference_fixture,
                repository_root=repository_root,
            )
            if report.registry_id != self.registry_id:
                raise ValueError("conformance report registry_id must match registry_id")
            observation_packet_id, rule_id, local_locator = _parse_source_finding_id(
                self.source_finding_id
            )
            if rule_id != self.rule_id:
                raise ValueError("source_finding_id must embed the declared rule_id")
            _find_conformance_source_finding(report, self.source_finding_id)
            _, packet = _find_observation_packet_fixture_by_id(
                observation_packet_id,
                repository_root=repository_root,
            )
            if packet.subject_kind != self.subject_kind:
                raise ValueError(
                    "subject_kind must match the released source observation packet"
                )
            if packet.subject_ref != self.subject_ref:
                raise ValueError(
                    "subject_ref must match the released source observation packet"
                )
            if local_locator != self.local_subject_anchor:
                raise ValueError(
                    "local_subject_anchor must match the released source finding locator"
                )
            if (
                self.source_projected_item_id is not None
                or self.local_hybrid_fixture_id is not None
            ):
                raise ValueError(
                    "released_conformance_finding requests must not carry fix-plan or local "
                    "fixture ids"
                )
            source_binding_id = self.source_finding_id
            source_fixture_path = self.conformance_report_reference_fixture

        expected_checkpoint_id = _checkpoint_id(
            source_kind=self.source_kind,
            source_binding_id=source_binding_id,
            rule_id=self.rule_id,
            subject_ref=self.subject_ref,
            local_subject_anchor=self.local_subject_anchor,
        )
        if self.checkpoint_id != expected_checkpoint_id:
            raise ValueError(
                "checkpoint_id must match the source binding, subject, and rule identity"
            )
        replay_identity_payload = self.replay_identity.model_dump(
            mode="json",
            exclude_none=True,
        )
        if self.replay_identity.source_kind != self.source_kind:
            raise ValueError("replay_identity.source_kind must match source_kind")
        if self.replay_identity.source_binding_id != source_binding_id:
            raise ValueError(
                "replay_identity.source_binding_id must match the source binding"
            )
        if self.replay_identity.source_fixture_path != source_fixture_path:
            raise ValueError(
                "replay_identity.source_fixture_path must match the bound source fixture"
            )
        expected_request_id = _oracle_request_id(
            checkpoint_id=self.checkpoint_id,
            replay_identity=replay_identity_payload,
            interpretation_prompt=self.interpretation_prompt,
            bounded_context=self.bounded_context,
        )
        if self.oracle_request_id != expected_request_id:
            raise ValueError(
                "oracle_request_id must match the validated replay identity and prompt"
            )
        return self


class SyntheticPressureMismatchOracleResolution(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: SyntheticPressureMismatchOracleResolutionSchemaVersion = (
        SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_SCHEMA
    )
    target_arc: Literal["vNext+76"] = "vNext+76"
    target_path: Literal["V39-E"] = "V39-E"
    contract_source: Literal[
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md"
        "#v39e_synthetic_pressure_mismatch_hybrid_execution_contract@1"
    ] = V39E_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE
    oracle_resolution_id: str = Field(min_length=1)
    oracle_request_id: str = Field(min_length=1)
    oracle_request_reference_fixture: str = Field(min_length=1)
    checkpoint_id: str = Field(min_length=1)
    resolution_disposition: SyntheticPressureMismatchOracleDisposition
    resolution_origin: SyntheticPressureMismatchOracleResolutionOrigin
    model_id: str = Field(min_length=1)
    model_version: str = Field(min_length=1)
    reasoning_effort: SyntheticPressureMismatchReasoningEffort
    request_replay_identity_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    advisory_summary: str = Field(min_length=1)
    raw_output_text: str = Field(min_length=1)
    raw_output_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(
        self,
        info: ValidationInfo,
    ) -> "SyntheticPressureMismatchOracleResolution":
        repository_root = _resolve_repository_root(info)
        _assert_non_empty_text(
            self.oracle_resolution_id,
            field_name="oracle_resolution_id",
        )
        _assert_non_empty_text(
            self.oracle_request_id,
            field_name="oracle_request_id",
        )
        _assert_non_empty_text(self.checkpoint_id, field_name="checkpoint_id")
        _assert_non_empty_text(self.model_id, field_name="model_id")
        _assert_non_empty_text(self.model_version, field_name="model_version")
        _assert_non_empty_text(self.advisory_summary, field_name="advisory_summary")
        _assert_non_empty_text(self.raw_output_text, field_name="raw_output_text")
        self.oracle_request_reference_fixture = _normalize_repo_relative_path(
            self.oracle_request_reference_fixture,
            field_name="oracle_request_reference_fixture",
        )
        request_payload = _load_repo_json_object(
            self.oracle_request_reference_fixture,
            field_name="oracle_request_reference_fixture",
            repository_root=repository_root,
        )
        request = SyntheticPressureMismatchOracleRequest.model_validate(
            request_payload,
            context=_validation_context(repository_root),
        )
        if request.oracle_request_id != self.oracle_request_id:
            raise ValueError(
                "oracle_request_id must match the referenced oracle request fixture"
            )
        if request.checkpoint_id != self.checkpoint_id:
            raise ValueError(
                "checkpoint_id must match the referenced oracle request fixture"
            )
        if request.replay_identity.model_id != self.model_id:
            raise ValueError("model_id must match the referenced oracle request")
        if request.replay_identity.model_version != self.model_version:
            raise ValueError("model_version must match the referenced oracle request")
        if request.replay_identity.reasoning_effort != self.reasoning_effort:
            raise ValueError(
                "reasoning_effort must match the referenced oracle request"
            )
        request_replay_identity_payload = request.replay_identity.model_dump(
            mode="json",
            exclude_none=True,
        )
        if self.request_replay_identity_sha256 != _replay_identity_sha256(
            request_replay_identity_payload
        ):
            raise ValueError(
                "request_replay_identity_sha256 must match the referenced request replay identity"
            )
        if self.raw_output_sha256 != _sha256_text(self.raw_output_text):
            raise ValueError("raw_output_sha256 must match raw_output_text bytes")
        expected_resolution_id = _oracle_resolution_id(
            oracle_request_id=self.oracle_request_id,
            resolution_disposition=self.resolution_disposition,
            resolution_origin=self.resolution_origin,
            raw_output_sha256=self.raw_output_sha256,
            model_id=self.model_id,
            model_version=self.model_version,
            reasoning_effort=self.reasoning_effort,
        )
        if self.oracle_resolution_id != expected_resolution_id:
            raise ValueError(
                "oracle_resolution_id must match the referenced request and resolution payload"
            )
        return self


class SyntheticPressureMismatchCheckpointEntry(BaseModel):
    model_config = ConfigDict(
        extra="forbid",
        json_schema_extra={
            "allOf": [
                {
                    "if": {
                        "properties": {
                            "checkpoint_class": {"const": "deterministic_pass"},
                        },
                        "required": ["checkpoint_class"],
                    },
                    "then": {
                        "properties": {
                            "final_adjudication": {"const": "resolved_pass"},
                        },
                        "not": {
                            "anyOf": [
                                {"required": ["oracle_request_id"]},
                                {"required": ["oracle_resolution_id"]},
                            ]
                        },
                    },
                },
                {
                    "if": {
                        "properties": {
                            "checkpoint_class": {"const": "deterministic_fail"},
                        },
                        "required": ["checkpoint_class"],
                    },
                    "then": {
                        "properties": {
                            "final_adjudication": {"const": "resolved_fail"},
                        },
                        "not": {
                            "anyOf": [
                                {"required": ["oracle_request_id"]},
                                {"required": ["oracle_resolution_id"]},
                            ]
                        },
                    },
                },
                {
                    "if": {
                        "properties": {
                            "checkpoint_class": {"const": "oracle_needed"},
                        },
                        "required": ["checkpoint_class"],
                    },
                    "then": {
                        "required": ["oracle_request_id"],
                        "properties": {
                            "final_adjudication": {
                                "enum": [
                                    "resolved_pass",
                                    "resolved_fail",
                                    "escalated_human",
                                ]
                            },
                        },
                    },
                },
                {
                    "if": {
                        "properties": {
                            "checkpoint_class": {"const": "human_needed"},
                        },
                        "required": ["checkpoint_class"],
                    },
                    "then": {
                        "properties": {
                            "final_adjudication": {"const": "escalated_human"},
                        },
                        "not": {
                            "anyOf": [
                                {"required": ["oracle_request_id"]},
                                {"required": ["oracle_resolution_id"]},
                            ]
                        },
                    },
                },
            ]
        },
    )

    checkpoint_id: str = Field(min_length=1)
    checkpoint_class: SyntheticPressureMismatchCheckpointClass
    source_kind: SyntheticPressureMismatchHybridSourceKind
    rule_id: str = Field(min_length=1)
    signal_kind: SyntheticPressureMismatchSignalKind
    harm_kind: SyntheticPressureMismatchHarmKind
    evidence_regime: SyntheticPressureMismatchEvidenceRegime
    allowed_action: SyntheticPressureMismatchAllowedAction
    resolution_route: SyntheticPressureMismatchResolutionRoute
    subject_kind: SyntheticPressureMismatchSubjectKind
    subject_ref: str = Field(min_length=1)
    local_subject_anchor: str = Field(min_length=1)
    source_finding_id: str | None = None
    source_projected_item_id: str | None = None
    local_hybrid_fixture_id: str | None = None
    oracle_request_id: str | None = None
    oracle_resolution_id: str | None = None
    final_adjudication: SyntheticPressureMismatchFinalAdjudication

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchCheckpointEntry":
        _assert_non_empty_text(self.checkpoint_id, field_name="checkpoints[].checkpoint_id")
        _assert_non_empty_text(self.rule_id, field_name="checkpoints[].rule_id")
        _assert_non_empty_text(self.subject_ref, field_name="checkpoints[].subject_ref")
        _assert_non_empty_text(
            self.local_subject_anchor,
            field_name="checkpoints[].local_subject_anchor",
        )
        if self.source_kind == "released_fix_plan_projection":
            if self.source_projected_item_id is None or self.source_finding_id is None:
                raise ValueError(
                    "released_fix_plan_projection checkpoints require source_projected_item_id "
                    "and source_finding_id"
                )
            if self.local_hybrid_fixture_id is not None:
                raise ValueError(
                    "released_fix_plan_projection checkpoints must not carry "
                    "local_hybrid_fixture_id"
                )
        elif self.source_kind == "released_conformance_finding":
            if self.source_finding_id is None:
                raise ValueError(
                    "released_conformance_finding checkpoints require source_finding_id"
                )
            if (
                self.source_projected_item_id is not None
                or self.local_hybrid_fixture_id is not None
            ):
                raise ValueError(
                    "released_conformance_finding checkpoints must not carry fix-plan or "
                    "local fixture ids"
                )
        else:
            if self.local_hybrid_fixture_id is None:
                raise ValueError(
                    "local_hybrid_fixture checkpoints require local_hybrid_fixture_id"
                )
            if self.source_finding_id is not None or self.source_projected_item_id is not None:
                raise ValueError(
                    "local_hybrid_fixture checkpoints must not carry released source ids"
                )
        expected_final = _expected_final_adjudication_for_checkpoint_class(self.checkpoint_class)
        if expected_final is not None and self.final_adjudication != expected_final:
            raise ValueError(
                "final_adjudication must match the frozen deterministic or human transition law"
            )
        if self.checkpoint_class == "oracle_needed":
            if self.oracle_request_id is None:
                raise ValueError(
                    "oracle_needed checkpoints must emit an oracle_request_id"
                )
        else:
            if self.oracle_request_id is not None:
                raise ValueError(
                    "oracle requests may be emitted only for oracle_needed checkpoints"
                )
            if self.oracle_resolution_id is not None:
                raise ValueError(
                    "only oracle_needed checkpoints may carry oracle_resolution_id"
                )
        if self.checkpoint_class == "human_needed" and self.oracle_resolution_id is not None:
            raise ValueError("human_needed checkpoints must not carry oracle_resolution_id")
        if self.oracle_resolution_id is not None and self.oracle_request_id is None:
            raise ValueError("oracle_resolution_id requires oracle_request_id")
        return self


class SyntheticPressureMismatchCheckpointTraceDerivationMetadata(BaseModel):
    model_config = ConfigDict(extra="forbid")

    adjudicator_id: Literal[
        "adeu_core_ir.synthetic_pressure_mismatch_hybrid_execution"
        ".derive_v39e_checkpoint_trace@1"
    ] = V39E_SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_EVALUATOR_ID
    adjudicator_version: Literal["1"] = "1"
    registry_reference_fixture_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    conformance_report_reference_fixture_sha256: str | None = Field(
        default=None,
        pattern=r"^[0-9a-f]{64}$",
    )
    fix_plan_reference_fixture_sha256: str | None = Field(
        default=None,
        pattern=r"^[0-9a-f]{64}$",
    )
    local_hybrid_fixture_reference_sha256: str | None = Field(
        default=None,
        pattern=r"^[0-9a-f]{64}$",
    )
    oracle_request_reference_fixture_sha256: str | None = Field(
        default=None,
        pattern=r"^[0-9a-f]{64}$",
    )
    oracle_resolution_reference_fixture_sha256: str | None = Field(
        default=None,
        pattern=r"^[0-9a-f]{64}$",
    )
    deterministic_adjudicator_authoritative: Literal[True] = True
    oracle_output_advisory_only: Literal[True] = True
    single_oracle_round_enforced: Literal[True] = True
    cache_identity_exact_match_required: Literal[True] = True


class SyntheticPressureMismatchCheckpointTrace(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: SyntheticPressureMismatchCheckpointTraceSchemaVersion = (
        SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_SCHEMA
    )
    target_arc: Literal["vNext+76"] = "vNext+76"
    target_path: Literal["V39-E"] = "V39-E"
    contract_source: Literal[
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md"
        "#v39e_synthetic_pressure_mismatch_hybrid_execution_contract@1"
    ] = V39E_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE
    trace_id: str = Field(min_length=1)
    registry_schema: Literal["synthetic_pressure_mismatch_rule_registry@1"] = (
        SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA
    )
    registry_id: str = Field(min_length=1)
    registry_reference_fixture: str = Field(min_length=1)
    source_kind: SyntheticPressureMismatchHybridSourceKind
    conformance_report_schema: (
        Literal["synthetic_pressure_mismatch_conformance_report@1"] | None
    ) = None
    conformance_report_reference_fixture: str | None = None
    fix_plan_schema: Literal["synthetic_pressure_mismatch_fix_plan@1"] | None = None
    fix_plan_reference_fixture: str | None = None
    local_hybrid_fixture_reference: str | None = None
    oracle_request_reference_fixture: str | None = None
    oracle_resolution_reference_fixture: str | None = None
    checkpoints: list[SyntheticPressureMismatchCheckpointEntry] = Field(min_length=1)
    derivation_metadata: SyntheticPressureMismatchCheckpointTraceDerivationMetadata

    @model_validator(mode="after")
    def _validate_contract(
        self,
        info: ValidationInfo,
    ) -> "SyntheticPressureMismatchCheckpointTrace":
        repository_root = _resolve_repository_root(info)
        _assert_non_empty_text(self.trace_id, field_name="trace_id")
        _assert_non_empty_text(self.registry_id, field_name="registry_id")
        self.registry_reference_fixture = _normalize_repo_relative_path(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
        )
        registry = _load_validated_registry(
            self.registry_reference_fixture,
            repository_root=repository_root,
        )
        if registry.registry_id != self.registry_id:
            raise ValueError("registry_id must match the referenced released registry fixture")
        if (
            self.derivation_metadata.registry_reference_fixture_sha256
            != _sha256_repo_file(
                self.registry_reference_fixture,
                field_name="registry_reference_fixture",
                repository_root=repository_root,
            )
        ):
            raise ValueError(
                "derivation_metadata.registry_reference_fixture_sha256 must match "
                "registry_reference_fixture bytes"
            )
        rules_by_id = _rule_index(registry)

        report: SyntheticPressureMismatchConformanceReport | None = None
        plan: SyntheticPressureMismatchFixPlan | None = None
        local_fixture: SyntheticPressureMismatchLocalHybridFixture | None = None
        source_reference_fixture: str

        if self.source_kind == "released_fix_plan_projection":
            if self.fix_plan_reference_fixture is None:
                raise ValueError(
                    "fix_plan_reference_fixture is required for released_fix_plan_projection"
                )
            self.fix_plan_reference_fixture = _normalize_repo_relative_path(
                self.fix_plan_reference_fixture,
                field_name="fix_plan_reference_fixture",
            )
            plan = _load_validated_fix_plan(
                self.fix_plan_reference_fixture,
                repository_root=repository_root,
            )
            if plan.registry_id != self.registry_id:
                raise ValueError("fix plan registry_id must match registry_id")
            if self.fix_plan_schema != SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_SCHEMA:
                raise ValueError("fix_plan_schema must be synthetic_pressure_mismatch_fix_plan@1")
            if self.conformance_report_reference_fixture is None:
                raise ValueError(
                    "conformance_report_reference_fixture is required for "
                    "released_fix_plan_projection"
                )
            self.conformance_report_reference_fixture = _normalize_repo_relative_path(
                self.conformance_report_reference_fixture,
                field_name="conformance_report_reference_fixture",
            )
            report = _load_validated_conformance_report(
                self.conformance_report_reference_fixture,
                repository_root=repository_root,
            )
            if report.report_id != plan.conformance_report_id:
                raise ValueError(
                    "conformance_report_reference_fixture must match the released fix-plan source"
                )
            if report.registry_id != self.registry_id:
                raise ValueError("conformance report registry_id must match registry_id")
            if (
                self.derivation_metadata.fix_plan_reference_fixture_sha256
                != _sha256_repo_file(
                    self.fix_plan_reference_fixture,
                    field_name="fix_plan_reference_fixture",
                    repository_root=repository_root,
                )
            ):
                raise ValueError(
                    "derivation_metadata.fix_plan_reference_fixture_sha256 must match "
                    "fix_plan_reference_fixture bytes"
                )
            if (
                self.derivation_metadata.conformance_report_reference_fixture_sha256
                != _sha256_repo_file(
                    self.conformance_report_reference_fixture,
                    field_name="conformance_report_reference_fixture",
                    repository_root=repository_root,
                )
            ):
                raise ValueError(
                    "derivation_metadata.conformance_report_reference_fixture_sha256 must "
                    "match conformance_report_reference_fixture bytes"
                )
            source_reference_fixture = self.fix_plan_reference_fixture
        elif self.source_kind == "released_conformance_finding":
            if self.conformance_report_reference_fixture is None:
                raise ValueError(
                    "conformance_report_reference_fixture is required for "
                    "released_conformance_finding"
                )
            self.conformance_report_reference_fixture = _normalize_repo_relative_path(
                self.conformance_report_reference_fixture,
                field_name="conformance_report_reference_fixture",
            )
            report = _load_validated_conformance_report(
                self.conformance_report_reference_fixture,
                repository_root=repository_root,
            )
            if report.registry_id != self.registry_id:
                raise ValueError("conformance report registry_id must match registry_id")
            if (
                self.derivation_metadata.conformance_report_reference_fixture_sha256
                != _sha256_repo_file(
                    self.conformance_report_reference_fixture,
                    field_name="conformance_report_reference_fixture",
                    repository_root=repository_root,
                )
            ):
                raise ValueError(
                    "derivation_metadata.conformance_report_reference_fixture_sha256 must "
                    "match conformance_report_reference_fixture bytes"
                )
            source_reference_fixture = self.conformance_report_reference_fixture
        else:
            if self.local_hybrid_fixture_reference is None:
                raise ValueError(
                    "local_hybrid_fixture_reference is required for local_hybrid_fixture"
                )
            self.local_hybrid_fixture_reference = _normalize_repo_relative_path(
                self.local_hybrid_fixture_reference,
                field_name="local_hybrid_fixture_reference",
            )
            local_fixture = _load_local_hybrid_fixture(
                self.local_hybrid_fixture_reference,
                repository_root=repository_root,
            )
            if (
                self.derivation_metadata.local_hybrid_fixture_reference_sha256
                != _sha256_repo_file(
                    self.local_hybrid_fixture_reference,
                    field_name="local_hybrid_fixture_reference",
                    repository_root=repository_root,
                )
            ):
                raise ValueError(
                    "derivation_metadata.local_hybrid_fixture_reference_sha256 must match "
                    "local_hybrid_fixture_reference bytes"
                )
            source_reference_fixture = self.local_hybrid_fixture_reference

        request: SyntheticPressureMismatchOracleRequest | None = None
        resolution: SyntheticPressureMismatchOracleResolution | None = None
        if self.oracle_request_reference_fixture is not None:
            self.oracle_request_reference_fixture = _normalize_repo_relative_path(
                self.oracle_request_reference_fixture,
                field_name="oracle_request_reference_fixture",
            )
            request_payload = _load_repo_json_object(
                self.oracle_request_reference_fixture,
                field_name="oracle_request_reference_fixture",
                repository_root=repository_root,
            )
            request = SyntheticPressureMismatchOracleRequest.model_validate(
                request_payload,
                context=_validation_context(repository_root),
            )
            if (
                self.derivation_metadata.oracle_request_reference_fixture_sha256
                != _sha256_repo_file(
                    self.oracle_request_reference_fixture,
                    field_name="oracle_request_reference_fixture",
                    repository_root=repository_root,
                )
            ):
                raise ValueError(
                    "derivation_metadata.oracle_request_reference_fixture_sha256 must match "
                    "oracle_request_reference_fixture bytes"
                )
        if self.oracle_resolution_reference_fixture is not None:
            self.oracle_resolution_reference_fixture = _normalize_repo_relative_path(
                self.oracle_resolution_reference_fixture,
                field_name="oracle_resolution_reference_fixture",
            )
            if request is None:
                raise ValueError(
                    "oracle_resolution_reference_fixture requires "
                    "oracle_request_reference_fixture"
                )
            resolution_payload = _load_repo_json_object(
                self.oracle_resolution_reference_fixture,
                field_name="oracle_resolution_reference_fixture",
                repository_root=repository_root,
            )
            resolution = SyntheticPressureMismatchOracleResolution.model_validate(
                resolution_payload,
                context=_validation_context(repository_root),
            )
            if (
                self.derivation_metadata.oracle_resolution_reference_fixture_sha256
                != _sha256_repo_file(
                    self.oracle_resolution_reference_fixture,
                    field_name="oracle_resolution_reference_fixture",
                    repository_root=repository_root,
                )
            ):
                raise ValueError(
                    "derivation_metadata.oracle_resolution_reference_fixture_sha256 must match "
                    "oracle_resolution_reference_fixture bytes"
                )
        elif request is not None:
            raise ValueError(
                "oracle_request_reference_fixture requires oracle_resolution_reference_fixture"
            )

        checkpoint_identities: list[str] = []
        oracle_needed_ids: list[str] = []
        for checkpoint in self.checkpoints:
            try:
                rule = rules_by_id[checkpoint.rule_id]
            except KeyError as exc:
                raise ValueError(
                    "checkpoints[].rule_id must reference a released registry rule"
                ) from exc
            if checkpoint.signal_kind != rule.signal_kind:
                raise ValueError(
                    "checkpoints[].signal_kind must match the referenced registry rule"
                )
            if checkpoint.harm_kind != rule.harm_kind:
                raise ValueError(
                    "checkpoints[].harm_kind must match the referenced registry rule"
                )
            if checkpoint.evidence_regime != rule.evidence_regime:
                raise ValueError(
                    "checkpoints[].evidence_regime must match the referenced registry rule"
                )
            if checkpoint.allowed_action != rule.allowed_action:
                raise ValueError(
                    "checkpoints[].allowed_action must match the referenced registry rule"
                )
            if checkpoint.resolution_route != rule.resolution_route:
                raise ValueError(
                    "checkpoints[].resolution_route must match the referenced registry rule"
                )

            if checkpoint.source_kind != self.source_kind:
                raise ValueError("all checkpoints must match trace source_kind")

            source_binding_id: str
            if self.source_kind == "released_fix_plan_projection":
                assert plan is not None
                projection = _find_projection_by_id(
                    plan,
                    checkpoint.source_projected_item_id or "",
                )
                if checkpoint.source_finding_id != projection.source_finding_id:
                    raise ValueError(
                        "checkpoints[].source_finding_id must match the released fix-plan "
                        "projection"
                    )
                if checkpoint.allowed_action != projection.allowed_action:
                    raise ValueError(
                        "checkpoints[].allowed_action must match the released fix-plan "
                        "projection"
                    )
                observation_packet_id, _, local_locator = _parse_source_finding_id(
                    checkpoint.source_finding_id or ""
                )
                _, packet = _find_observation_packet_fixture_by_id(
                    observation_packet_id,
                    repository_root=repository_root,
                )
                if packet.subject_kind != checkpoint.subject_kind:
                    raise ValueError(
                        "checkpoints[].subject_kind must match the released source packet"
                    )
                if packet.subject_ref != checkpoint.subject_ref:
                    raise ValueError(
                        "checkpoints[].subject_ref must match the released source packet"
                    )
                if local_locator != checkpoint.local_subject_anchor:
                    raise ValueError(
                        "checkpoints[].local_subject_anchor must match the released source "
                        "finding locator"
                    )
                source_binding_id = checkpoint.source_projected_item_id or ""
            elif self.source_kind == "released_conformance_finding":
                assert report is not None
                source_finding_id = checkpoint.source_finding_id or ""
                _find_conformance_source_finding(report, source_finding_id)
                observation_packet_id, _, local_locator = _parse_source_finding_id(
                    source_finding_id
                )
                _, packet = _find_observation_packet_fixture_by_id(
                    observation_packet_id,
                    repository_root=repository_root,
                )
                if packet.subject_kind != checkpoint.subject_kind:
                    raise ValueError(
                        "checkpoints[].subject_kind must match the released source packet"
                    )
                if packet.subject_ref != checkpoint.subject_ref:
                    raise ValueError(
                        "checkpoints[].subject_ref must match the released source packet"
                    )
                if local_locator != checkpoint.local_subject_anchor:
                    raise ValueError(
                        "checkpoints[].local_subject_anchor must match the released source "
                        "finding locator"
                    )
                source_binding_id = source_finding_id
            else:
                assert local_fixture is not None
                if checkpoint.local_hybrid_fixture_id != local_fixture.fixture_id:
                    raise ValueError(
                        "checkpoints[].local_hybrid_fixture_id must match the referenced "
                        "local hybrid fixture"
                    )
                if checkpoint.subject_kind != local_fixture.subject_kind:
                    raise ValueError(
                        "checkpoints[].subject_kind must match the local hybrid fixture"
                    )
                if checkpoint.subject_ref != local_fixture.subject_ref:
                    raise ValueError(
                        "checkpoints[].subject_ref must match the local hybrid fixture"
                    )
                if checkpoint.local_subject_anchor != local_fixture.local_subject_anchor:
                    raise ValueError(
                        "checkpoints[].local_subject_anchor must match the local hybrid "
                        "fixture"
                    )
                if checkpoint.rule_id != local_fixture.rule_id:
                    raise ValueError(
                        "checkpoints[].rule_id must match the local hybrid fixture rule_id"
                    )
                source_binding_id = checkpoint.local_hybrid_fixture_id or ""

            expected_checkpoint_id = _checkpoint_id(
                source_kind=checkpoint.source_kind,
                source_binding_id=source_binding_id,
                rule_id=checkpoint.rule_id,
                subject_ref=checkpoint.subject_ref,
                local_subject_anchor=checkpoint.local_subject_anchor,
            )
            if checkpoint.checkpoint_id != expected_checkpoint_id:
                raise ValueError(
                    "checkpoints[].checkpoint_id must match the bound source and subject"
                )

            if checkpoint.resolution_route == "deterministic_only":
                if checkpoint.checkpoint_class not in {
                    "deterministic_pass",
                    "deterministic_fail",
                }:
                    raise ValueError(
                        "deterministic_only checkpoints must stay deterministic in V39-E"
                    )
            elif checkpoint.resolution_route == "human_only":
                if checkpoint.checkpoint_class != "human_needed":
                    raise ValueError(
                        "human_only checkpoints must classify as human_needed"
                    )
            else:
                if checkpoint.checkpoint_class != "oracle_needed":
                    raise ValueError(
                        "oracle_assisted checkpoints must classify as oracle_needed"
                    )

            if checkpoint.checkpoint_class == "oracle_needed":
                oracle_needed_ids.append(checkpoint.checkpoint_id)
                if request is None or resolution is None:
                    raise ValueError(
                        "oracle_needed checkpoints require request and resolution fixtures"
                    )
                if checkpoint.oracle_request_id != request.oracle_request_id:
                    raise ValueError(
                        "checkpoints[].oracle_request_id must match the referenced oracle "
                        "request"
                    )
                if checkpoint.oracle_resolution_id != resolution.oracle_resolution_id:
                    raise ValueError(
                        "checkpoints[].oracle_resolution_id must match the referenced oracle "
                        "resolution"
                    )
                if request.checkpoint_id != checkpoint.checkpoint_id:
                    raise ValueError(
                        "referenced oracle request must bind the same checkpoint_id"
                    )
                if resolution.checkpoint_id != checkpoint.checkpoint_id:
                    raise ValueError(
                        "referenced oracle resolution must bind the same checkpoint_id"
                    )
                expected_final = _expected_final_adjudication_for_resolution(
                    resolution.resolution_disposition
                )
                if checkpoint.final_adjudication != expected_final:
                    raise ValueError(
                        "oracle_needed final_adjudication must match the referenced oracle "
                        "resolution disposition"
                    )
            else:
                if (
                    checkpoint.oracle_request_id is not None
                    or checkpoint.oracle_resolution_id is not None
                ):
                    raise ValueError(
                        "non-oracle checkpoints must not carry oracle request or resolution ids"
                    )

            checkpoint_identities.append(
                "::".join(
                    (
                        checkpoint.source_kind,
                        source_binding_id,
                        checkpoint.rule_id,
                        checkpoint.subject_ref,
                        checkpoint.local_subject_anchor,
                    )
                )
            )

        _assert_sorted_unique(
            sorted(checkpoint.checkpoint_id for checkpoint in self.checkpoints),
            field_name="checkpoints.checkpoint_id",
            allow_empty=False,
        )
        _assert_sorted_unique(
            sorted(checkpoint_identities),
            field_name="checkpoints.identity",
            allow_empty=False,
        )
        if len(oracle_needed_ids) > 1:
            raise ValueError(
                "V39-E first baseline allows at most one oracle_needed checkpoint per trace"
            )
        expected_trace_id = _trace_id(
            source_kind=self.source_kind,
            source_reference_fixture=source_reference_fixture,
            checkpoint_ids=sorted(checkpoint.checkpoint_id for checkpoint in self.checkpoints),
            oracle_request_id=request.oracle_request_id if request is not None else None,
            oracle_resolution_id=(
                resolution.oracle_resolution_id if resolution is not None else None
            ),
        )
        if self.trace_id != expected_trace_id:
            raise ValueError(
                "trace_id must match the validated source fixture and checkpoint set"
            )
        return self


def canonicalize_synthetic_pressure_mismatch_oracle_request_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = SyntheticPressureMismatchOracleRequest.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_synthetic_pressure_mismatch_oracle_resolution_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = SyntheticPressureMismatchOracleResolution.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = SyntheticPressureMismatchCheckpointTrace.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return model.model_dump(mode="json", exclude_none=True)


def derive_v39e_oracle_request(
    local_hybrid_fixture_reference: str = DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH,
    *,
    model_id: str = "gpt-5.4",
    model_version: str = "2026-03-01",
    reasoning_effort: SyntheticPressureMismatchReasoningEffort = "xhigh",
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchOracleRequest:
    normalized_fixture_path = _normalize_repo_relative_path(
        local_hybrid_fixture_reference,
        field_name="local_hybrid_fixture_reference",
    )
    fixture = _load_local_hybrid_fixture(
        normalized_fixture_path,
        repository_root=repository_root,
    )
    registry_reference_fixture = (
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/"
        "synthetic_pressure_mismatch_rule_registry_v73_reference.json"
    )
    registry = _load_validated_registry(
        registry_reference_fixture,
        repository_root=repository_root,
    )
    rule = _rule_index(registry)[fixture.rule_id]
    if rule.resolution_route != "oracle_assisted":
        raise ValueError(
            "derive_v39e_oracle_request requires a local hybrid fixture whose rule "
            "uses resolution_route oracle_assisted"
        )
    checkpoint_id = _checkpoint_id(
        source_kind="local_hybrid_fixture",
        source_binding_id=fixture.fixture_id,
        rule_id=rule.rule_id,
        subject_ref=fixture.subject_ref,
        local_subject_anchor=fixture.local_subject_anchor,
    )
    interpretation_prompt = (
        "Interpret whether the anchored subject supports the released pressure-mismatch "
        f"subpattern {rule.subpattern} under the current counterexample policy."
    )
    bounded_context = fixture.content
    replay_identity = {
        "source_kind": "local_hybrid_fixture",
        "source_binding_id": fixture.fixture_id,
        "source_fixture_path": normalized_fixture_path,
        "source_fixture_sha256": _sha256_repo_file(
            normalized_fixture_path,
            field_name="local_hybrid_fixture_reference",
            repository_root=repository_root,
        ),
        "policy_sources": _policy_source_snapshots(repository_root=repository_root),
        "model_id": model_id,
        "model_version": model_version,
        "reasoning_effort": reasoning_effort,
        "evaluator_version": "1",
    }
    payload = {
        "oracle_request_id": _oracle_request_id(
            checkpoint_id=checkpoint_id,
            replay_identity=replay_identity,
            interpretation_prompt=interpretation_prompt,
            bounded_context=bounded_context,
        ),
        "checkpoint_id": checkpoint_id,
        "registry_id": registry.registry_id,
        "registry_reference_fixture": registry_reference_fixture,
        "source_kind": "local_hybrid_fixture",
        "local_hybrid_fixture_reference": normalized_fixture_path,
        "local_hybrid_fixture_id": fixture.fixture_id,
        "rule_id": rule.rule_id,
        "signal_kind": rule.signal_kind,
        "harm_kind": rule.harm_kind,
        "evidence_regime": rule.evidence_regime,
        "allowed_action": rule.allowed_action,
        "resolution_route": rule.resolution_route,
        "subject_kind": fixture.subject_kind,
        "subject_ref": fixture.subject_ref,
        "local_subject_anchor": fixture.local_subject_anchor,
        "interpretation_prompt": interpretation_prompt,
        "bounded_context": bounded_context,
        "replay_identity": replay_identity,
    }
    return SyntheticPressureMismatchOracleRequest.model_validate(
        payload,
        context=_validation_context(repository_root),
    )


def derive_v39e_oracle_resolution(
    oracle_request_reference_fixture: str,
    *,
    resolution_disposition: SyntheticPressureMismatchOracleDisposition,
    advisory_summary: str,
    raw_output_text: str,
    resolution_origin: SyntheticPressureMismatchOracleResolutionOrigin = (
        "fresh_model_output"
    ),
    model_id: str = "gpt-5.4",
    model_version: str = "2026-03-01",
    reasoning_effort: SyntheticPressureMismatchReasoningEffort = "xhigh",
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchOracleResolution:
    normalized_request_path = _normalize_repo_relative_path(
        oracle_request_reference_fixture,
        field_name="oracle_request_reference_fixture",
    )
    request_payload = _load_repo_json_object(
        normalized_request_path,
        field_name="oracle_request_reference_fixture",
        repository_root=repository_root,
    )
    request = SyntheticPressureMismatchOracleRequest.model_validate(
        request_payload,
        context=_validation_context(repository_root),
    )
    replay_identity_payload = request.replay_identity.model_dump(mode="json", exclude_none=True)
    raw_output_sha256 = _sha256_text(raw_output_text)
    payload = {
        "oracle_resolution_id": _oracle_resolution_id(
            oracle_request_id=request.oracle_request_id,
            resolution_disposition=resolution_disposition,
            resolution_origin=resolution_origin,
            raw_output_sha256=raw_output_sha256,
            model_id=model_id,
            model_version=model_version,
            reasoning_effort=reasoning_effort,
        ),
        "oracle_request_id": request.oracle_request_id,
        "oracle_request_reference_fixture": normalized_request_path,
        "checkpoint_id": request.checkpoint_id,
        "resolution_disposition": resolution_disposition,
        "resolution_origin": resolution_origin,
        "model_id": model_id,
        "model_version": model_version,
        "reasoning_effort": reasoning_effort,
        "request_replay_identity_sha256": _replay_identity_sha256(replay_identity_payload),
        "advisory_summary": advisory_summary,
        "raw_output_text": raw_output_text,
        "raw_output_sha256": raw_output_sha256,
    }
    return SyntheticPressureMismatchOracleResolution.model_validate(
        payload,
        context=_validation_context(repository_root),
    )


def _build_checkpoint_from_fix_plan_projection(
    *,
    projection: SyntheticPressureMismatchProjectedPlanItem,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    observation_packet_id, _, local_anchor = _parse_source_finding_id(
        projection.source_finding_id
    )
    _, packet = _find_observation_packet_fixture_by_id(
        observation_packet_id,
        repository_root=repository_root,
    )
    checkpoint_id = _checkpoint_id(
        source_kind="released_fix_plan_projection",
        source_binding_id=projection.projected_item_id,
        rule_id=projection.rule_id,
        subject_ref=packet.subject_ref,
        local_subject_anchor=local_anchor,
    )
    return {
        "checkpoint_id": checkpoint_id,
        "checkpoint_class": "deterministic_fail",
        "source_kind": "released_fix_plan_projection",
        "rule_id": projection.rule_id,
        "signal_kind": projection.signal_kind,
        "harm_kind": projection.harm_kind,
        "evidence_regime": "deterministic_local",
        "allowed_action": projection.allowed_action,
        "resolution_route": projection.resolution_route,
        "subject_kind": packet.subject_kind,
        "subject_ref": packet.subject_ref,
        "local_subject_anchor": local_anchor,
        "source_finding_id": projection.source_finding_id,
        "source_projected_item_id": projection.projected_item_id,
        "final_adjudication": "resolved_fail",
    }


def _build_checkpoint_from_conformance_finding(
    *,
    source_finding_id: str,
    rules_by_id: dict[str, SyntheticPressureMismatchRule],
    request: SyntheticPressureMismatchOracleRequest | None = None,
    resolution: SyntheticPressureMismatchOracleResolution | None = None,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    observation_packet_id, rule_id, local_anchor = _parse_source_finding_id(source_finding_id)
    _, packet = _find_observation_packet_fixture_by_id(
        observation_packet_id,
        repository_root=repository_root,
    )
    rule = rules_by_id[rule_id]
    checkpoint_class: SyntheticPressureMismatchCheckpointClass
    final_adjudication: SyntheticPressureMismatchFinalAdjudication
    if rule.resolution_route == "deterministic_only":
        checkpoint_class = "deterministic_fail"
        final_adjudication = "resolved_fail"
    elif rule.resolution_route == "human_only":
        checkpoint_class = "human_needed"
        final_adjudication = "escalated_human"
    else:
        if request is None or resolution is None:
            raise ValueError(
                "oracle_assisted released conformance findings require oracle request "
                "and resolution fixtures"
            )
        if request.source_kind != "released_conformance_finding":
            raise ValueError(
                "oracle_assisted released conformance findings require "
                "released_conformance_finding oracle requests"
            )
        if request.source_finding_id != source_finding_id:
            raise ValueError(
                "oracle request must bind the exact released conformance finding"
            )
        if request.rule_id != rule_id:
            raise ValueError("oracle request rule_id must match the source finding")
        if request.subject_kind != packet.subject_kind:
            raise ValueError("oracle request subject_kind must match the source packet")
        if request.subject_ref != packet.subject_ref:
            raise ValueError("oracle request subject_ref must match the source packet")
        if request.local_subject_anchor != local_anchor:
            raise ValueError(
                "oracle request local_subject_anchor must match the source finding locator"
            )
        if resolution.oracle_request_id != request.oracle_request_id:
            raise ValueError(
                "oracle resolution must bind the released conformance oracle request"
            )
        checkpoint_class = "oracle_needed"
        final_adjudication = _expected_final_adjudication_for_resolution(
            resolution.resolution_disposition
        )
    payload = {
        "checkpoint_id": _checkpoint_id(
            source_kind="released_conformance_finding",
            source_binding_id=source_finding_id,
            rule_id=rule_id,
            subject_ref=packet.subject_ref,
            local_subject_anchor=local_anchor,
        ),
        "checkpoint_class": checkpoint_class,
        "source_kind": "released_conformance_finding",
        "rule_id": rule_id,
        "signal_kind": rule.signal_kind,
        "harm_kind": rule.harm_kind,
        "evidence_regime": rule.evidence_regime,
        "allowed_action": rule.allowed_action,
        "resolution_route": rule.resolution_route,
        "subject_kind": packet.subject_kind,
        "subject_ref": packet.subject_ref,
        "local_subject_anchor": local_anchor,
        "source_finding_id": source_finding_id,
        "final_adjudication": final_adjudication,
    }
    if request is not None:
        payload["oracle_request_id"] = request.oracle_request_id
    if resolution is not None:
        payload["oracle_resolution_id"] = resolution.oracle_resolution_id
    return payload


def _build_checkpoint_from_local_hybrid_fixture(
    *,
    fixture: SyntheticPressureMismatchLocalHybridFixture,
    rule: SyntheticPressureMismatchRule,
    request: SyntheticPressureMismatchOracleRequest | None,
    resolution: SyntheticPressureMismatchOracleResolution | None,
) -> dict[str, Any]:
    checkpoint_id = _checkpoint_id(
        source_kind="local_hybrid_fixture",
        source_binding_id=fixture.fixture_id,
        rule_id=rule.rule_id,
        subject_ref=fixture.subject_ref,
        local_subject_anchor=fixture.local_subject_anchor,
    )
    if rule.resolution_route == "human_only":
        checkpoint_class: SyntheticPressureMismatchCheckpointClass = "human_needed"
        final_adjudication: SyntheticPressureMismatchFinalAdjudication = "escalated_human"
    elif rule.resolution_route == "oracle_assisted":
        checkpoint_class = "oracle_needed"
        if resolution is None:
            raise ValueError(
                "oracle_assisted local hybrid fixtures require an oracle resolution"
            )
        final_adjudication = _expected_final_adjudication_for_resolution(
            resolution.resolution_disposition
        )
    else:
        checkpoint_class = "deterministic_fail"
        final_adjudication = "resolved_fail"
    payload: dict[str, Any] = {
        "checkpoint_id": checkpoint_id,
        "checkpoint_class": checkpoint_class,
        "source_kind": "local_hybrid_fixture",
        "rule_id": rule.rule_id,
        "signal_kind": rule.signal_kind,
        "harm_kind": rule.harm_kind,
        "evidence_regime": rule.evidence_regime,
        "allowed_action": rule.allowed_action,
        "resolution_route": rule.resolution_route,
        "subject_kind": fixture.subject_kind,
        "subject_ref": fixture.subject_ref,
        "local_subject_anchor": fixture.local_subject_anchor,
        "local_hybrid_fixture_id": fixture.fixture_id,
        "final_adjudication": final_adjudication,
    }
    if request is not None:
        payload["oracle_request_id"] = request.oracle_request_id
    if resolution is not None:
        payload["oracle_resolution_id"] = resolution.oracle_resolution_id
    return payload


def derive_v39e_checkpoint_trace(
    *,
    fix_plan_reference_fixture: str | None = None,
    conformance_report_reference_fixture: str | None = None,
    local_hybrid_fixture_reference: str | None = None,
    oracle_request_reference_fixture: str | None = None,
    oracle_resolution_reference_fixture: str | None = None,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchCheckpointTrace:
    sources = [
        fix_plan_reference_fixture is not None,
        conformance_report_reference_fixture is not None,
        local_hybrid_fixture_reference is not None,
    ]
    if sum(sources) != 1:
        raise ValueError(
            "derive_v39e_checkpoint_trace requires exactly one of fix_plan, "
            "conformance_report, or local_hybrid_fixture"
        )

    if fix_plan_reference_fixture is not None:
        normalized_fix_plan_path = _normalize_repo_relative_path(
            fix_plan_reference_fixture,
            field_name="fix_plan_reference_fixture",
        )
        plan = _load_validated_fix_plan(
            normalized_fix_plan_path,
            repository_root=repository_root,
        )
        registry = _load_validated_registry(
            plan.registry_reference_fixture,
            repository_root=repository_root,
        )
        checkpoints = [
            _build_checkpoint_from_fix_plan_projection(
                projection=projection,
                repository_root=repository_root,
            )
            for projection in (
                plan.forward_agent_projections + plan.post_optimizer_projections
            )
        ]
        checkpoints.sort(key=lambda entry: entry["checkpoint_id"])
        source_kind: SyntheticPressureMismatchHybridSourceKind = (
            "released_fix_plan_projection"
        )
        trace_payload = {
            "registry_id": registry.registry_id,
            "registry_reference_fixture": plan.registry_reference_fixture,
            "source_kind": source_kind,
            "conformance_report_schema": SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA,
            "conformance_report_reference_fixture": plan.conformance_report_reference_fixture,
            "fix_plan_schema": SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_SCHEMA,
            "fix_plan_reference_fixture": normalized_fix_plan_path,
            "checkpoints": checkpoints,
            "derivation_metadata": {
                "registry_reference_fixture_sha256": _sha256_repo_file(
                    plan.registry_reference_fixture,
                    field_name="registry_reference_fixture",
                    repository_root=repository_root,
                ),
                "conformance_report_reference_fixture_sha256": _sha256_repo_file(
                    plan.conformance_report_reference_fixture,
                    field_name="conformance_report_reference_fixture",
                    repository_root=repository_root,
                ),
                "fix_plan_reference_fixture_sha256": _sha256_repo_file(
                    normalized_fix_plan_path,
                    field_name="fix_plan_reference_fixture",
                    repository_root=repository_root,
                ),
            },
        }
        trace_payload["trace_id"] = _trace_id(
            source_kind=source_kind,
            source_reference_fixture=normalized_fix_plan_path,
            checkpoint_ids=sorted(entry["checkpoint_id"] for entry in checkpoints),
            oracle_request_id=None,
            oracle_resolution_id=None,
        )
    elif conformance_report_reference_fixture is not None:
        normalized_report_path = _normalize_repo_relative_path(
            conformance_report_reference_fixture,
            field_name="conformance_report_reference_fixture",
        )
        report = _load_validated_conformance_report(
            normalized_report_path,
            repository_root=repository_root,
        )
        registry = _load_validated_registry(
            report.registry_reference_fixture,
            repository_root=repository_root,
        )
        rules_by_id = _rule_index(registry)
        source_finding_ids = sorted(
            {
                _source_finding_id_from_parts(
                    observation_packet_id=ref.observation_packet_id,
                    rule_id=ref.rule_id,
                    local_observation_locator=ref.local_observation_locator,
                )
                for refs in (
                    report.safe_autofix_candidates,
                    report.deterministic_high_severity_findings,
                    report.review_only_findings,
                    report.meta_governance_findings,
                )
                for ref in refs
            }
        )
        oracle_assisted_source_finding_ids = [
            source_finding_id
            for source_finding_id in source_finding_ids
            if rules_by_id[_parse_source_finding_id(source_finding_id)[1]].resolution_route
            == "oracle_assisted"
        ]
        if len(oracle_assisted_source_finding_ids) > 1:
            raise ValueError(
                "V39-E first baseline supports at most one released conformance "
                "oracle_assisted finding per trace"
            )

        request = None
        resolution = None
        if oracle_request_reference_fixture is not None:
            normalized_request_path = _normalize_repo_relative_path(
                oracle_request_reference_fixture,
                field_name="oracle_request_reference_fixture",
            )
            request_payload = _load_repo_json_object(
                normalized_request_path,
                field_name="oracle_request_reference_fixture",
                repository_root=repository_root,
            )
            request = SyntheticPressureMismatchOracleRequest.model_validate(
                request_payload,
                context=_validation_context(repository_root),
            )
            if request.source_kind != "released_conformance_finding":
                raise ValueError(
                    "released conformance trace derivation requires "
                    "released_conformance_finding oracle requests"
                )
            if request.conformance_report_reference_fixture != normalized_report_path:
                raise ValueError(
                    "oracle request must reference the same conformance report fixture"
                )
        if oracle_resolution_reference_fixture is not None:
            if request is None:
                raise ValueError(
                    "oracle_resolution_reference_fixture requires "
                    "oracle_request_reference_fixture"
                )
            normalized_resolution_path = _normalize_repo_relative_path(
                oracle_resolution_reference_fixture,
                field_name="oracle_resolution_reference_fixture",
            )
            resolution_payload = _load_repo_json_object(
                normalized_resolution_path,
                field_name="oracle_resolution_reference_fixture",
                repository_root=repository_root,
            )
            resolution = SyntheticPressureMismatchOracleResolution.model_validate(
                resolution_payload,
                context=_validation_context(repository_root),
            )
        elif request is not None:
            raise ValueError(
                "oracle_request_reference_fixture requires "
                "oracle_resolution_reference_fixture"
            )

        oracle_assisted_source_finding_id = (
            oracle_assisted_source_finding_ids[0]
            if oracle_assisted_source_finding_ids
            else None
        )
        if oracle_assisted_source_finding_id is None:
            if request is not None or resolution is not None:
                raise ValueError(
                    "oracle request and resolution fixtures may be supplied only when "
                    "the conformance report contains an oracle_assisted finding"
                )
        else:
            if request is None or resolution is None:
                raise ValueError(
                    "oracle_assisted released conformance findings require oracle "
                    "request and resolution fixtures"
                )
            if request.source_finding_id != oracle_assisted_source_finding_id:
                raise ValueError(
                    "oracle request must bind the released oracle_assisted finding"
                )

        checkpoints = []
        for source_finding_id in source_finding_ids:
            checkpoint_request = (
                request if source_finding_id == oracle_assisted_source_finding_id else None
            )
            checkpoint_resolution = (
                resolution if source_finding_id == oracle_assisted_source_finding_id else None
            )
            checkpoints.append(
                _build_checkpoint_from_conformance_finding(
                    source_finding_id=source_finding_id,
                    rules_by_id=rules_by_id,
                    request=checkpoint_request,
                    resolution=checkpoint_resolution,
                    repository_root=repository_root,
                )
            )
        checkpoints.sort(key=lambda entry: entry["checkpoint_id"])
        source_kind = "released_conformance_finding"
        trace_payload = {
            "registry_id": registry.registry_id,
            "registry_reference_fixture": report.registry_reference_fixture,
            "source_kind": source_kind,
            "conformance_report_schema": SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA,
            "conformance_report_reference_fixture": normalized_report_path,
            "checkpoints": checkpoints,
            "derivation_metadata": {
                "registry_reference_fixture_sha256": _sha256_repo_file(
                    report.registry_reference_fixture,
                    field_name="registry_reference_fixture",
                    repository_root=repository_root,
                ),
                "conformance_report_reference_fixture_sha256": _sha256_repo_file(
                    normalized_report_path,
                    field_name="conformance_report_reference_fixture",
                    repository_root=repository_root,
                ),
            },
        }
        if request is not None:
            normalized_request_path = _normalize_repo_relative_path(
                oracle_request_reference_fixture,
                field_name="oracle_request_reference_fixture",
            )
            trace_payload["oracle_request_reference_fixture"] = normalized_request_path
            trace_payload["derivation_metadata"][
                "oracle_request_reference_fixture_sha256"
            ] = _sha256_repo_file(
                normalized_request_path,
                field_name="oracle_request_reference_fixture",
                repository_root=repository_root,
            )
        if resolution is not None:
            normalized_resolution_path = _normalize_repo_relative_path(
                oracle_resolution_reference_fixture,
                field_name="oracle_resolution_reference_fixture",
            )
            trace_payload["oracle_resolution_reference_fixture"] = normalized_resolution_path
            trace_payload["derivation_metadata"][
                "oracle_resolution_reference_fixture_sha256"
            ] = _sha256_repo_file(
                normalized_resolution_path,
                field_name="oracle_resolution_reference_fixture",
                repository_root=repository_root,
            )
        trace_payload["trace_id"] = _trace_id(
            source_kind=source_kind,
            source_reference_fixture=normalized_report_path,
            checkpoint_ids=sorted(entry["checkpoint_id"] for entry in checkpoints),
            oracle_request_id=request.oracle_request_id if request is not None else None,
            oracle_resolution_id=(
                resolution.oracle_resolution_id if resolution is not None else None
            ),
        )
    else:
        normalized_fixture_path = _normalize_repo_relative_path(
            local_hybrid_fixture_reference,
            field_name="local_hybrid_fixture_reference",
        )
        fixture = _load_local_hybrid_fixture(
            normalized_fixture_path,
            repository_root=repository_root,
        )
        registry_reference_fixture = (
            "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/"
            "synthetic_pressure_mismatch_rule_registry_v73_reference.json"
        )
        registry = _load_validated_registry(
            registry_reference_fixture,
            repository_root=repository_root,
        )
        rule = _rule_index(registry)[fixture.rule_id]
        request = None
        resolution = None
        if oracle_request_reference_fixture is not None:
            normalized_request_path = _normalize_repo_relative_path(
                oracle_request_reference_fixture,
                field_name="oracle_request_reference_fixture",
            )
            request_payload = _load_repo_json_object(
                normalized_request_path,
                field_name="oracle_request_reference_fixture",
                repository_root=repository_root,
            )
            request = SyntheticPressureMismatchOracleRequest.model_validate(
                request_payload,
                context=_validation_context(repository_root),
            )
        if oracle_resolution_reference_fixture is not None:
            normalized_resolution_path = _normalize_repo_relative_path(
                oracle_resolution_reference_fixture,
                field_name="oracle_resolution_reference_fixture",
            )
            resolution_payload = _load_repo_json_object(
                normalized_resolution_path,
                field_name="oracle_resolution_reference_fixture",
                repository_root=repository_root,
            )
            resolution = SyntheticPressureMismatchOracleResolution.model_validate(
                resolution_payload,
                context=_validation_context(repository_root),
            )
        checkpoint = _build_checkpoint_from_local_hybrid_fixture(
            fixture=fixture,
            rule=rule,
            request=request,
            resolution=resolution,
        )
        checkpoints = [checkpoint]
        source_kind = "local_hybrid_fixture"
        trace_payload = {
            "registry_id": registry.registry_id,
            "registry_reference_fixture": registry_reference_fixture,
            "source_kind": source_kind,
            "local_hybrid_fixture_reference": normalized_fixture_path,
            "checkpoints": checkpoints,
            "derivation_metadata": {
                "registry_reference_fixture_sha256": _sha256_repo_file(
                    registry_reference_fixture,
                    field_name="registry_reference_fixture",
                    repository_root=repository_root,
                ),
                "local_hybrid_fixture_reference_sha256": _sha256_repo_file(
                    normalized_fixture_path,
                    field_name="local_hybrid_fixture_reference",
                    repository_root=repository_root,
                ),
            },
        }
        if request is not None:
            normalized_request_path = _normalize_repo_relative_path(
                oracle_request_reference_fixture,
                field_name="oracle_request_reference_fixture",
            )
            trace_payload["oracle_request_reference_fixture"] = normalized_request_path
            trace_payload["derivation_metadata"][
                "oracle_request_reference_fixture_sha256"
            ] = _sha256_repo_file(
                normalized_request_path,
                field_name="oracle_request_reference_fixture",
                repository_root=repository_root,
            )
        if resolution is not None:
            normalized_resolution_path = _normalize_repo_relative_path(
                oracle_resolution_reference_fixture,
                field_name="oracle_resolution_reference_fixture",
            )
            trace_payload["oracle_resolution_reference_fixture"] = normalized_resolution_path
            trace_payload["derivation_metadata"][
                "oracle_resolution_reference_fixture_sha256"
            ] = _sha256_repo_file(
                normalized_resolution_path,
                field_name="oracle_resolution_reference_fixture",
                repository_root=repository_root,
            )
        trace_payload["trace_id"] = _trace_id(
            source_kind=source_kind,
            source_reference_fixture=normalized_fixture_path,
            checkpoint_ids=[checkpoint["checkpoint_id"]],
            oracle_request_id=request.oracle_request_id if request is not None else None,
            oracle_resolution_id=(
                resolution.oracle_resolution_id if resolution is not None else None
            ),
        )

    return SyntheticPressureMismatchCheckpointTrace.model_validate(
        trace_payload,
        context=_validation_context(repository_root),
    )


__all__ = [
    "DEFAULT_V39E_FIX_PLAN_REFERENCE_FIXTURE_PATH",
    "DEFAULT_V39E_LOCAL_HYBRID_HUMAN_FIXTURE_PATH",
    "DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH",
    "SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_SCHEMA",
    "SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_SCHEMA",
    "SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_SCHEMA",
    "V39E_SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_EVALUATOR_ID",
    "V39E_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE",
    "V39E_SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_EVALUATOR_ID",
    "V39E_SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_EVALUATOR_ID",
    "SyntheticPressureMismatchCheckpointClass",
    "SyntheticPressureMismatchCheckpointEntry",
    "SyntheticPressureMismatchCheckpointTrace",
    "SyntheticPressureMismatchCheckpointTraceDerivationMetadata",
    "SyntheticPressureMismatchFinalAdjudication",
    "SyntheticPressureMismatchHybridSourceKind",
    "SyntheticPressureMismatchLocalHybridFixture",
    "SyntheticPressureMismatchOracleDisposition",
    "SyntheticPressureMismatchOracleReplayIdentity",
    "SyntheticPressureMismatchOracleRequest",
    "SyntheticPressureMismatchOracleResolution",
    "SyntheticPressureMismatchOracleResolutionOrigin",
    "SyntheticPressureMismatchPolicySourceSnapshot",
    "SyntheticPressureMismatchReasoningEffort",
    "canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload",
    "canonicalize_synthetic_pressure_mismatch_oracle_request_payload",
    "canonicalize_synthetic_pressure_mismatch_oracle_resolution_payload",
    "derive_v39e_checkpoint_trace",
    "derive_v39e_oracle_request",
    "derive_v39e_oracle_resolution",
]
