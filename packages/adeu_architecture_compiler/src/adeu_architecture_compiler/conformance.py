from __future__ import annotations

import json
import re
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_architecture_ir import (
    ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA,
    ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
    ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA,
    ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA,
    ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA,
    AdeuArchitectureSemanticIR,
    ArchitectureBoundaryGraph,
    ArchitectureIntentPacket,
    ArchitectureOntologyFrame,
    ArchitectureWorldHypothesis,
    canonicalize_adeu_architecture_boundary_graph_payload,
    canonicalize_adeu_architecture_intent_packet_payload,
    canonicalize_adeu_architecture_ontology_frame_payload,
    canonicalize_adeu_architecture_semantic_ir_payload,
    canonicalize_adeu_architecture_world_hypothesis_payload,
)
from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json, sha256_text

ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA = "adeu_architecture_conformance_report@1"
V40B_V78_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS78.md#v78-continuation-contract-machine-checkable"
)

ArchitectureProjectionReadiness = Literal["ready", "blocked"]
ArchitectureValidationCheckFamily = Literal["ASIR-O", "ASIR-E", "ASIR-D", "ASIR-U", "ASIR-P"]

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")
_CHECK_ID_RE = re.compile(r"^(ASIR-[OEDUP])-(\d{3})$")
_HEX_64_RE = re.compile(r"^[0-9a-f]{64}$")

_CROSSING_CLASSES = {"authority_crossing", "sensitivity_crossing", "audit_crossing"}
_HUMAN_ESCALATION_DISPOSITIONS = {"escalated_human", "human_review"}
_EXPECTED_CHECKS: tuple[tuple[str, bool], ...] = (
    ("ASIR-O-001", True),
    ("ASIR-O-002", True),
    ("ASIR-O-003", True),
    ("ASIR-E-001", True),
    ("ASIR-E-002", True),
    ("ASIR-E-003", True),
    ("ASIR-D-001", True),
    ("ASIR-D-002", True),
    ("ASIR-U-001", True),
    ("ASIR-U-002", False),
    ("ASIR-P-001", True),
    ("ASIR-P-002", True),
    ("ASIR-P-003", True),
)
_EXPECTED_CHECK_REQUIREMENTS = dict(_EXPECTED_CHECKS)
_EXPECTED_CHECK_IDS = sorted(_EXPECTED_CHECK_REQUIREMENTS)


def _resolve_repository_root(explicit_root: Path | None = None) -> Path:
    if explicit_root is not None:
        return explicit_root.resolve(strict=True)
    return repo_root(anchor=Path(__file__))


def _validation_context(repository_root: Path | None = None) -> dict[str, Any]:
    return {"repository_root": repository_root}


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return normalized


def _assert_sorted_unique(
    values: list[str], *, field_name: str, allow_empty: bool = True
) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if not allow_empty and not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return sorted(normalized)


def _normalize_repo_relative_path(raw_path: str, *, field_name: str) -> str:
    value = raw_path.strip().replace("\\", "/")
    if not value:
        raise ValueError(f"{field_name} must not be empty")
    if value.startswith("/") or value.startswith("\\") or _WINDOWS_ABSOLUTE_PATH_RE.match(value):
        raise ValueError(f"{field_name} must be repo-relative")
    parts: list[str] = []
    for part in value.split("/"):
        if part in ("", "."):
            continue
        if part == "..":
            if not parts:
                raise ValueError(f"{field_name} must not escape repository root")
            parts.pop()
            continue
        parts.append(part)
    if not parts:
        raise ValueError(f"{field_name} resolves to repository root")
    return "/".join(parts)


def _sha256_repo_file(path: str, *, repository_root: Path | None = None) -> str:
    root = _resolve_repository_root(repository_root)
    file_path = root / path
    if not file_path.is_file():
        raise ValueError(f"referenced repo-relative path does not exist: {path}")
    return sha256_text(file_path.read_text(encoding="utf-8"))


def _load_repo_json(path: str, *, repository_root: Path | None = None) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    file_path = root / path
    if not file_path.is_file():
        raise ValueError(f"referenced repo-relative path does not exist: {path}")
    return json.loads(file_path.read_text(encoding="utf-8"))


def _dump_json_payload(model: BaseModel) -> dict[str, Any]:
    return model.model_dump(mode="json", exclude_none=True)


def _extract_ontology_section(frame: ArchitectureOntologyFrame) -> dict[str, Any]:
    return {
        "actors": _dump_json_payloads(frame.actors),
        "surfaces": _dump_json_payloads(frame.surfaces),
        "data_objects": _dump_json_payloads(frame.data_objects),
        "boundaries": _dump_json_payloads(frame.boundaries),
        "capabilities": _dump_json_payloads(frame.capabilities),
        "workflows": _dump_json_payloads(frame.workflows),
        "states": _dump_json_payloads(frame.states),
        "transitions": _dump_json_payloads(frame.transitions),
        "decisions": _dump_json_payloads(frame.decisions),
        "failure_modes": _dump_json_payloads(frame.failure_modes),
        "flow_steps": _dump_json_payloads(frame.flow_steps),
    }


def _dump_json_payloads(models: list[BaseModel]) -> list[dict[str, Any]]:
    return [_dump_json_payload(model) for model in models]


def _compiler_config_hash() -> str:
    return sha256_canonical_json(
        {
            "contract_source": V40B_V78_CONTRACT_SOURCE,
            "profile": "v40b_deterministic_conformance.v1",
            "checks": [
                {
                    "check_id": check_id,
                    "required": required,
                }
                for check_id, required in _EXPECTED_CHECKS
            ],
            "slice": "vNext+78",
            "target_path": "V40-B",
        }
    )


class ArchitectureCompilerProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    name: Literal["adeu_architecture_compiler.v40b"] = "adeu_architecture_compiler.v40b"
    version: str = "1"
    report_generation_profile: Literal[
        "v40b_deterministic_conformance.v1"
    ] = "v40b_deterministic_conformance.v1"
    config_hash: str = Field(default_factory=_compiler_config_hash)
    contract_source: str = V40B_V78_CONTRACT_SOURCE

    @model_validator(mode="after")
    def _validate_compiler(self) -> ArchitectureCompilerProvenance:
        object.__setattr__(
            self, "version", _assert_non_empty_text(self.version, field_name="compiler.version")
        )
        object.__setattr__(
            self,
            "contract_source",
            _assert_non_empty_text(self.contract_source, field_name="compiler.contract_source"),
        )
        if not _HEX_64_RE.match(self.config_hash):
            raise ValueError("compiler.config_hash must be a 64-character lowercase hex sha256")
        expected_hash = _compiler_config_hash()
        if self.config_hash != expected_hash:
            raise ValueError(
                "compiler.config_hash must match the fixed "
                "v40b_deterministic_conformance.v1 profile"
            )
        return self


class ArchitectureConsumedRootRef(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    artifact_schema: Literal[
        ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
        ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA,
        ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA,
        ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA,
        ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA,
    ]
    artifact_id: str
    artifact_path: str
    sha256: str

    @model_validator(mode="after")
    def _validate_ref(self, info: ValidationInfo) -> ArchitectureConsumedRootRef:
        object.__setattr__(
            self,
            "artifact_id",
            _assert_non_empty_text(self.artifact_id, field_name="artifact_id"),
        )
        normalized_path = _normalize_repo_relative_path(
            self.artifact_path,
            field_name="artifact_path",
        )
        object.__setattr__(self, "artifact_path", normalized_path)
        object.__setattr__(
            self,
            "sha256",
            _assert_non_empty_text(self.sha256, field_name="sha256"),
        )
        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            actual_hash = _sha256_repo_file(normalized_path, repository_root=repository_root)
            if actual_hash != self.sha256:
                raise ValueError(
                    "consumed_root_ref sha256 does not match repo file contents "
                    f"for {normalized_path}"
                )
        return self


class ArchitectureValidationCheckResult(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    check_id: str
    required: bool
    passed: bool
    subject_refs: list[str]
    detail: str

    @model_validator(mode="after")
    def _validate_result(self) -> ArchitectureValidationCheckResult:
        object.__setattr__(
            self, "check_id", _assert_non_empty_text(self.check_id, field_name="check_id")
        )
        object.__setattr__(
            self, "detail", _assert_non_empty_text(self.detail, field_name="detail")
        )
        object.__setattr__(
            self,
            "subject_refs",
            _assert_sorted_unique(self.subject_refs, field_name="subject_refs"),
        )
        if _CHECK_ID_RE.match(self.check_id) is None:
            raise ValueError("check_id must match ASIR-[O|E|D|U|P]-NNN")
        return self


class AdeuArchitectureConformanceReport(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA]
    architecture_id: str
    semantic_hash: str
    compiler: ArchitectureCompilerProvenance
    consumed_root_refs: list[ArchitectureConsumedRootRef]
    projection_readiness: ArchitectureProjectionReadiness
    blocking_ambiguity_refs: list[str]
    failed_check_ids: list[str]
    human_escalation_refs: list[str]
    emitted_artifact_refs: list[str]
    check_results: list[ArchitectureValidationCheckResult]

    @model_validator(mode="after")
    def _validate_report(self) -> AdeuArchitectureConformanceReport:
        object.__setattr__(
            self,
            "architecture_id",
            _assert_non_empty_text(self.architecture_id, field_name="architecture_id"),
        )
        object.__setattr__(
            self,
            "semantic_hash",
            _assert_non_empty_text(self.semantic_hash, field_name="semantic_hash"),
        )
        if not self.consumed_root_refs:
            raise ValueError("consumed_root_refs must not be empty")
        paths = [entry.artifact_path for entry in self.consumed_root_refs]
        if sorted(paths) != paths or len(paths) != len(set(paths)):
            raise ValueError(
                "consumed_root_refs must be sorted by artifact_path "
                "with no duplicates"
            )
        object.__setattr__(
            self,
            "blocking_ambiguity_refs",
            _assert_sorted_unique(
                self.blocking_ambiguity_refs, field_name="blocking_ambiguity_refs"
            ),
        )
        object.__setattr__(
            self,
            "failed_check_ids",
            _assert_sorted_unique(self.failed_check_ids, field_name="failed_check_ids"),
        )
        object.__setattr__(
            self,
            "human_escalation_refs",
            _assert_sorted_unique(self.human_escalation_refs, field_name="human_escalation_refs"),
        )
        object.__setattr__(
            self,
            "emitted_artifact_refs",
            _assert_sorted_unique(self.emitted_artifact_refs, field_name="emitted_artifact_refs"),
        )
        if self.emitted_artifact_refs:
            raise ValueError("emitted_artifact_refs must remain empty in V40-B")
        check_ids = [result.check_id for result in self.check_results]
        if sorted(check_ids) != check_ids or len(check_ids) != len(set(check_ids)):
            raise ValueError("check_results must be sorted by check_id with no duplicates")
        if check_ids != _EXPECTED_CHECK_IDS:
            raise ValueError(
                "check_results must exactly cover the fixed V40-B "
                "deterministic check profile"
            )
        for result in self.check_results:
            expected_required = _EXPECTED_CHECK_REQUIREMENTS[result.check_id]
            if result.required != expected_required:
                raise ValueError(
                    f"check_result.required must match the fixed profile for {result.check_id}"
                )
        failed_required = sorted(
            result.check_id
            for result in self.check_results
            if result.required and not result.passed
        )
        if self.failed_check_ids != failed_required:
            raise ValueError("failed_check_ids must match failed required check_results")
        expected_readiness: ArchitectureProjectionReadiness = (
            "blocked"
            if (
                self.blocking_ambiguity_refs
                or self.human_escalation_refs
                or self.failed_check_ids
            )
            else "ready"
        )
        if self.projection_readiness != expected_readiness:
            raise ValueError("projection_readiness must match blocking refs and failed_check_ids")
        return self


class ArchitectureCompilerInputBundle(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    intent_packet_path: str
    intent_packet: ArchitectureIntentPacket
    ontology_frame_path: str
    ontology_frame: ArchitectureOntologyFrame
    boundary_graph_path: str
    boundary_graph: ArchitectureBoundaryGraph
    world_hypothesis_path: str
    world_hypothesis: ArchitectureWorldHypothesis
    semantic_ir_path: str
    semantic_ir: AdeuArchitectureSemanticIR

    @model_validator(mode="after")
    def _validate_bundle(self, info: ValidationInfo) -> ArchitectureCompilerInputBundle:
        repository_root = info.context.get("repository_root") if info.context else None
        normalized_paths = {
            "intent_packet_path": _normalize_repo_relative_path(
                self.intent_packet_path, field_name="intent_packet_path"
            ),
            "ontology_frame_path": _normalize_repo_relative_path(
                self.ontology_frame_path, field_name="ontology_frame_path"
            ),
            "boundary_graph_path": _normalize_repo_relative_path(
                self.boundary_graph_path, field_name="boundary_graph_path"
            ),
            "world_hypothesis_path": _normalize_repo_relative_path(
                self.world_hypothesis_path, field_name="world_hypothesis_path"
            ),
            "semantic_ir_path": _normalize_repo_relative_path(
                self.semantic_ir_path, field_name="semantic_ir_path"
            ),
        }
        for field_name, value in normalized_paths.items():
            object.__setattr__(self, field_name, value)

        self._assert_payload_matches_repo_file(repository_root=repository_root)

        intent_packet_id = self.intent_packet.intent_packet_id
        if self.ontology_frame.intent_packet_id != intent_packet_id:
            raise ValueError("ontology_frame.intent_packet_id must match intent_packet")
        if self.boundary_graph.intent_packet_id != intent_packet_id:
            raise ValueError("boundary_graph.intent_packet_id must match intent_packet")
        if self.world_hypothesis.intent_packet_id != intent_packet_id:
            raise ValueError("world_hypothesis.intent_packet_id must match intent_packet")
        if self.semantic_ir.intent_packet_id != intent_packet_id:
            raise ValueError("semantic_ir.intent_packet_id must match intent_packet")

        authority_policy = _dump_json_payload(self.intent_packet.authority_boundary_policy)
        for artifact_name, policy in (
            (
                "ontology_frame",
                _dump_json_payload(self.ontology_frame.authority_boundary_policy),
            ),
            (
                "boundary_graph",
                _dump_json_payload(self.boundary_graph.authority_boundary_policy),
            ),
            (
                "world_hypothesis",
                _dump_json_payload(self.world_hypothesis.authority_boundary_policy),
            ),
            ("semantic_ir", _dump_json_payload(self.semantic_ir.authority_boundary_policy)),
        ):
            if policy != authority_policy:
                raise ValueError(
                    f"{artifact_name} authority_boundary_policy must match intent_packet"
                )

        if _extract_ontology_section(self.ontology_frame) != _dump_json_payload(
            self.semantic_ir.ontology
        ):
            raise ValueError("semantic_ir.ontology must exactly match consumed ontology_frame")

        if (
            self.world_hypothesis.candidate_id
            != self.semantic_ir.variant_lineage.accepted_candidate_id
        ):
            raise ValueError(
                "world_hypothesis.candidate_id must match "
                "semantic_ir.variant_lineage.accepted_candidate_id"
            )
        if not set(self.world_hypothesis.ontology_bindings).issubset(
            {item["decision_id"] for item in _dump_json_payloads(self.ontology_frame.decisions)}
            | {item["workflow_id"] for item in _dump_json_payloads(self.ontology_frame.workflows)}
            | {item["surface_id"] for item in _dump_json_payloads(self.ontology_frame.surfaces)}
        ):
            raise ValueError(
                "world_hypothesis.ontology_bindings must resolve within "
                "companion ontology_frame"
            )
        return self

    def _assert_payload_matches_repo_file(self, *, repository_root: Path | None) -> None:
        comparisons = [
            (
                self.intent_packet_path,
                canonicalize_adeu_architecture_intent_packet_payload(
                    _dump_json_payload(self.intent_packet),
                    repository_root=repository_root,
                ),
            ),
            (
                self.ontology_frame_path,
                canonicalize_adeu_architecture_ontology_frame_payload(
                    _dump_json_payload(self.ontology_frame),
                    repository_root=repository_root,
                ),
            ),
            (
                self.boundary_graph_path,
                canonicalize_adeu_architecture_boundary_graph_payload(
                    _dump_json_payload(self.boundary_graph),
                    repository_root=repository_root,
                    ontology_frame=_dump_json_payload(self.ontology_frame),
                ),
            ),
            (
                self.world_hypothesis_path,
                canonicalize_adeu_architecture_world_hypothesis_payload(
                    _dump_json_payload(self.world_hypothesis),
                    repository_root=repository_root,
                ),
            ),
            (
                self.semantic_ir_path,
                canonicalize_adeu_architecture_semantic_ir_payload(
                    _dump_json_payload(self.semantic_ir),
                    repository_root=repository_root,
                ),
            ),
        ]
        for artifact_path, canonical_payload in comparisons:
            repo_payload = _load_repo_json(artifact_path, repository_root=repository_root)
            if repo_payload != canonical_payload:
                raise ValueError(
                    f"consumed root artifact path does not match canonical payload: {artifact_path}"
                )


class ArchitectureCompilerValidationResult(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    check_results: list[ArchitectureValidationCheckResult]
    blocking_ambiguity_refs: list[str]
    human_escalation_refs: list[str]


def _make_check(
    *,
    check_id: str,
    required: bool,
    passed: bool,
    subject_refs: list[str],
    detail: str,
) -> ArchitectureValidationCheckResult:
    return ArchitectureValidationCheckResult.model_validate(
        {
            "check_id": check_id,
            "required": required,
            "passed": passed,
            "subject_refs": subject_refs,
            "detail": detail,
        }
    )


def _build_consumed_root_refs(
    bundle: ArchitectureCompilerInputBundle,
    *,
    repository_root: Path | None = None,
) -> list[ArchitectureConsumedRootRef]:
    refs = [
        {
            "artifact_schema": bundle.intent_packet.schema,
            "artifact_id": bundle.intent_packet.intent_packet_id,
            "artifact_path": bundle.intent_packet_path,
            "sha256": _sha256_repo_file(bundle.intent_packet_path, repository_root=repository_root),
        },
        {
            "artifact_schema": bundle.ontology_frame.schema,
            "artifact_id": bundle.ontology_frame.ontology_frame_id,
            "artifact_path": bundle.ontology_frame_path,
            "sha256": _sha256_repo_file(
                bundle.ontology_frame_path,
                repository_root=repository_root,
            ),
        },
        {
            "artifact_schema": bundle.boundary_graph.schema,
            "artifact_id": bundle.boundary_graph.boundary_graph_id,
            "artifact_path": bundle.boundary_graph_path,
            "sha256": _sha256_repo_file(
                bundle.boundary_graph_path,
                repository_root=repository_root,
            ),
        },
        {
            "artifact_schema": bundle.world_hypothesis.schema,
            "artifact_id": bundle.world_hypothesis.candidate_id,
            "artifact_path": bundle.world_hypothesis_path,
            "sha256": _sha256_repo_file(
                bundle.world_hypothesis_path,
                repository_root=repository_root,
            ),
        },
        {
            "artifact_schema": bundle.semantic_ir.schema,
            "artifact_id": bundle.semantic_ir.architecture_id,
            "artifact_path": bundle.semantic_ir_path,
            "sha256": _sha256_repo_file(bundle.semantic_ir_path, repository_root=repository_root),
        },
    ]
    refs.sort(key=lambda item: item["artifact_path"])
    return [
        ArchitectureConsumedRootRef.model_validate(
            item,
            context=_validation_context(repository_root),
        )
        for item in refs
    ]


def _build_validation_result(
    bundle: ArchitectureCompilerInputBundle,
) -> ArchitectureCompilerValidationResult:
    semantic_ir = bundle.semantic_ir
    ontology_frame = bundle.ontology_frame
    boundary_graph = bundle.boundary_graph
    world_hypothesis = bundle.world_hypothesis

    boundary_ids = {item.boundary_id for item in ontology_frame.boundaries}
    surface_ids = {item.surface_id for item in ontology_frame.surfaces}
    evidence_ids = {item.evidence_id for item in semantic_ir.epistemics.evidence_requirements}
    hook_ids = {item.hook_id for item in semantic_ir.epistemics.observability_hooks}
    goal_ids = {item.goal_id for item in semantic_ir.utility.goals}
    priority_refs = {
        ref
        for item in semantic_ir.utility.priority_rules
        for ref in (item.higher_ref, item.lower_ref)
    }
    tradeoff_refs = {ref for item in semantic_ir.utility.tradeoffs for ref in item.between_refs}
    ambiguity_ids = {item.ambiguity_id for item in semantic_ir.epistemics.ambiguities}

    blocking_ambiguity_refs = sorted(
        item.ambiguity_id
        for item in semantic_ir.epistemics.ambiguities
        if item.impact_class in {"high", "critical"}
    )
    human_escalation_refs = sorted(
        item.rule_id
        for item in semantic_ir.deontics.escalation_rules
        if item.default_disposition in _HUMAN_ESCALATION_DISPOSITIONS
    )

    checks = [
        _make_check(
            check_id="ASIR-O-001",
            required=True,
            passed=all(
                edge.boundary_ref in boundary_ids
                for edge in boundary_graph.edge_set
                if edge.crossing_class in _CROSSING_CLASSES
            ),
            subject_refs=sorted(edge.edge_id for edge in boundary_graph.edge_set),
            detail="Cross-boundary edges must bind to declared ontology boundaries.",
        ),
        _make_check(
            check_id="ASIR-O-002",
            required=True,
            passed=set(boundary_graph.node_refs).issubset(
                {
                    item.actor_id
                    for item in ontology_frame.actors
                }
                | {item.surface_id for item in ontology_frame.surfaces}
                | {item.object_id for item in ontology_frame.data_objects}
                | {item.boundary_id for item in ontology_frame.boundaries}
                | {item.capability_id for item in ontology_frame.capabilities}
                | {item.workflow_id for item in ontology_frame.workflows}
                | {item.state_id for item in ontology_frame.states}
                | {item.transition_id for item in ontology_frame.transitions}
                | {item.decision_id for item in ontology_frame.decisions}
                | {item.failure_mode_id for item in ontology_frame.failure_modes}
                | {item.step_id for item in ontology_frame.flow_steps}
            ),
            subject_refs=boundary_graph.node_refs,
            detail="Boundary graph nodes must resolve within the consumed ontology frame.",
        ),
        _make_check(
            check_id="ASIR-O-003",
            required=True,
            passed=_extract_ontology_section(ontology_frame)
            == _dump_json_payload(semantic_ir.ontology),
            subject_refs=["ontology_frame", semantic_ir.architecture_id],
            detail=(
                "Semantic IR ontology must exactly match the consumed "
                "ontology companion artifact."
            ),
        ),
        _make_check(
            check_id="ASIR-E-001",
            required=True,
            passed=all(
                set(decision.evidence_required_refs).issubset(evidence_ids)
                for decision in semantic_ir.ontology.decisions
            ),
            subject_refs=sorted(item.decision_id for item in semantic_ir.ontology.decisions),
            detail="Decision evidence requirements must resolve to epistemic evidence ids.",
        ),
        _make_check(
            check_id="ASIR-E-002",
            required=True,
            passed=all(
                not (
                    ambiguity.impact_class in {"high", "critical"}
                    and ambiguity.resolution_route == "deterministic_only"
                )
                for ambiguity in semantic_ir.epistemics.ambiguities
            ),
            subject_refs=sorted(ambiguity_ids) or [semantic_ir.architecture_id],
            detail="High-impact ambiguities may not claim deterministic-only resolution in V40-B.",
        ),
        _make_check(
            check_id="ASIR-E-003",
            required=True,
            passed=(
                world_hypothesis.candidate_id
                == semantic_ir.variant_lineage.accepted_candidate_id
            ),
            subject_refs=[world_hypothesis.candidate_id],
            detail=(
                "Consumed world hypothesis must align to the accepted "
                "semantic-root candidate lineage."
            ),
        ),
        _make_check(
            check_id="ASIR-D-001",
            required=True,
            passed=all(
                decision.authority_source_ref in surface_ids
                for decision in semantic_ir.ontology.decisions
            ),
            subject_refs=sorted(item.decision_id for item in semantic_ir.ontology.decisions),
            detail="Authoritative decisions must name a consumed authoritative source surface.",
        ),
        _make_check(
            check_id="ASIR-D-002",
            required=True,
            passed=all(
                any(
                    gate.subject_ref == decision.decision_id
                    and gate.authority_source_ref == decision.authority_source_ref
                    and gate.fail_closed
                    and set(decision.evidence_required_refs).issubset(set(gate.required_refs))
                    for gate in semantic_ir.deontics.gates
                )
                for decision in semantic_ir.ontology.decisions
            ),
            subject_refs=sorted(item.decision_id for item in semantic_ir.ontology.decisions),
            detail=(
                "Each decision must have a fail-closed gate covering "
                "required evidence before commit."
            ),
        ),
        _make_check(
            check_id="ASIR-U-001",
            required=True,
            passed=all(
                metric.measured_by_refs
                and set(metric.measured_by_refs).issubset(evidence_ids | hook_ids)
                for metric in semantic_ir.utility.metrics
            ),
            subject_refs=sorted(item.metric_id for item in semantic_ir.utility.metrics),
            detail=(
                "Utility metrics must remain measurable from evidence "
                "requirements or observability hooks."
            ),
        ),
        _make_check(
            check_id="ASIR-U-002",
            required=False,
            passed=all(goal_id in priority_refs | tradeoff_refs for goal_id in goal_ids),
            subject_refs=sorted(goal_ids) or [semantic_ir.architecture_id],
            detail="Utility goals should participate in an explicit priority or tradeoff relation.",
        ),
        _make_check(
            check_id="ASIR-P-001",
            required=True,
            passed=not blocking_ambiguity_refs,
            subject_refs=blocking_ambiguity_refs or [semantic_ir.architecture_id],
            detail=(
                "No unresolved high- or critical-impact ambiguity may "
                "survive pre-projection readiness."
            ),
        ),
        _make_check(
            check_id="ASIR-P-002",
            required=True,
            passed=not human_escalation_refs,
            subject_refs=human_escalation_refs or [semantic_ir.architecture_id],
            detail=(
                "Static human escalation lineage must remain empty before "
                "the hybrid lane is released."
            ),
        ),
        _make_check(
            check_id="ASIR-P-003",
            required=True,
            passed=True,
            subject_refs=[semantic_ir.architecture_id],
            detail=(
                "V40-B conformance reports must keep emitted_artifact_refs "
                "structurally present but empty."
            ),
        ),
    ]
    checks.sort(key=lambda item: item.check_id)
    return ArchitectureCompilerValidationResult.model_validate(
        {
            "check_results": [_dump_json_payload(item) for item in checks],
            "blocking_ambiguity_refs": blocking_ambiguity_refs,
            "human_escalation_refs": human_escalation_refs,
        }
    )


def canonicalize_adeu_architecture_conformance_report_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = AdeuArchitectureConformanceReport.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return _dump_json_payload(model)


def derive_v40b_conformance_report(
    *,
    intent_packet_payload: dict[str, Any],
    intent_packet_path: str,
    ontology_frame_payload: dict[str, Any],
    ontology_frame_path: str,
    boundary_graph_payload: dict[str, Any],
    boundary_graph_path: str,
    world_hypothesis_payload: dict[str, Any],
    world_hypothesis_path: str,
    semantic_ir_payload: dict[str, Any],
    semantic_ir_path: str,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    context = _validation_context(repository_root)
    intent_packet = ArchitectureIntentPacket.model_validate(intent_packet_payload, context=context)
    ontology_frame = ArchitectureOntologyFrame.model_validate(
        ontology_frame_payload,
        context=context,
    )
    boundary_graph = ArchitectureBoundaryGraph.model_validate(
        boundary_graph_payload,
        context={**context, "ontology_frame": ontology_frame_payload},
    )
    world_hypothesis = ArchitectureWorldHypothesis.model_validate(
        world_hypothesis_payload,
        context=context,
    )
    semantic_ir = AdeuArchitectureSemanticIR.model_validate(semantic_ir_payload, context=context)

    bundle = ArchitectureCompilerInputBundle.model_validate(
        {
            "intent_packet_path": intent_packet_path,
            "intent_packet": _dump_json_payload(intent_packet),
            "ontology_frame_path": ontology_frame_path,
            "ontology_frame": _dump_json_payload(ontology_frame),
            "boundary_graph_path": boundary_graph_path,
            "boundary_graph": _dump_json_payload(boundary_graph),
            "world_hypothesis_path": world_hypothesis_path,
            "world_hypothesis": _dump_json_payload(world_hypothesis),
            "semantic_ir_path": semantic_ir_path,
            "semantic_ir": _dump_json_payload(semantic_ir),
        },
        context=context,
    )
    validation = _build_validation_result(bundle)
    failed_check_ids = sorted(
        result.check_id
        for result in validation.check_results
        if result.required and not result.passed
    )
    report = {
        "schema": ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA,
        "architecture_id": bundle.semantic_ir.architecture_id,
        "semantic_hash": bundle.semantic_ir.semantic_hash,
        "compiler": _dump_json_payload(ArchitectureCompilerProvenance()),
        "consumed_root_refs": [
            _dump_json_payload(ref)
            for ref in _build_consumed_root_refs(bundle, repository_root=repository_root)
        ],
        "projection_readiness": (
            "blocked"
            if (
                validation.blocking_ambiguity_refs
                or validation.human_escalation_refs
                or failed_check_ids
            )
            else "ready"
        ),
        "blocking_ambiguity_refs": validation.blocking_ambiguity_refs,
        "failed_check_ids": failed_check_ids,
        "human_escalation_refs": validation.human_escalation_refs,
        "emitted_artifact_refs": [],
        "check_results": [_dump_json_payload(result) for result in validation.check_results],
    }
    return canonicalize_adeu_architecture_conformance_report_payload(
        report,
        repository_root=repository_root,
    )
