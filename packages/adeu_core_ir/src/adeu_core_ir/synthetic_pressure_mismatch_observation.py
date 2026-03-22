from __future__ import annotations

import ast
import hashlib
import json
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
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

SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_PACKET_SCHEMA = (
    "synthetic_pressure_mismatch_observation_packet@1"
)
SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA = (
    "synthetic_pressure_mismatch_conformance_report@1"
)
V39C_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md"
    "#v39c_synthetic_pressure_mismatch_observation_contract@1"
)
V39C_SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_EVALUATOR_ID = (
    "adeu_core_ir.synthetic_pressure_mismatch_observation"
    ".derive_v39c_observation_packet@1"
)
V39C_SYNTHETIC_PRESSURE_MISMATCH_REPORT_EVALUATOR_ID = (
    "adeu_core_ir.synthetic_pressure_mismatch_observation"
    ".derive_v39c_conformance_report@1"
)
V39C_IMPOSSIBLE_NULL_CHECK_DETECTOR_ID = (
    "adeu_core_ir.synthetic_pressure_mismatch_observation"
    ".detect_impossible_null_guard@1"
)
DEFAULT_V39C_REGISTRY_REFERENCE_FIXTURE_PATH = (
    "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/"
    "synthetic_pressure_mismatch_rule_registry_v73_reference.json"
)

SyntheticPressureMismatchObservationPacketSchemaVersion = Literal[
    "synthetic_pressure_mismatch_observation_packet@1"
]
SyntheticPressureMismatchConformanceReportSchemaVersion = Literal[
    "synthetic_pressure_mismatch_conformance_report@1"
]
SyntheticPressureMismatchObservationOverallPosture = Literal[
    "deterministic_high_severity_findings_present",
    "mixed_findings",
    "no_findings",
    "review_only_or_meta_findings_present",
    "safe_autofix_candidates_present",
]
_SUPPORTED_SUBJECT_LANGUAGE = Literal["python"]


def _assert_sorted_unique(
    values: list[str],
    *,
    field_name: str,
    allow_empty: bool = False,
) -> None:
    if not allow_empty and not values:
        raise ValueError(f"{field_name} must not be empty")
    if any(not value for value in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _assert_non_empty_text(value: str, *, field_name: str) -> None:
    if not value.strip():
        raise ValueError(f"{field_name} must not be empty")


def _validation_context(repository_root: Path | None) -> dict[str, Path] | None:
    if repository_root is None:
        return None
    return {"repository_root": repository_root}


def _default_repository_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _resolve_repository_root(info: ValidationInfo | None = None) -> Path:
    if info is not None and isinstance(info.context, dict):
        repository_root = info.context.get("repository_root")
        if isinstance(repository_root, Path):
            return repository_root
    return _default_repository_root()


def _normalize_repo_relative_path(value: str, *, field_name: str) -> str:
    normalized = value.strip().replace("\\", "/")
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    if normalized.startswith("/") or normalized.startswith("../") or "/../" in normalized:
        raise ValueError(f"{field_name} must be repository-relative")
    return normalized


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_text(value: str) -> str:
    return _sha256_bytes(value.encode("utf-8"))


def _sha256_repo_file(
    path_text: str,
    *,
    field_name: str,
    repository_root: Path | None = None,
) -> str:
    normalized = _normalize_repo_relative_path(path_text, field_name=field_name)
    path = (repository_root or _default_repository_root()) / normalized
    if not path.is_file():
        raise ValueError(f"{field_name} must resolve to an existing repo file")
    return _sha256_bytes(path.read_bytes())


def _canonical_json_hash(payload: dict[str, Any]) -> str:
    return hashlib.sha256(
        json.dumps(
            payload,
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        ).encode("utf-8")
    ).hexdigest()


def _load_repo_json_object(
    path_text: str,
    *,
    field_name: str,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    normalized = _normalize_repo_relative_path(path_text, field_name=field_name)
    path = (repository_root or _default_repository_root()) / normalized
    if not path.is_file():
        raise ValueError(f"{field_name} must resolve to an existing repo file")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"{field_name} must contain a JSON object") from exc
    if not isinstance(payload, dict):
        raise ValueError(f"{field_name} must contain a JSON object")
    return payload


class SyntheticPressureMismatchLocalSubjectFixture(BaseModel):
    model_config = ConfigDict(extra="forbid")

    subject_id: str = Field(min_length=1)
    subject_kind: SyntheticPressureMismatchSubjectKind
    language: _SUPPORTED_SUBJECT_LANGUAGE = "python"
    content: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchLocalSubjectFixture":
        _assert_non_empty_text(self.subject_id, field_name="subject_id")
        _assert_non_empty_text(self.content, field_name="content")
        return self


class SyntheticPressureMismatchDetectorProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid")

    detector_id: str = Field(min_length=1)
    detector_version: Literal["1"] = "1"

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchDetectorProvenance":
        _assert_non_empty_text(self.detector_id, field_name="detector_provenance.detector_id")
        return self


class SyntheticPressureMismatchObservationFinding(BaseModel):
    model_config = ConfigDict(extra="forbid")

    rule_id: str = Field(min_length=1)
    signal_kind: SyntheticPressureMismatchSignalKind
    harm_kind: SyntheticPressureMismatchHarmKind
    evidence_regime: SyntheticPressureMismatchEvidenceRegime
    allowed_action: SyntheticPressureMismatchAllowedAction
    resolution_route: SyntheticPressureMismatchResolutionRoute
    local_observation_locator: str = Field(min_length=1)
    detector_provenance: SyntheticPressureMismatchDetectorProvenance

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchObservationFinding":
        _assert_non_empty_text(self.rule_id, field_name="findings[].rule_id")
        _assert_non_empty_text(
            self.local_observation_locator,
            field_name=f"findings[{self.rule_id}].local_observation_locator",
        )
        return self


class SyntheticPressureMismatchObservationDerivationMetadata(BaseModel):
    model_config = ConfigDict(extra="forbid")

    evaluator_id: Literal[
        "adeu_core_ir.synthetic_pressure_mismatch_observation"
        ".derive_v39c_observation_packet@1"
    ] = V39C_SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_EVALUATOR_ID
    evaluator_version: Literal["1"] = "1"
    registry_reference_fixture_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    executed_rule_ids: list[str] = Field(default_factory=list)
    canonical_local_subject_only: Literal[True] = True
    deterministic_local_execution_only: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(
        self,
    ) -> "SyntheticPressureMismatchObservationDerivationMetadata":
        _assert_sorted_unique(
            self.executed_rule_ids,
            field_name="derivation_metadata.executed_rule_ids",
            allow_empty=True,
        )
        return self


class SyntheticPressureMismatchObservationPacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: SyntheticPressureMismatchObservationPacketSchemaVersion = (
        SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_PACKET_SCHEMA
    )
    target_arc: Literal["vNext+74"] = "vNext+74"
    target_path: Literal["V39-C"] = "V39-C"
    contract_source: Literal[
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md"
        "#v39c_synthetic_pressure_mismatch_observation_contract@1"
    ] = V39C_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE
    observation_packet_id: str = Field(min_length=1)
    registry_schema: Literal["synthetic_pressure_mismatch_rule_registry@1"] = (
        SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA
    )
    registry_id: str = Field(min_length=1)
    registry_reference_fixture: str = Field(min_length=1)
    subject_kind: SyntheticPressureMismatchSubjectKind
    subject_ref: str = Field(min_length=1)
    subject_content_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    findings: list[SyntheticPressureMismatchObservationFinding] = Field(default_factory=list)
    derivation_metadata: SyntheticPressureMismatchObservationDerivationMetadata

    @model_validator(mode="after")
    def _validate_contract(
        self,
        info: ValidationInfo,
    ) -> "SyntheticPressureMismatchObservationPacket":
        repository_root = _resolve_repository_root(info)
        _assert_non_empty_text(
            self.observation_packet_id,
            field_name="observation_packet_id",
        )
        _assert_non_empty_text(self.registry_id, field_name="registry_id")
        self.registry_reference_fixture = _normalize_repo_relative_path(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
        )
        self.subject_ref = _normalize_repo_relative_path(
            self.subject_ref,
            field_name="subject_ref",
        )
        registry_payload = _load_repo_json_object(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
            repository_root=repository_root,
        )
        registry = SyntheticPressureMismatchRuleRegistry.model_validate(
            canonicalize_synthetic_pressure_mismatch_rule_registry_payload(registry_payload),
            context=_validation_context(repository_root),
        )
        if registry.registry_id != self.registry_id:
            raise ValueError("registry_id must match the referenced released registry fixture")
        if self.derivation_metadata.registry_reference_fixture_sha256 != _sha256_repo_file(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
            repository_root=repository_root,
        ):
            raise ValueError(
                "derivation_metadata.registry_reference_fixture_sha256 must match "
                "registry_reference_fixture bytes"
            )
        subject_payload = _load_repo_json_object(
            self.subject_ref,
            field_name="subject_ref",
            repository_root=repository_root,
        )
        subject = SyntheticPressureMismatchLocalSubjectFixture.model_validate(subject_payload)
        if subject.subject_kind != self.subject_kind:
            raise ValueError("subject_kind must match the referenced subject fixture")
        if _sha256_text(subject.content) != self.subject_content_sha256:
            raise ValueError("subject_content_sha256 must match subject fixture content bytes")
        executed_rule_ids = list(self.derivation_metadata.executed_rule_ids)
        for rule_id in executed_rule_ids:
            if rule_id not in {rule.rule_id for rule in registry.rules}:
                raise ValueError(
                    "derivation_metadata.executed_rule_ids must reference registry rules"
                )
        rule_index = {rule.rule_id: rule for rule in registry.rules}
        finding_identities: list[str] = []
        for finding in self.findings:
            try:
                rule = rule_index[finding.rule_id]
            except KeyError as exc:
                raise ValueError(
                    "findings[].rule_id must reference a released registry rule"
                ) from exc
            if rule.evidence_regime != "deterministic_local":
                raise ValueError(
                    "findings[].rule_id must reference deterministic_local rules only in V39-C"
                )
            if self.subject_kind not in rule.applicable_subject_kinds:
                raise ValueError(
                    "findings[].rule_id must be applicable to the packet subject_kind"
                )
            if finding.signal_kind != rule.signal_kind:
                raise ValueError("findings[].signal_kind must match the referenced registry rule")
            if finding.harm_kind != rule.harm_kind:
                raise ValueError("findings[].harm_kind must match the referenced registry rule")
            if finding.evidence_regime != rule.evidence_regime:
                raise ValueError(
                    "findings[].evidence_regime must match the referenced registry rule"
                )
            if finding.allowed_action != rule.allowed_action:
                raise ValueError(
                    "findings[].allowed_action must match the referenced registry rule"
                )
            if finding.resolution_route != rule.resolution_route:
                raise ValueError(
                    "findings[].resolution_route must match the referenced registry rule"
                )
            finding_identities.append(
                f"{finding.rule_id}::{finding.local_observation_locator}"
            )
        _assert_sorted_unique(
            finding_identities,
            field_name="findings.identity",
            allow_empty=True,
        )
        return self


class SyntheticPressureMismatchFindingCountByEvidenceRegime(BaseModel):
    model_config = ConfigDict(extra="forbid")

    evidence_regime: SyntheticPressureMismatchEvidenceRegime
    finding_count: int = Field(ge=1)


class SyntheticPressureMismatchFindingCountByAllowedAction(BaseModel):
    model_config = ConfigDict(extra="forbid")

    allowed_action: SyntheticPressureMismatchAllowedAction
    finding_count: int = Field(ge=1)


class SyntheticPressureMismatchFindingRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    observation_packet_id: str = Field(min_length=1)
    rule_id: str = Field(min_length=1)
    local_observation_locator: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchFindingRef":
        _assert_non_empty_text(
            self.observation_packet_id,
            field_name="finding_ref.observation_packet_id",
        )
        _assert_non_empty_text(self.rule_id, field_name="finding_ref.rule_id")
        _assert_non_empty_text(
            self.local_observation_locator,
            field_name="finding_ref.local_observation_locator",
        )
        return self


class SyntheticPressureMismatchConformanceDerivationMetadata(BaseModel):
    model_config = ConfigDict(extra="forbid")

    evaluator_id: Literal[
        "adeu_core_ir.synthetic_pressure_mismatch_observation"
        ".derive_v39c_conformance_report@1"
    ] = V39C_SYNTHETIC_PRESSURE_MISMATCH_REPORT_EVALUATOR_ID
    evaluator_version: Literal["1"] = "1"
    observation_packet_hashes: list[str] = Field(min_length=1)
    registry_reference_fixture_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    canonical_local_subject_only: Literal[True] = True
    count_based_aggregation_only: Literal[True] = True
    weighted_rollup_forbidden: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(
        self,
    ) -> "SyntheticPressureMismatchConformanceDerivationMetadata":
        _assert_sorted_unique(
            self.observation_packet_hashes,
            field_name="derivation_metadata.observation_packet_hashes",
            allow_empty=False,
        )
        return self


class SyntheticPressureMismatchConformanceReport(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: SyntheticPressureMismatchConformanceReportSchemaVersion = (
        SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA
    )
    target_arc: Literal["vNext+74"] = "vNext+74"
    target_path: Literal["V39-C"] = "V39-C"
    contract_source: Literal[
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md"
        "#v39c_synthetic_pressure_mismatch_observation_contract@1"
    ] = V39C_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE
    report_id: str = Field(min_length=1)
    registry_schema: Literal["synthetic_pressure_mismatch_rule_registry@1"] = (
        SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA
    )
    registry_id: str = Field(min_length=1)
    registry_reference_fixture: str = Field(min_length=1)
    aggregated_observation_packet_ids: list[str] = Field(min_length=1)
    aggregated_observation_packet_hashes: list[str] = Field(min_length=1)
    aggregated_subject_refs: list[str] = Field(min_length=1)
    observation_count: int = Field(ge=1)
    finding_count: int = Field(ge=0)
    findings_by_evidence_regime: list[SyntheticPressureMismatchFindingCountByEvidenceRegime] = (
        Field(default_factory=list)
    )
    findings_by_allowed_action: list[SyntheticPressureMismatchFindingCountByAllowedAction] = Field(
        default_factory=list
    )
    safe_autofix_candidates: list[SyntheticPressureMismatchFindingRef] = Field(
        default_factory=list
    )
    deterministic_high_severity_findings: list[SyntheticPressureMismatchFindingRef] = Field(
        default_factory=list
    )
    review_only_findings: list[SyntheticPressureMismatchFindingRef] = Field(default_factory=list)
    meta_governance_findings: list[SyntheticPressureMismatchFindingRef] = Field(
        default_factory=list
    )
    overall_pressure_mismatch_posture: SyntheticPressureMismatchObservationOverallPosture
    derivation_metadata: SyntheticPressureMismatchConformanceDerivationMetadata

    @model_validator(mode="after")
    def _validate_contract(
        self,
        info: ValidationInfo,
    ) -> "SyntheticPressureMismatchConformanceReport":
        repository_root = _resolve_repository_root(info)
        _assert_non_empty_text(self.report_id, field_name="report_id")
        _assert_non_empty_text(self.registry_id, field_name="registry_id")
        self.registry_reference_fixture = _normalize_repo_relative_path(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
        )
        registry_payload = _load_repo_json_object(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
            repository_root=repository_root,
        )
        registry = SyntheticPressureMismatchRuleRegistry.model_validate(
            canonicalize_synthetic_pressure_mismatch_rule_registry_payload(registry_payload),
            context=_validation_context(repository_root),
        )
        if registry.registry_id != self.registry_id:
            raise ValueError("registry_id must match the referenced released registry fixture")
        if self.derivation_metadata.registry_reference_fixture_sha256 != _sha256_repo_file(
            self.registry_reference_fixture,
            field_name="registry_reference_fixture",
            repository_root=repository_root,
        ):
            raise ValueError(
                "derivation_metadata.registry_reference_fixture_sha256 must match "
                "registry_reference_fixture bytes"
            )
        _assert_sorted_unique(
            self.aggregated_observation_packet_ids,
            field_name="aggregated_observation_packet_ids",
            allow_empty=False,
        )
        _assert_sorted_unique(
            self.aggregated_observation_packet_hashes,
            field_name="aggregated_observation_packet_hashes",
            allow_empty=False,
        )
        _assert_sorted_unique(
            self.aggregated_subject_refs,
            field_name="aggregated_subject_refs",
            allow_empty=False,
        )
        aggregated_packet_ids = set(self.aggregated_observation_packet_ids)
        if len(self.aggregated_observation_packet_ids) != self.observation_count:
            raise ValueError("observation_count must match aggregated_observation_packet_ids")
        if len(self.aggregated_observation_packet_hashes) != self.observation_count:
            raise ValueError("observation_count must match aggregated_observation_packet_hashes")
        if len(self.aggregated_subject_refs) != self.observation_count:
            raise ValueError("observation_count must match aggregated_subject_refs")
        if (
            self.derivation_metadata.observation_packet_hashes
            != self.aggregated_observation_packet_hashes
        ):
            raise ValueError(
                "derivation_metadata.observation_packet_hashes must match the aggregated packet set"
            )
        regime_total = sum(entry.finding_count for entry in self.findings_by_evidence_regime)
        action_total = sum(entry.finding_count for entry in self.findings_by_allowed_action)
        if regime_total != self.finding_count:
            raise ValueError("findings_by_evidence_regime counts must sum to finding_count")
        if action_total != self.finding_count:
            raise ValueError("findings_by_allowed_action counts must sum to finding_count")
        category_keys: dict[str, set[str]] = {}
        for field_name, refs in (
            ("safe_autofix_candidates", self.safe_autofix_candidates),
            (
                "deterministic_high_severity_findings",
                self.deterministic_high_severity_findings,
            ),
            ("review_only_findings", self.review_only_findings),
            ("meta_governance_findings", self.meta_governance_findings),
        ):
            keys = [
                f"{ref.observation_packet_id}::{ref.rule_id}::{ref.local_observation_locator}"
                for ref in refs
            ]
            for ref in refs:
                if ref.observation_packet_id not in aggregated_packet_ids:
                    raise ValueError(
                        f"{field_name}.observation_packet_id must belong to "
                        "aggregated_observation_packet_ids"
                    )
            _assert_sorted_unique(keys, field_name=field_name, allow_empty=True)
            category_keys[field_name] = set(keys)
        for left_name, left_keys in category_keys.items():
            for right_name, right_keys in category_keys.items():
                if left_name >= right_name:
                    continue
                if left_keys & right_keys:
                    raise ValueError(
                        f"{left_name} and {right_name} must remain disjoint"
                    )
        categorized_count = sum(len(keys) for keys in category_keys.values())
        if categorized_count != self.finding_count:
            raise ValueError("finding categories must account for every aggregated finding")
        if self.finding_count == 0 and self.overall_pressure_mismatch_posture != "no_findings":
            raise ValueError(
                "overall_pressure_mismatch_posture must be no_findings when finding_count is zero"
            )
        if self.finding_count > 0 and self.overall_pressure_mismatch_posture == "no_findings":
            raise ValueError(
                "overall_pressure_mismatch_posture cannot be no_findings when findings exist"
            )
        return self


def _load_validated_registry(
    registry_reference_fixture_path: str,
    *,
    repository_root: Path | None = None,
) -> tuple[dict[str, Any], SyntheticPressureMismatchRuleRegistry]:
    payload = _load_repo_json_object(
        registry_reference_fixture_path,
        field_name="registry_reference_fixture_path",
        repository_root=repository_root,
    )
    canonical_payload = canonicalize_synthetic_pressure_mismatch_rule_registry_payload(payload)
    registry = SyntheticPressureMismatchRuleRegistry.model_validate(
        canonical_payload,
        context=_validation_context(repository_root),
    )
    return canonical_payload, registry


def _load_subject_fixture(
    subject_ref: str,
    *,
    repository_root: Path | None = None,
) -> tuple[dict[str, Any], SyntheticPressureMismatchLocalSubjectFixture]:
    payload = _load_repo_json_object(
        subject_ref,
        field_name="subject_ref",
        repository_root=repository_root,
    )
    subject = SyntheticPressureMismatchLocalSubjectFixture.model_validate(payload)
    return payload, subject


def _annotation_allows_none(annotation: ast.expr | None) -> bool:
    if annotation is None:
        return True
    if isinstance(annotation, ast.Constant):
        return annotation.value is None
    if isinstance(annotation, ast.Name):
        return annotation.id in {"Any", "None", "Optional"}
    if isinstance(annotation, ast.Attribute):
        return annotation.attr in {"Any", "None", "Optional"}
    if isinstance(annotation, ast.BinOp) and isinstance(annotation.op, ast.BitOr):
        return _annotation_allows_none(annotation.left) or _annotation_allows_none(annotation.right)
    if isinstance(annotation, ast.Tuple):
        return any(_annotation_allows_none(element) for element in annotation.elts)
    if isinstance(annotation, ast.Subscript):
        base_name = _annotation_name(annotation.value)
        if base_name.endswith("Optional"):
            return True
        if base_name.endswith("Union") or base_name.endswith("Literal"):
            return any(
                _annotation_allows_none(element)
                for element in _slice_elements(annotation.slice)
            )
    return False


def _annotation_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return f"{_annotation_name(node.value)}.{node.attr}"
    return ""


def _slice_elements(slice_node: ast.expr) -> list[ast.expr]:
    if isinstance(slice_node, ast.Tuple):
        return list(slice_node.elts)
    return [slice_node]


def _default_allows_none(default_node: ast.expr | None) -> bool:
    return isinstance(default_node, ast.Constant) and default_node.value is None


def _extract_null_guard_name(test: ast.expr) -> str | None:
    if not isinstance(test, ast.Compare):
        return None
    if len(test.ops) != 1 or len(test.comparators) != 1:
        return None
    left = test.left
    right = test.comparators[0]
    operator = test.ops[0]
    if not isinstance(operator, (ast.Is, ast.Eq)):
        return None
    if isinstance(left, ast.Name) and isinstance(right, ast.Constant) and right.value is None:
        return left.id
    if isinstance(right, ast.Name) and isinstance(left, ast.Constant) and left.value is None:
        return right.id
    return None


def _function_argument_defaults(
    function_node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> dict[str, ast.expr | None]:
    positional_args = list(function_node.args.posonlyargs) + list(function_node.args.args)
    positional_defaults = [None] * (len(positional_args) - len(function_node.args.defaults))
    positional_defaults.extend(function_node.args.defaults)
    kwonly_defaults = list(function_node.args.kw_defaults)
    defaults: dict[str, ast.expr | None] = {}
    for argument, default in zip(positional_args, positional_defaults, strict=True):
        defaults[argument.arg] = default
    for argument, default in zip(function_node.args.kwonlyargs, kwonly_defaults, strict=True):
        defaults[argument.arg] = default
    return defaults


def _detect_impossible_null_guard(
    *,
    subject: SyntheticPressureMismatchLocalSubjectFixture,
    rule: SyntheticPressureMismatchRule,
) -> list[dict[str, Any]]:
    if subject.language != "python":
        raise ValueError("V39-C deterministic detection currently supports python subjects only")
    try:
        tree = ast.parse(subject.content)
    except SyntaxError as exc:
        raise ValueError("subject fixture content must parse as valid python") from exc

    findings: list[dict[str, Any]] = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        defaults = _function_argument_defaults(node)
        annotations = {
            argument.arg: argument.annotation
            for argument in (
                list(node.args.posonlyargs)
                + list(node.args.args)
                + list(node.args.kwonlyargs)
            )
        }
        for child in ast.walk(node):
            if not isinstance(child, ast.If):
                continue
            candidate_name = _extract_null_guard_name(child.test)
            if candidate_name is None:
                continue
            if candidate_name not in annotations:
                continue
            if _annotation_allows_none(annotations[candidate_name]):
                continue
            if _default_allows_none(defaults.get(candidate_name)):
                continue
            findings.append(
                {
                    "rule_id": rule.rule_id,
                    "signal_kind": rule.signal_kind,
                    "harm_kind": rule.harm_kind,
                    "evidence_regime": rule.evidence_regime,
                    "allowed_action": rule.allowed_action,
                    "resolution_route": rule.resolution_route,
                    "local_observation_locator": (
                        f"function:{node.name}:line:{child.lineno}:symbol:{candidate_name}"
                    ),
                    "detector_provenance": {
                        "detector_id": V39C_IMPOSSIBLE_NULL_CHECK_DETECTOR_ID,
                    },
                }
            )
    findings.sort(key=lambda entry: (entry["rule_id"], entry["local_observation_locator"]))
    return findings


_DETECTORS_BY_RULE_ID = {
    "state_model_impossible_null_check": _detect_impossible_null_guard,
}
_SUPPORTED_SUBJECT_KINDS_BY_RULE_ID = {
    "state_model_impossible_null_check": frozenset({"function_or_method"}),
}


def _detector_for_rule(rule: SyntheticPressureMismatchRule) -> Any:
    detector = _DETECTORS_BY_RULE_ID.get(rule.rule_id)
    if detector is None:
        raise ValueError(
            f"no deterministic detector is implemented for released rule_id {rule.rule_id}"
        )
    return detector


def _assert_subject_kind_supported_by_detector(
    *,
    rule: SyntheticPressureMismatchRule,
    subject: SyntheticPressureMismatchLocalSubjectFixture,
) -> None:
    supported_subject_kinds = _SUPPORTED_SUBJECT_KINDS_BY_RULE_ID.get(rule.rule_id)
    if supported_subject_kinds is None:
        raise ValueError(
            f"no subject-kind support map is defined for released rule_id {rule.rule_id}"
        )
    if subject.subject_kind not in supported_subject_kinds:
        raise ValueError(
            "V39-C deterministic detector for released rule_id "
            f"{rule.rule_id} does not support subject_kind {subject.subject_kind}"
        )


def _derive_multi_packet_report_id(*, packet_hashes: list[str]) -> str:
    digest = hashlib.sha256(
        json.dumps(
            packet_hashes,
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=False,
        ).encode("utf-8")
    ).hexdigest()[:16]
    return f"v39c_v74_report_{digest}"


def canonicalize_synthetic_pressure_mismatch_observation_packet_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = SyntheticPressureMismatchObservationPacket.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_synthetic_pressure_mismatch_conformance_report_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    model = SyntheticPressureMismatchConformanceReport.model_validate(
        deepcopy(payload),
        context=_validation_context(repository_root),
    )
    return model.model_dump(mode="json", exclude_none=True)


def derive_v39c_observation_packet(
    subject_ref: str,
    *,
    registry_reference_fixture_path: str = DEFAULT_V39C_REGISTRY_REFERENCE_FIXTURE_PATH,
    requested_rule_ids: list[str] | None = None,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchObservationPacket:
    _canonical_registry_payload, registry = _load_validated_registry(
        registry_reference_fixture_path,
        repository_root=repository_root,
    )
    normalized_subject_ref = _normalize_repo_relative_path(subject_ref, field_name="subject_ref")
    _subject_payload, subject = _load_subject_fixture(
        normalized_subject_ref,
        repository_root=repository_root,
    )
    rules_by_id = {rule.rule_id: rule for rule in registry.rules}
    if requested_rule_ids is not None:
        requested_rule_ids = list(requested_rule_ids)
        _assert_sorted_unique(
            requested_rule_ids,
            field_name="requested_rule_ids",
            allow_empty=False,
        )
        candidate_rules: list[SyntheticPressureMismatchRule] = []
        for rule_id in requested_rule_ids:
            try:
                rule = rules_by_id[rule_id]
            except KeyError as exc:
                raise ValueError(
                    "requested_rule_ids must reference released registry rules"
                ) from exc
            if rule.evidence_regime != "deterministic_local":
                raise ValueError(
                    "requested_rule_ids may execute deterministic_local rules only in V39-C"
                )
            if subject.subject_kind not in rule.applicable_subject_kinds:
                raise ValueError(
                    "requested_rule_ids must be applicable to the subject fixture kind"
                )
            _detector_for_rule(rule)
            _assert_subject_kind_supported_by_detector(rule=rule, subject=subject)
            candidate_rules.append(rule)
    else:
        candidate_rules = []
        for rule in registry.rules:
            if rule.evidence_regime != "deterministic_local":
                continue
            if subject.subject_kind not in rule.applicable_subject_kinds:
                continue
            _detector_for_rule(rule)
            _assert_subject_kind_supported_by_detector(rule=rule, subject=subject)
            candidate_rules.append(rule)

    findings: list[dict[str, Any]] = []
    executed_rule_ids: list[str] = []
    for rule in sorted(candidate_rules, key=lambda entry: entry.rule_id):
        detector = _detector_for_rule(rule)
        findings.extend(detector(subject=subject, rule=rule))
        executed_rule_ids.append(rule.rule_id)
    findings.sort(key=lambda entry: (entry["rule_id"], entry["local_observation_locator"]))
    packet_payload = {
        "observation_packet_id": f"v39c_v74_obs_{subject.subject_id}",
        "registry_id": registry.registry_id,
        "registry_reference_fixture": _normalize_repo_relative_path(
            registry_reference_fixture_path,
            field_name="registry_reference_fixture_path",
        ),
        "subject_kind": subject.subject_kind,
        "subject_ref": normalized_subject_ref,
        "subject_content_sha256": _sha256_text(subject.content),
        "findings": findings,
        "derivation_metadata": {
            "registry_reference_fixture_sha256": _sha256_repo_file(
                registry_reference_fixture_path,
                field_name="registry_reference_fixture_path",
                repository_root=repository_root,
            ),
            "executed_rule_ids": executed_rule_ids,
        },
    }
    return SyntheticPressureMismatchObservationPacket.model_validate(
        packet_payload,
        context=_validation_context(repository_root),
    )


def _finding_ref_from_packet(
    packet: SyntheticPressureMismatchObservationPacket,
    finding: SyntheticPressureMismatchObservationFinding,
) -> dict[str, str]:
    return {
        "observation_packet_id": packet.observation_packet_id,
        "rule_id": finding.rule_id,
        "local_observation_locator": finding.local_observation_locator,
    }


def _derive_overall_posture(
    *,
    safe_autofix_candidates: list[dict[str, str]],
    deterministic_high_severity_findings: list[dict[str, str]],
    review_only_findings: list[dict[str, str]],
    meta_governance_findings: list[dict[str, str]],
) -> SyntheticPressureMismatchObservationOverallPosture:
    total = (
        len(safe_autofix_candidates)
        + len(deterministic_high_severity_findings)
        + len(review_only_findings)
        + len(meta_governance_findings)
    )
    if total == 0:
        return "no_findings"
    present = sum(
        bool(bucket)
        for bucket in (
            safe_autofix_candidates,
            deterministic_high_severity_findings,
            review_only_findings,
            meta_governance_findings,
        )
    )
    if present > 1:
        return "mixed_findings"
    if safe_autofix_candidates:
        return "safe_autofix_candidates_present"
    if deterministic_high_severity_findings:
        return "deterministic_high_severity_findings_present"
    return "review_only_or_meta_findings_present"


def derive_v39c_conformance_report(
    payloads: list[dict[str, Any] | SyntheticPressureMismatchObservationPacket],
    *,
    repository_root: Path | None = None,
) -> SyntheticPressureMismatchConformanceReport:
    if not payloads:
        raise ValueError("payloads must contain at least one observation packet")
    packets: list[SyntheticPressureMismatchObservationPacket] = []
    packet_hashes: list[str] = []
    for payload in payloads:
        raw_payload = (
            payload.model_dump(mode="json", exclude_none=True)
            if isinstance(payload, SyntheticPressureMismatchObservationPacket)
            else deepcopy(payload)
        )
        canonical_payload = canonicalize_synthetic_pressure_mismatch_observation_packet_payload(
            raw_payload,
            repository_root=repository_root,
        )
        packets.append(
            SyntheticPressureMismatchObservationPacket.model_validate(
                canonical_payload,
                context=_validation_context(repository_root),
            )
        )
        packet_hashes.append(_canonical_json_hash(canonical_payload))

    registry_reference_fixture = packets[0].registry_reference_fixture
    registry_id = packets[0].registry_id
    for packet in packets[1:]:
        if packet.registry_reference_fixture != registry_reference_fixture:
            raise ValueError("all observation packets must use the same released registry fixture")
        if packet.registry_id != registry_id:
            raise ValueError("all observation packets must use the same released registry id")

    finding_counts_by_regime: dict[str, int] = {}
    finding_counts_by_action: dict[str, int] = {}
    safe_autofix_candidates: list[dict[str, str]] = []
    deterministic_high_severity_findings: list[dict[str, str]] = []
    review_only_findings: list[dict[str, str]] = []
    meta_governance_findings: list[dict[str, str]] = []
    finding_count = 0

    for packet in packets:
        for finding in packet.findings:
            finding_count += 1
            finding_counts_by_regime[finding.evidence_regime] = (
                finding_counts_by_regime.get(finding.evidence_regime, 0) + 1
            )
            finding_counts_by_action[finding.allowed_action] = (
                finding_counts_by_action.get(finding.allowed_action, 0) + 1
            )
            finding_ref = _finding_ref_from_packet(packet, finding)
            if finding.allowed_action == "safe_autofix":
                safe_autofix_candidates.append(finding_ref)
            elif finding.allowed_action in {"deterministic_finding", "forbid"}:
                deterministic_high_severity_findings.append(finding_ref)
            elif finding.allowed_action == "meta_artifact_correction":
                meta_governance_findings.append(finding_ref)
            else:
                review_only_findings.append(finding_ref)

    packet_ids = sorted(packet.observation_packet_id for packet in packets)
    packet_hashes = sorted(packet_hashes)
    subject_refs = sorted(packet.subject_ref for packet in packets)
    report_payload = {
        "report_id": (
            _derive_multi_packet_report_id(packet_hashes=packet_hashes)
            if len(packet_ids) > 1
            else f"{packet_ids[0]}_report"
        ),
        "registry_id": registry_id,
        "registry_reference_fixture": registry_reference_fixture,
        "aggregated_observation_packet_ids": packet_ids,
        "aggregated_observation_packet_hashes": packet_hashes,
        "aggregated_subject_refs": subject_refs,
        "observation_count": len(packets),
        "finding_count": finding_count,
        "findings_by_evidence_regime": [
            {
                "evidence_regime": regime,
                "finding_count": finding_counts_by_regime[regime],
            }
            for regime in sorted(finding_counts_by_regime)
        ],
        "findings_by_allowed_action": [
            {
                "allowed_action": action,
                "finding_count": finding_counts_by_action[action],
            }
            for action in sorted(finding_counts_by_action)
        ],
        "safe_autofix_candidates": sorted(
            safe_autofix_candidates,
            key=lambda entry: (
                entry["observation_packet_id"],
                entry["rule_id"],
                entry["local_observation_locator"],
            ),
        ),
        "deterministic_high_severity_findings": sorted(
            deterministic_high_severity_findings,
            key=lambda entry: (
                entry["observation_packet_id"],
                entry["rule_id"],
                entry["local_observation_locator"],
            ),
        ),
        "review_only_findings": sorted(
            review_only_findings,
            key=lambda entry: (
                entry["observation_packet_id"],
                entry["rule_id"],
                entry["local_observation_locator"],
            ),
        ),
        "meta_governance_findings": sorted(
            meta_governance_findings,
            key=lambda entry: (
                entry["observation_packet_id"],
                entry["rule_id"],
                entry["local_observation_locator"],
            ),
        ),
        "overall_pressure_mismatch_posture": _derive_overall_posture(
            safe_autofix_candidates=safe_autofix_candidates,
            deterministic_high_severity_findings=deterministic_high_severity_findings,
            review_only_findings=review_only_findings,
            meta_governance_findings=meta_governance_findings,
        ),
        "derivation_metadata": {
            "observation_packet_hashes": packet_hashes,
            "registry_reference_fixture_sha256": _sha256_repo_file(
                registry_reference_fixture,
                field_name="registry_reference_fixture",
                repository_root=repository_root,
            ),
        },
    }
    return SyntheticPressureMismatchConformanceReport.model_validate(
        report_payload,
        context=_validation_context(repository_root),
    )


__all__ = [
    "DEFAULT_V39C_REGISTRY_REFERENCE_FIXTURE_PATH",
    "SYNTHETIC_PRESSURE_MISMATCH_CONFORMANCE_REPORT_SCHEMA",
    "SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_PACKET_SCHEMA",
    "V39C_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE",
    "V39C_SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_EVALUATOR_ID",
    "V39C_SYNTHETIC_PRESSURE_MISMATCH_REPORT_EVALUATOR_ID",
    "SyntheticPressureMismatchConformanceDerivationMetadata",
    "SyntheticPressureMismatchConformanceReport",
    "SyntheticPressureMismatchDetectorProvenance",
    "SyntheticPressureMismatchFindingCountByAllowedAction",
    "SyntheticPressureMismatchFindingCountByEvidenceRegime",
    "SyntheticPressureMismatchFindingRef",
    "SyntheticPressureMismatchLocalSubjectFixture",
    "SyntheticPressureMismatchObservationDerivationMetadata",
    "SyntheticPressureMismatchObservationFinding",
    "SyntheticPressureMismatchObservationPacket",
    "canonicalize_synthetic_pressure_mismatch_conformance_report_payload",
    "canonicalize_synthetic_pressure_mismatch_observation_packet_payload",
    "derive_v39c_conformance_report",
    "derive_v39c_observation_packet",
]
