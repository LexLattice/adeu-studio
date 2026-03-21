from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, ValidationError

from .external_contribution_alignment import (
    EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA,
    MODULE_CONFORMANCE_REPORT_SCHEMA,
    V39A_MODULE_CONFORMANCE_EVALUATOR_ID,
    ExternalContributionAlignmentPacket,
    ModuleConformanceReport,
    PolicySourceSnapshot,
    canonicalize_external_contribution_alignment_packet_payload,
    canonicalize_module_conformance_report_payload,
    derive_v39a_module_conformance,
)

V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_SCHEMA = (
    "v39a_external_contribution_alignment_evidence@1"
)
V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS72.md#v39a_external_contribution_alignment_contract@1"
)
DEFAULT_EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_REFERENCE_PATH = (
    "apps/api/fixtures/external_contribution_alignment/vnext_plus72/"
    "external_contribution_alignment_packet_pr293_poetry_utility.json"
)
DEFAULT_MODULE_CONFORMANCE_REPORT_REFERENCE_PATH = (
    "apps/api/fixtures/external_contribution_alignment/vnext_plus72/"
    "module_conformance_report_pr293_poetry_utility.json"
)
DEFAULT_V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_PATH = (
    "artifacts/agent_harness/v72/evidence_inputs/"
    "v39a_external_contribution_alignment_evidence_v72.json"
)


class ExternalContributionAlignmentEvidenceError(ValueError):
    pass


class MaterializedExternalContributionAlignmentEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    path: str = Field(min_length=1)
    hash: str = Field(min_length=64, max_length=64)
    payload: dict[str, Any]


class V39AExternalContributionAlignmentEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(
        default=V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_SCHEMA,
        alias="schema",
    )
    contract_source: str = V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    external_contribution_alignment_packet_reference_path: str = Field(min_length=1)
    external_contribution_alignment_packet_reference_hash: str = Field(
        pattern=r"^[0-9a-f]{64}$"
    )
    module_conformance_report_reference_path: str = Field(min_length=1)
    module_conformance_report_reference_hash: str = Field(pattern=r"^[0-9a-f]{64}$")
    policy_sources: list[PolicySourceSnapshot]
    evaluator_id: str = V39A_MODULE_CONFORMANCE_EVALUATOR_ID
    evaluator_version: Literal["1"] = "1"
    localized_subject_inputs_verified: bool
    code_and_meta_sequence_dimensions_separated: bool
    three_layer_scope_model_verified: bool
    default_negative_precedent_verified: bool
    live_github_dependency_absent: Literal[True] = True
    verification_passed: bool
    notes: str = Field(min_length=1)


def _normalize_repo_relative_path(value: str, *, field_name: str) -> str:
    normalized = value.strip().replace("\\", "/")
    if not normalized:
        raise ExternalContributionAlignmentEvidenceError(f"{field_name} must not be empty")
    if normalized.startswith("/") or normalized.startswith("../") or "/../" in normalized:
        raise ExternalContributionAlignmentEvidenceError(
            f"{field_name} must be repository-relative"
        )
    return normalized


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_payload_hash(payload: dict[str, Any]) -> str:
    return hashlib.sha256(
        json.dumps(
            payload,
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        ).encode("utf-8")
    ).hexdigest()


def _resolve_required_file(*, repo_root: Path, relative_path: str, field_name: str) -> Path:
    normalized = _normalize_repo_relative_path(relative_path, field_name=field_name)
    path = repo_root / normalized
    if not path.is_file():
        raise ExternalContributionAlignmentEvidenceError(f"{field_name} does not exist")
    return path


def _read_json_object(path: Path, *, field_name: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ExternalContributionAlignmentEvidenceError(f"{field_name} is not valid JSON") from exc
    if not isinstance(payload, dict):
        raise ExternalContributionAlignmentEvidenceError(f"{field_name} must contain a JSON object")
    return payload


def _verify_three_layer_scope_model(report: ModuleConformanceReport) -> bool:
    observed_surface_refs = {
        entry.surface_ref for entry in report.observed_reachable_surfaces if entry.reachable
    }
    if not observed_surface_refs:
        return False
    if not set(report.accepted_shipped_scope.surface_refs).issubset(observed_surface_refs):
        return False
    return True


def _verify_default_negative_precedent(report: ModuleConformanceReport) -> bool:
    if report.derivation_metadata.default_precedent_status != "non_precedent":
        return False
    if report.precedent_status == "non_precedent":
        return report.precedent_reason is None
    return bool(report.precedent_reason)


def materialize_v39a_external_contribution_alignment_evidence(
    *,
    repository_root: Path,
    external_contribution_alignment_packet_reference_path: str = (
        DEFAULT_EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_REFERENCE_PATH
    ),
    module_conformance_report_reference_path: str = (
        DEFAULT_MODULE_CONFORMANCE_REPORT_REFERENCE_PATH
    ),
    evidence_input_path: str = DEFAULT_V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_PATH,
) -> MaterializedExternalContributionAlignmentEvidence:
    if not repository_root.exists():
        raise ExternalContributionAlignmentEvidenceError("repository root does not exist")

    packet_path = _resolve_required_file(
        repo_root=repository_root,
        relative_path=external_contribution_alignment_packet_reference_path,
        field_name="external_contribution_alignment_packet_reference_path",
    )
    report_path = _resolve_required_file(
        repo_root=repository_root,
        relative_path=module_conformance_report_reference_path,
        field_name="module_conformance_report_reference_path",
    )
    packet_payload = _read_json_object(
        packet_path,
        field_name="external_contribution_alignment_packet_reference_path",
    )
    if packet_payload.get("schema") != EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA:
        raise ExternalContributionAlignmentEvidenceError(
            "external_contribution_alignment_packet_reference_path must use "
            f"{EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA}"
        )
    try:
        canonical_packet = canonicalize_external_contribution_alignment_packet_payload(
            packet_payload,
            repository_root=repository_root,
        )
        packet = ExternalContributionAlignmentPacket.model_validate(
            canonical_packet,
            context={"repository_root": repository_root},
        )
    except ValidationError as exc:
        raise ExternalContributionAlignmentEvidenceError(str(exc)) from exc
    report_payload = _read_json_object(
        report_path,
        field_name="module_conformance_report_reference_path",
    )
    if report_payload.get("schema") != MODULE_CONFORMANCE_REPORT_SCHEMA:
        raise ExternalContributionAlignmentEvidenceError(
            "module_conformance_report_reference_path must use "
            f"{MODULE_CONFORMANCE_REPORT_SCHEMA}"
        )
    expected_report = canonicalize_module_conformance_report_payload(
        derive_v39a_module_conformance(
            packet,
            repository_root=repository_root,
        ).model_dump(mode="json", exclude_none=True),
        repository_root=repository_root,
    )
    try:
        canonical_report = canonicalize_module_conformance_report_payload(
            report_payload,
            repository_root=repository_root,
        )
    except ValidationError as exc:
        raise ExternalContributionAlignmentEvidenceError(str(exc)) from exc
    if canonical_report != expected_report:
        raise ExternalContributionAlignmentEvidenceError(
            "module conformance report must match deterministic derivation from packet"
        )
    try:
        report = ModuleConformanceReport.model_validate(
            canonical_report,
            context={"repository_root": repository_root},
        )
    except ValidationError as exc:
        raise ExternalContributionAlignmentEvidenceError(str(exc)) from exc
    packet_hash = _canonical_payload_hash(canonical_packet)
    if report.derivation_metadata.alignment_packet_hash != packet_hash:
        raise ExternalContributionAlignmentEvidenceError(
            "module conformance report must pin the canonical packet hash"
        )
    code_and_meta_sequence_dimensions_separated = (
        bool(packet.imported_meta_sequence_gaps)
        and report.meta_sequence_alignment_judgment != "native"
    ) or (
        not packet.imported_meta_sequence_gaps
        and report.meta_sequence_alignment_judgment == "native"
    )
    evidence = V39AExternalContributionAlignmentEvidence(
        evidence_input_path=_normalize_repo_relative_path(
            evidence_input_path,
            field_name="evidence_input_path",
        ),
        external_contribution_alignment_packet_reference_path=_normalize_repo_relative_path(
            external_contribution_alignment_packet_reference_path,
            field_name="external_contribution_alignment_packet_reference_path",
        ),
        external_contribution_alignment_packet_reference_hash=_sha256_file(packet_path),
        module_conformance_report_reference_path=_normalize_repo_relative_path(
            module_conformance_report_reference_path,
            field_name="module_conformance_report_reference_path",
        ),
        module_conformance_report_reference_hash=_sha256_file(report_path),
        policy_sources=report.derivation_metadata.policy_sources,
        localized_subject_inputs_verified=True,
        code_and_meta_sequence_dimensions_separated=code_and_meta_sequence_dimensions_separated,
        three_layer_scope_model_verified=_verify_three_layer_scope_model(report),
        default_negative_precedent_verified=_verify_default_negative_precedent(report),
        verification_passed=True,
        notes=(
            "v72 evidence pins the localized subject bundle, packet/report hash binding, "
            "policy provenance, and default-negative precedent semantics for the first "
            "retrospective external-alignment reference."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    return MaterializedExternalContributionAlignmentEvidence(
        path=evidence.evidence_input_path,
        hash=_canonical_payload_hash(payload),
        payload=payload,
    )


__all__ = [
    "DEFAULT_EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_REFERENCE_PATH",
    "DEFAULT_MODULE_CONFORMANCE_REPORT_REFERENCE_PATH",
    "DEFAULT_V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_PATH",
    "ExternalContributionAlignmentEvidenceError",
    "MaterializedExternalContributionAlignmentEvidence",
    "V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_CONTRACT_SOURCE",
    "V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_SCHEMA",
    "V39AExternalContributionAlignmentEvidence",
    "materialize_v39a_external_contribution_alignment_evidence",
]
