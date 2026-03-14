from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, TypeVar

from pydantic import BaseModel, ConfigDict, Field, ValidationError

from .ux_governance import (
    V36A_ALTERNATE_LAWFUL_PROFILE_ID,
    V36A_APPROVED_PROFILE_TABLE_SCHEMA,
    V36A_CANONICAL_REFERENCE_PROFILE_ID,
    V36A_REFERENCE_SURFACE_FAMILY,
    V36A_SAME_CONTEXT_GLOSSARY_SCHEMA,
    UXDomainPacket,
    UXMorphIR,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    assert_v36a_reference_bundle_consistent,
)

V36A_UX_DOMAIN_MORPH_IR_EVIDENCE_SCHEMA = "v36a_ux_domain_morph_ir_evidence@1"
V36A_UX_DOMAIN_MORPH_IR_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md#v36a_ux_domain_morph_ir_contract@1"
)
STOP_GATE_METRICS_SCHEMA = "stop_gate_metrics@1"
EXPECTED_METRIC_KEY_CARDINALITY = 80

DEFAULT_UX_DOMAIN_PACKET_SCHEMA_PATH = "packages/adeu_core_ir/schema/ux_domain_packet.v1.json"
DEFAULT_UX_MORPH_IR_SCHEMA_PATH = "packages/adeu_core_ir/schema/ux_morph_ir.v1.json"
DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus61/"
    "ux_domain_packet_artifact_inspector_reference.json"
)
DEFAULT_UX_MORPH_IR_REFERENCE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus61/ux_morph_ir_artifact_inspector_reference.json"
)
DEFAULT_APPROVED_PROFILE_TABLE_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json"
)
DEFAULT_SAME_CONTEXT_GLOSSARY_PATH = (
    "apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json"
)

ModelT = TypeVar("ModelT", bound=BaseModel)
_FREE_FORM_POLICY_LOC = (
    "authority_boundary_policy",
    "no_free_form_ui_codegen_without_ir",
)
_AUTHORITY_MINTING_POLICY_LOC = (
    "authority_boundary_policy",
    "ui_artifacts_may_express_but_may_not_mint_authority",
)


class UXGovernanceEvidenceError(ValueError):
    pass


class MaterializedUXGovernanceEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    path: str = Field(min_length=1)
    hash: str = Field(min_length=64, max_length=64)
    payload: dict[str, Any]


class V36AUXDomainMorphIREvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V36A_UX_DOMAIN_MORPH_IR_EVIDENCE_SCHEMA, alias="schema")
    contract_source: str = V36A_UX_DOMAIN_MORPH_IR_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    ux_domain_packet_schema_path: str = Field(min_length=1)
    ux_domain_packet_schema_hash: str = Field(min_length=64, max_length=64)
    ux_morph_ir_schema_path: str = Field(min_length=1)
    ux_morph_ir_schema_hash: str = Field(min_length=64, max_length=64)
    ux_domain_packet_reference_path: str = Field(min_length=1)
    ux_domain_packet_reference_hash: str = Field(min_length=64, max_length=64)
    ux_morph_ir_reference_path: str = Field(min_length=1)
    ux_morph_ir_reference_hash: str = Field(min_length=64, max_length=64)
    approved_profile_table_path: str = Field(min_length=1)
    approved_profile_table_hash: str = Field(min_length=64, max_length=64)
    same_context_reachability_glossary_path: str = Field(min_length=1)
    same_context_reachability_glossary_hash: str = Field(min_length=64, max_length=64)
    adeu_split_vocabulary_frozen: bool
    approved_profile_table_frozen: bool
    approved_profile_cardinality_verified: bool
    reference_instance_binding_verified: bool
    reference_instance_required_and_present: bool
    deterministic_serialization_verified: bool
    no_free_form_ui_codegen_without_ir_preserved: bool
    ui_artifacts_may_express_but_may_not_mint_authority_preserved: bool
    v35_authority_baseline_unchanged: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v60: bool
    notes: str = Field(min_length=1)


def _canonical_json(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_canonical_json(value: object) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _pretty_canonical_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _resolve_repo_relative_path(
    *,
    root: Path,
    path_text: str,
    field_name: str,
    required_prefix: str | None = None,
) -> Path:
    if not path_text:
        raise UXGovernanceEvidenceError(f"{field_name} must not be empty")
    relative = Path(path_text)
    if relative.is_absolute():
        raise UXGovernanceEvidenceError(f"{field_name} must be repo-relative")
    if required_prefix is not None and not path_text.startswith(required_prefix):
        raise UXGovernanceEvidenceError(
            f"{field_name} must stay under the {required_prefix!r} subtree"
        )
    if any(part in {"", ".", ".."} for part in relative.parts):
        raise UXGovernanceEvidenceError(f"{field_name} contains invalid path components")
    resolved = (root / relative).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise UXGovernanceEvidenceError(f"{field_name} must stay within repository root") from exc
    return resolved


def _load_json_dict(*, path: Path, field_name: str) -> tuple[str, dict[str, Any]]:
    if not path.is_file():
        raise UXGovernanceEvidenceError(f"{field_name} does not exist")
    text = path.read_text(encoding="utf-8")
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        raise UXGovernanceEvidenceError(f"{field_name} is not valid JSON") from exc
    if not isinstance(payload, dict):
        raise UXGovernanceEvidenceError(f"{field_name} must contain a JSON object")
    return text, payload


def _validate_pretty_canonical_serialization(
    *,
    text: str,
    payload: dict[str, Any],
    field_name: str,
) -> None:
    expected = _pretty_canonical_json(payload)
    if text != expected:
        raise UXGovernanceEvidenceError(
            f"{field_name} must use the frozen pretty canonical JSON writer profile"
        )


def _load_stop_gate_metrics(*, path: Path, field_name: str) -> dict[str, Any]:
    _text, payload = _load_json_dict(path=path, field_name=field_name)
    if payload.get("schema") != STOP_GATE_METRICS_SCHEMA:
        raise UXGovernanceEvidenceError(f"{field_name} must use {STOP_GATE_METRICS_SCHEMA}")
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict) or not all(isinstance(key, str) for key in metrics):
        raise UXGovernanceEvidenceError(f"{field_name} metrics must be an object with string keys")
    return payload


def _load_validated_model(
    *,
    path: Path,
    field_name: str,
    model_type: type[ModelT],
) -> tuple[dict[str, Any], ModelT]:
    text, payload = _load_json_dict(path=path, field_name=field_name)
    _validate_pretty_canonical_serialization(text=text, payload=payload, field_name=field_name)
    try:
        model = model_type.model_validate(payload)
    except ValidationError as exc:
        for error in exc.errors():
            loc = tuple(error.get("loc", ()))
            if loc == _FREE_FORM_POLICY_LOC:
                raise UXGovernanceEvidenceError("free-form UI codegen bypass detected") from exc
            if loc == _AUTHORITY_MINTING_POLICY_LOC:
                raise UXGovernanceEvidenceError("authority-minting drift detected") from exc
        raise UXGovernanceEvidenceError(f"{field_name} is invalid") from exc
    return payload, model


def _load_frozen_schema(
    *,
    path: Path,
    field_name: str,
    model_type: type[BaseModel],
) -> dict[str, Any]:
    text, payload = _load_json_dict(path=path, field_name=field_name)
    _validate_pretty_canonical_serialization(text=text, payload=payload, field_name=field_name)
    expected = model_type.model_json_schema(by_alias=True)
    if payload != expected:
        raise UXGovernanceEvidenceError(f"{field_name} does not match the frozen exported schema")
    return payload


def materialize_v36a_ux_domain_morph_ir_evidence(
    *,
    repo_root: Path,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
    ux_domain_packet_schema_path: str = DEFAULT_UX_DOMAIN_PACKET_SCHEMA_PATH,
    ux_morph_ir_schema_path: str = DEFAULT_UX_MORPH_IR_SCHEMA_PATH,
    ux_domain_packet_reference_path: str = DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
    ux_morph_ir_reference_path: str = DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
    approved_profile_table_path: str = DEFAULT_APPROVED_PROFILE_TABLE_PATH,
    same_context_reachability_glossary_path: str = DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
) -> MaterializedUXGovernanceEvidence:
    repo_root = repo_root.resolve()
    if not repo_root.is_dir():
        raise UXGovernanceEvidenceError("repository root does not exist")

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )
    domain_schema_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_domain_packet_schema_path,
        field_name="ux_domain_packet_schema_path",
        required_prefix="packages/",
    )
    morph_schema_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_ir_schema_path,
        field_name="ux_morph_ir_schema_path",
        required_prefix="packages/",
    )
    domain_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_domain_packet_reference_path,
        field_name="ux_domain_packet_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    morph_reference_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=ux_morph_ir_reference_path,
        field_name="ux_morph_ir_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    approved_profile_table_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=approved_profile_table_path,
        field_name="approved_profile_table_path",
        required_prefix="apps/api/fixtures/",
    )
    same_context_glossary_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=same_context_reachability_glossary_path,
        field_name="same_context_reachability_glossary_path",
        required_prefix="apps/api/fixtures/",
    )

    baseline_metrics = _load_stop_gate_metrics(
        path=baseline_metrics_file,
        field_name="baseline_metrics_path",
    )
    current_metrics = _load_stop_gate_metrics(
        path=current_metrics_file,
        field_name="current_metrics_path",
    )
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    current_metric_keys = set(current_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise UXGovernanceEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise UXGovernanceEvidenceError("metric key set must remain exactly equal to v60")

    domain_schema_payload = _load_frozen_schema(
        path=domain_schema_file,
        field_name="ux_domain_packet_schema_path",
        model_type=UXDomainPacket,
    )
    morph_schema_payload = _load_frozen_schema(
        path=morph_schema_file,
        field_name="ux_morph_ir_schema_path",
        model_type=UXMorphIR,
    )
    domain_payload, domain_packet = _load_validated_model(
        path=domain_reference_file,
        field_name="ux_domain_packet_reference_path",
        model_type=UXDomainPacket,
    )
    morph_payload, morph_ir = _load_validated_model(
        path=morph_reference_file,
        field_name="ux_morph_ir_reference_path",
        model_type=UXMorphIR,
    )
    profile_table_payload, approved_profile_table = _load_validated_model(
        path=approved_profile_table_file,
        field_name="approved_profile_table_path",
        model_type=V36AFirstFamilyApprovedProfileTable,
    )
    glossary_payload, same_context_glossary = _load_validated_model(
        path=same_context_glossary_file,
        field_name="same_context_reachability_glossary_path",
        model_type=V36ASameContextReachabilityGlossary,
    )

    try:
        assert_v36a_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
        )
    except ValueError as exc:
        raise UXGovernanceEvidenceError(str(exc)) from exc

    if not {"ontology", "epistemics", "deontics", "utility"}.issubset(morph_payload):
        raise UXGovernanceEvidenceError("ux_morph_ir reference must preserve the A/E/D/U split")
    if "invariants" not in morph_payload or "morphable_surface_choices" not in morph_payload:
        raise UXGovernanceEvidenceError(
            "ux_morph_ir reference must preserve invariant and morphable surface separation"
        )
    if approved_profile_table.reference_surface_family != V36A_REFERENCE_SURFACE_FAMILY:
        raise UXGovernanceEvidenceError("approved profile table reference surface family drift")
    if approved_profile_table.canonical_reference_profile_id != V36A_CANONICAL_REFERENCE_PROFILE_ID:
        raise UXGovernanceEvidenceError("canonical reference profile id drift detected")
    if approved_profile_table.alternate_lawful_profile_id != V36A_ALTERNATE_LAWFUL_PROFILE_ID:
        raise UXGovernanceEvidenceError("alternate lawful profile id drift detected")
    if approved_profile_table.schema != V36A_APPROVED_PROFILE_TABLE_SCHEMA:
        raise UXGovernanceEvidenceError("approved profile table schema drift detected")
    if same_context_glossary.schema != V36A_SAME_CONTEXT_GLOSSARY_SCHEMA:
        raise UXGovernanceEvidenceError("same-context reachability glossary schema drift detected")
    if (
        not domain_packet.authority_boundary_policy.no_free_form_ui_codegen_without_ir
        or not morph_ir.authority_boundary_policy.no_free_form_ui_codegen_without_ir
    ):
        raise UXGovernanceEvidenceError("free-form UI codegen bypass detected")
    domain_mint_policy = (
        domain_packet.authority_boundary_policy.ui_artifacts_may_express_but_may_not_mint_authority
    )
    morph_mint_policy = (
        morph_ir.authority_boundary_policy.ui_artifacts_may_express_but_may_not_mint_authority
    )
    if (
        not domain_mint_policy
        or not morph_mint_policy
    ):
        raise UXGovernanceEvidenceError("authority-minting drift detected")

    evidence = V36AUXDomainMorphIREvidence(
        evidence_input_path=output_path,
        ux_domain_packet_schema_path=ux_domain_packet_schema_path,
        ux_domain_packet_schema_hash=_sha256_canonical_json(domain_schema_payload),
        ux_morph_ir_schema_path=ux_morph_ir_schema_path,
        ux_morph_ir_schema_hash=_sha256_canonical_json(morph_schema_payload),
        ux_domain_packet_reference_path=ux_domain_packet_reference_path,
        ux_domain_packet_reference_hash=_sha256_canonical_json(domain_payload),
        ux_morph_ir_reference_path=ux_morph_ir_reference_path,
        ux_morph_ir_reference_hash=_sha256_canonical_json(morph_payload),
        approved_profile_table_path=approved_profile_table_path,
        approved_profile_table_hash=_sha256_canonical_json(profile_table_payload),
        same_context_reachability_glossary_path=same_context_reachability_glossary_path,
        same_context_reachability_glossary_hash=_sha256_canonical_json(glossary_payload),
        adeu_split_vocabulary_frozen=True,
        approved_profile_table_frozen=True,
        approved_profile_cardinality_verified=len(approved_profile_table.profiles) == 2,
        reference_instance_binding_verified=True,
        reference_instance_required_and_present=True,
        deterministic_serialization_verified=True,
        no_free_form_ui_codegen_without_ir_preserved=True,
        ui_artifacts_may_express_but_may_not_mint_authority_preserved=True,
        v35_authority_baseline_unchanged=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v60=True,
        notes=(
            "v61 closeout evidence remains pre-projection, pre-rendered-surface, and "
            "pre-compiler; it verifies the typed ux-domain/morph substrate only."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(_pretty_canonical_json(payload), encoding="utf-8")
    return MaterializedUXGovernanceEvidence(
        path=output_path,
        hash=_sha256_canonical_json(payload),
        payload=payload,
    )
