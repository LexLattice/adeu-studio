from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_CASE_BLUEPRINT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_CLEANROOM_EVIDENCE_PACK_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_CONTAMINATION_SCREEN_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_ORACLE_BOUNDARY_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_PROBE_CONTRACT_SCHEMA,
    ProgrambenchLocalCaseBlueprint,
    ProgrambenchLocalCaseCleanroomEvidencePack,
    ProgrambenchLocalCaseContaminationScreen,
    ProgrambenchLocalCaseExpansionControlContract,
    ProgrambenchLocalCaseExpansionEligibilityReview,
    ProgrambenchLocalCaseExpansionNonAuthorityGuardrail,
    ProgrambenchLocalCaseExpansionRequest,
    ProgrambenchLocalCaseOracleBoundary,
    ProgrambenchLocalCaseProbeContract,
    ProgrambenchLocalCaseSourcePoolManifest,
    validate_pb_case_expansion_0b_blueprint_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_case_expansion_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus263"


def _fixture_root_case_expansion_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus264"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_case_expansion_a(), name)


def _load_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_case_expansion_b(), name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (_repo_root() / "packages" / "adeu_benchmarking" / "schema" / schema_filename).read_text(
            encoding="utf-8"
        )
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = _repo_root()
    return [
        (
            PROGRAMBENCH_LOCAL_CASE_BLUEPRINT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_blueprint.v1.json",
            root / "spec" / "programbench_local_case_blueprint.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_CLEANROOM_EVIDENCE_PACK_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_cleanroom_evidence_pack.v1.json",
            root / "spec" / "programbench_local_case_cleanroom_evidence_pack.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_PROBE_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_probe_contract.v1.json",
            root / "spec" / "programbench_local_case_probe_contract.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_ORACLE_BOUNDARY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_oracle_boundary.v1.json",
            root / "spec" / "programbench_local_case_oracle_boundary.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_CONTAMINATION_SCREEN_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_contamination_screen.v1.json",
            root / "spec" / "programbench_local_case_contamination_screen.schema.json",
        ),
    ]


def _load_a_rows() -> tuple[
    ProgrambenchLocalCaseExpansionRequest,
    ProgrambenchLocalCaseSourcePoolManifest,
    ProgrambenchLocalCaseExpansionEligibilityReview,
    ProgrambenchLocalCaseExpansionControlContract,
    ProgrambenchLocalCaseExpansionNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalCaseExpansionRequest.model_validate(
            _load_a_fixture("programbench_local_case_expansion_request_v263_reference.json")
        ),
        ProgrambenchLocalCaseSourcePoolManifest.model_validate(
            _load_a_fixture("programbench_local_case_source_pool_manifest_v263_reference.json")
        ),
        ProgrambenchLocalCaseExpansionEligibilityReview.model_validate(
            _load_a_fixture(
                "programbench_local_case_expansion_eligibility_review_v263_reference.json"
            )
        ),
        ProgrambenchLocalCaseExpansionControlContract.model_validate(
            _load_a_fixture(
                "programbench_local_case_expansion_control_contract_v263_reference.json"
            )
        ),
        ProgrambenchLocalCaseExpansionNonAuthorityGuardrail.model_validate(
            _load_a_fixture(
                "programbench_local_case_expansion_non_authority_guardrail_v263_reference.json"
            )
        ),
    )


def _load_b_rows() -> tuple[
    ProgrambenchLocalCaseBlueprint,
    ProgrambenchLocalCaseCleanroomEvidencePack,
    ProgrambenchLocalCaseProbeContract,
    ProgrambenchLocalCaseOracleBoundary,
    ProgrambenchLocalCaseContaminationScreen,
]:
    return (
        ProgrambenchLocalCaseBlueprint.model_validate(
            _load_b_fixture("programbench_local_case_blueprint_v264_reference.json")
        ),
        ProgrambenchLocalCaseCleanroomEvidencePack.model_validate(
            _load_b_fixture(
                "programbench_local_case_cleanroom_evidence_pack_v264_reference.json"
            )
        ),
        ProgrambenchLocalCaseProbeContract.model_validate(
            _load_b_fixture("programbench_local_case_probe_contract_v264_reference.json")
        ),
        ProgrambenchLocalCaseOracleBoundary.model_validate(
            _load_b_fixture("programbench_local_case_oracle_boundary_v264_reference.json")
        ),
        ProgrambenchLocalCaseContaminationScreen.model_validate(
            _load_b_fixture("programbench_local_case_contamination_screen_v264_reference.json")
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_CASE_BLUEPRINT_SCHEMA,
            "programbench_local_case_blueprint.v1.json",
            "programbench_local_case_blueprint_v264_reference.json",
            ProgrambenchLocalCaseBlueprint,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_CLEANROOM_EVIDENCE_PACK_SCHEMA,
            "programbench_local_case_cleanroom_evidence_pack.v1.json",
            "programbench_local_case_cleanroom_evidence_pack_v264_reference.json",
            ProgrambenchLocalCaseCleanroomEvidencePack,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_PROBE_CONTRACT_SCHEMA,
            "programbench_local_case_probe_contract.v1.json",
            "programbench_local_case_probe_contract_v264_reference.json",
            ProgrambenchLocalCaseProbeContract,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_ORACLE_BOUNDARY_SCHEMA,
            "programbench_local_case_oracle_boundary.v1.json",
            "programbench_local_case_oracle_boundary_v264_reference.json",
            ProgrambenchLocalCaseOracleBoundary,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_CONTAMINATION_SCREEN_SCHEMA,
            "programbench_local_case_contamination_screen.v1.json",
            "programbench_local_case_contamination_screen_v264_reference.json",
            ProgrambenchLocalCaseContaminationScreen,
        ),
    ],
)
def test_pb_case_expansion_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_case_expansion_0b_reference_bundle_preserves_blueprint_boundary() -> None:
    request, manifest, eligibility, control, guardrail = _load_a_rows()
    blueprint, evidence_pack, probe_contract, oracle_boundary, contamination_screen = (
        _load_b_rows()
    )

    validate_pb_case_expansion_0b_blueprint_bundle(
        expansion_request=request,
        source_pool_manifest=manifest,
        eligibility_review=eligibility,
        control_contract=control,
        non_authority_guardrail=guardrail,
        case_blueprint=blueprint,
        cleanroom_evidence_pack=evidence_pack,
        probe_contract=probe_contract,
        oracle_boundary=oracle_boundary,
        contamination_screen=contamination_screen,
    )

    assert blueprint.execution_deferred_posture == "execution_deferred_to_later_trial_family"
    assert probe_contract.command_execution_posture == (
        "no_command_execution_authority_granted_by_0b"
    )
    assert oracle_boundary.hidden_test_equivalence_posture == (
        "no_hidden_test_equivalence_claimed"
    )
    assert contamination_screen.screen_verdict == "passed_cleanroom_screen"


def test_pb_case_expansion_0b_bundle_rejects_blocked_or_unknown_candidate() -> None:
    request, manifest, eligibility, control, guardrail = _load_a_rows()
    _, evidence_pack, probe_contract, oracle_boundary, contamination_screen = _load_b_rows()
    blueprint = ProgrambenchLocalCaseBlueprint.model_validate(
        _load_b_fixture(
            "programbench_local_case_expansion_v264_reject_blocked_candidate_blueprint.json"
        )
    )

    with pytest.raises(ValueError, match="candidate must exist"):
        validate_pb_case_expansion_0b_blueprint_bundle(
            expansion_request=request,
            source_pool_manifest=manifest,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
            case_blueprint=blueprint,
            cleanroom_evidence_pack=evidence_pack,
            probe_contract=probe_contract,
            oracle_boundary=oracle_boundary,
            contamination_screen=contamination_screen,
        )


def test_pb_case_expansion_0b_evidence_rejects_forbidden_summary_leak() -> None:
    payload = _load_b_fixture(
        "programbench_local_case_expansion_v264_reject_evidence_forbidden_summary.json"
    )

    with pytest.raises(ValidationError, match="derived-summary leakage"):
        ProgrambenchLocalCaseCleanroomEvidencePack.model_validate(payload)


def test_pb_case_expansion_0b_evidence_requires_obligation_basis_rows() -> None:
    payload = _load_b_fixture(
        "programbench_local_case_expansion_v264_reject_evidence_missing_basis.json"
    )

    with pytest.raises(ValidationError, match="every behavior obligation"):
        ProgrambenchLocalCaseCleanroomEvidencePack.model_validate(payload)


def test_pb_case_expansion_0b_evidence_basis_witness_must_match_obligation() -> None:
    payload = _load_b_fixture(
        "programbench_local_case_cleanroom_evidence_pack_v264_reference.json"
    )
    payload = deepcopy(payload)
    payload["behavior_obligation_basis_rows"][2]["source_witness_refs"] = [
        "source-witness:diagnostic-probe"
    ]

    with pytest.raises(ValidationError, match="witness the supported obligation"):
        ProgrambenchLocalCaseCleanroomEvidencePack.model_validate(payload)


def test_pb_case_expansion_0b_probe_rejects_command_authority() -> None:
    payload = _load_b_fixture(
        "programbench_local_case_expansion_v264_reject_probe_command_authority.json"
    )

    with pytest.raises(ValidationError, match="command_execution_authorized"):
        ProgrambenchLocalCaseProbeContract.model_validate(payload)


def test_pb_case_expansion_0b_probe_rejects_raw_shell_string() -> None:
    payload = _load_b_fixture("programbench_local_case_expansion_v264_reject_probe_raw_shell.json")

    with pytest.raises(ValidationError, match="argv templates"):
        ProgrambenchLocalCaseProbeContract.model_validate(payload)


def test_pb_case_expansion_0b_oracle_rejects_hidden_test_equivalence() -> None:
    payload = _load_b_fixture(
        "programbench_local_case_expansion_v264_reject_oracle_hidden_equivalence.json"
    )

    with pytest.raises(ValidationError, match="hidden_test_equivalence_claimed"):
        ProgrambenchLocalCaseOracleBoundary.model_validate(payload)


def test_pb_case_expansion_0b_oracle_basis_witnesses_resolve_to_evidence_pack() -> None:
    request, manifest, eligibility, control, guardrail = _load_a_rows()
    blueprint, evidence_pack, probe_contract, oracle_boundary, contamination_screen = (
        _load_b_rows()
    )
    oracle_boundary_payload = _load_b_fixture(
        "programbench_local_case_oracle_boundary_v264_reference.json"
    )
    oracle_boundary_payload = deepcopy(oracle_boundary_payload)
    oracle_boundary_payload["local_oracle_basis_rows"][0]["source_witness_refs"] = [
        "source-witness:foreign"
    ]
    oracle_boundary = ProgrambenchLocalCaseOracleBoundary.model_validate(
        oracle_boundary_payload
    )

    with pytest.raises(ValueError, match="local_oracle_basis_rows.source_witness_refs"):
        validate_pb_case_expansion_0b_blueprint_bundle(
            expansion_request=request,
            source_pool_manifest=manifest,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
            case_blueprint=blueprint,
            cleanroom_evidence_pack=evidence_pack,
            probe_contract=probe_contract,
            oracle_boundary=oracle_boundary,
            contamination_screen=contamination_screen,
        )


def test_pb_case_expansion_0b_contamination_screen_fails_closed() -> None:
    payload = _load_b_fixture(
        "programbench_local_case_expansion_v264_reject_contamination_clean_with_exposure.json"
    )

    with pytest.raises(ValidationError, match="passed contamination screens"):
        ProgrambenchLocalCaseContaminationScreen.model_validate(payload)


def test_pb_case_expansion_0b_rejects_c_artifact_shape() -> None:
    payload = _load_b_fixture("programbench_local_case_expansion_v264_reject_c_artifact_shape.json")

    with pytest.raises(ValidationError):
        ProgrambenchLocalCaseBlueprint.model_validate(payload)


def test_pb_case_expansion_0b_schema_exports_are_current() -> None:
    export_schema_main()
    for schema_name, authoritative_path, mirror_path in _schema_pairs():
        assert authoritative_path.exists(), schema_name
        assert mirror_path.exists(), schema_name
        assert authoritative_path.read_text(encoding="utf-8") == mirror_path.read_text(
            encoding="utf-8"
        )
        payload = json.loads(authoritative_path.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == schema_name
