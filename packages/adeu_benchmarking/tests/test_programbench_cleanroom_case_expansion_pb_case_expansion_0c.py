from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_READINESS_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_LINEAGE_REGISTRATION_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_CANDIDATE_HANDOFF_SCHEMA,
    ProgrambenchLocalCaseBlueprint,
    ProgrambenchLocalCaseCleanroomEvidencePack,
    ProgrambenchLocalCaseContaminationScreen,
    ProgrambenchLocalCaseExpansionControlContract,
    ProgrambenchLocalCaseExpansionEligibilityReview,
    ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment,
    ProgrambenchLocalCaseExpansionNonAuthorityGuardrail,
    ProgrambenchLocalCaseExpansionReadinessSummary,
    ProgrambenchLocalCaseExpansionRequest,
    ProgrambenchLocalCaseLineageRegistration,
    ProgrambenchLocalCaseMatrixCandidateHandoff,
    ProgrambenchLocalCaseOracleBoundary,
    ProgrambenchLocalCaseProbeContract,
    ProgrambenchLocalCaseSourcePoolManifest,
    validate_pb_case_expansion_0c_closeout_bundle,
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


def _fixture_root_case_expansion_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus265"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_case_expansion_a(), name)


def _load_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_case_expansion_b(), name)


def _load_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_case_expansion_c(), name)


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
            PROGRAMBENCH_LOCAL_CASE_LINEAGE_REGISTRATION_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_lineage_registration.v1.json",
            root / "spec" / "programbench_local_case_lineage_registration.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_READINESS_SUMMARY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_expansion_readiness_summary.v1.json",
            root
            / "spec"
            / "programbench_local_case_expansion_readiness_summary.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_CANDIDATE_HANDOFF_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_candidate_handoff.v1.json",
            root / "spec" / "programbench_local_case_matrix_candidate_handoff.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_expansion_family_closeout_alignment.v1.json",
            root
            / "spec"
            / "programbench_local_case_expansion_family_closeout_alignment.schema.json",
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


def _load_c_rows() -> tuple[
    ProgrambenchLocalCaseLineageRegistration,
    ProgrambenchLocalCaseExpansionReadinessSummary,
    ProgrambenchLocalCaseMatrixCandidateHandoff,
    ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchLocalCaseLineageRegistration.model_validate(
            _load_c_fixture("programbench_local_case_lineage_registration_v265_reference.json")
        ),
        ProgrambenchLocalCaseExpansionReadinessSummary.model_validate(
            _load_c_fixture(
                "programbench_local_case_expansion_readiness_summary_v265_reference.json"
            )
        ),
        ProgrambenchLocalCaseMatrixCandidateHandoff.model_validate(
            _load_c_fixture(
                "programbench_local_case_matrix_candidate_handoff_v265_reference.json"
            )
        ),
        ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment.model_validate(
            _load_c_fixture(
                "programbench_local_case_expansion_family_closeout_alignment_v265_reference.json"
            )
        ),
    )


def _validate_reference_bundle() -> None:
    request, manifest, eligibility, control, guardrail = _load_a_rows()
    blueprint, evidence_pack, probe_contract, oracle_boundary, contamination_screen = (
        _load_b_rows()
    )
    lineage_registration, readiness_summary, matrix_handoff, closeout = _load_c_rows()

    validate_pb_case_expansion_0c_closeout_bundle(
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
        lineage_registration=lineage_registration,
        readiness_summary=readiness_summary,
        matrix_candidate_handoff=matrix_handoff,
        family_closeout_alignment=closeout,
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_CASE_LINEAGE_REGISTRATION_SCHEMA,
            "programbench_local_case_lineage_registration.v1.json",
            "programbench_local_case_lineage_registration_v265_reference.json",
            ProgrambenchLocalCaseLineageRegistration,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_READINESS_SUMMARY_SCHEMA,
            "programbench_local_case_expansion_readiness_summary.v1.json",
            "programbench_local_case_expansion_readiness_summary_v265_reference.json",
            ProgrambenchLocalCaseExpansionReadinessSummary,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_CANDIDATE_HANDOFF_SCHEMA,
            "programbench_local_case_matrix_candidate_handoff.v1.json",
            "programbench_local_case_matrix_candidate_handoff_v265_reference.json",
            ProgrambenchLocalCaseMatrixCandidateHandoff,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_local_case_expansion_family_closeout_alignment.v1.json",
            "programbench_local_case_expansion_family_closeout_alignment_v265_reference.json",
            ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_case_expansion_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_c_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_case_expansion_0c_reference_bundle_closes_local_case_supply() -> None:
    _validate_reference_bundle()

    lineage_registration, readiness_summary, matrix_handoff, closeout = _load_c_rows()
    assert lineage_registration.lineage_registration_status == (
        "registered_for_later_matrix_review"
    )
    assert readiness_summary.ready_count_posture == "inventory_count_only_not_success_rate"
    assert matrix_handoff.handoff_non_selection_posture == (
        "pressure_only_no_matrix_inclusion_selected"
    )
    assert closeout.future_family_authority_posture == (
        "no_future_family_selection_authority_granted_by_0c"
    )
    assert closeout.case_expansion_request_refs == [
        "case-expansion:pb-case-expansion-0a:reference"
    ]
    assert closeout.case_blueprint_refs == [
        "case-blueprint:pb-case-expansion-0b:diagnostic"
    ]
    assert closeout.lineage_registration_refs == [
        "case-lineage-registration:pb-case-expansion-0c:diagnostic"
    ]


def test_pb_case_expansion_0c_bundle_rejects_contaminated_lineage_registration() -> None:
    request, manifest, eligibility, control, guardrail = _load_a_rows()
    blueprint, evidence_pack, probe_contract, oracle_boundary, contamination_screen = (
        _load_b_rows()
    )
    _, readiness_summary, matrix_handoff, closeout = _load_c_rows()
    lineage_registration = ProgrambenchLocalCaseLineageRegistration.model_validate(
        _load_c_fixture("programbench_local_case_expansion_v265_reject_lineage_contaminated.json")
    )

    with pytest.raises(ValueError, match="registered lineage status"):
        validate_pb_case_expansion_0c_closeout_bundle(
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
            lineage_registration=lineage_registration,
            readiness_summary=readiness_summary,
            matrix_candidate_handoff=matrix_handoff,
            family_closeout_alignment=closeout,
        )


def test_pb_case_expansion_0c_bundle_rejects_missing_probe_contract_coverage() -> None:
    request, manifest, eligibility, control, guardrail = _load_a_rows()
    blueprint, evidence_pack, probe_contract, oracle_boundary, contamination_screen = (
        _load_b_rows()
    )
    lineage_registration, _, matrix_handoff, closeout = _load_c_rows()
    readiness_summary = ProgrambenchLocalCaseExpansionReadinessSummary.model_validate(
        _load_c_fixture(
            "programbench_local_case_expansion_v265_reject_readiness_missing_probe_contract.json"
        )
    )

    with pytest.raises(ValueError, match="cover all required C readiness kinds"):
        validate_pb_case_expansion_0c_closeout_bundle(
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
            lineage_registration=lineage_registration,
            readiness_summary=readiness_summary,
            matrix_candidate_handoff=matrix_handoff,
            family_closeout_alignment=closeout,
        )


def test_pb_case_expansion_0c_rejects_duplicate_logical_coverage_key() -> None:
    payload = _load_c_fixture(
        "programbench_local_case_expansion_readiness_summary_v265_reference.json"
    )
    duplicate_row = deepcopy(payload["coverage_summary_rows"][0])
    duplicate_row["coverage_summary_ref"] = (
        "coverage-summary:pb-case-expansion-0c:blueprint-copy"
    )
    payload["coverage_summary_rows"].insert(1, duplicate_row)

    with pytest.raises(ValidationError, match="duplicate logical coverage keys"):
        ProgrambenchLocalCaseExpansionReadinessSummary.model_validate(payload)


def test_pb_case_expansion_0c_rejects_blueprint_ready_and_blocked_overlap() -> None:
    payload = _load_c_fixture(
        "programbench_local_case_expansion_readiness_summary_v265_reference.json"
    )
    payload["blocked_blueprint_refs"] = ["case-blueprint:pb-case-expansion-0b:diagnostic"]

    with pytest.raises(ValidationError, match="blueprint refs must be disjoint"):
        ProgrambenchLocalCaseExpansionReadinessSummary.model_validate(payload)


def test_pb_case_expansion_0c_bundle_rejects_probe_contract_hash_mismatch() -> None:
    request, manifest, eligibility, control, guardrail = _load_a_rows()
    blueprint, evidence_pack, probe_contract, oracle_boundary, contamination_screen = (
        _load_b_rows()
    )
    _, readiness_summary, matrix_handoff, closeout = _load_c_rows()
    payload = _load_c_fixture("programbench_local_case_lineage_registration_v265_reference.json")
    payload["probe_contract_hash"] = (
        "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
    )
    lineage_registration = ProgrambenchLocalCaseLineageRegistration.model_validate(payload)

    with pytest.raises(ValueError, match="probe contract hash"):
        validate_pb_case_expansion_0c_closeout_bundle(
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
            lineage_registration=lineage_registration,
            readiness_summary=readiness_summary,
            matrix_candidate_handoff=matrix_handoff,
            family_closeout_alignment=closeout,
        )


def test_pb_case_expansion_0c_bundle_rejects_contamination_screen_hash_mismatch() -> None:
    request, manifest, eligibility, control, guardrail = _load_a_rows()
    blueprint, evidence_pack, probe_contract, oracle_boundary, contamination_screen = (
        _load_b_rows()
    )
    _, readiness_summary, matrix_handoff, closeout = _load_c_rows()
    payload = _load_c_fixture("programbench_local_case_lineage_registration_v265_reference.json")
    payload["contamination_screen_hash"] = (
        "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
    )
    lineage_registration = ProgrambenchLocalCaseLineageRegistration.model_validate(payload)

    with pytest.raises(ValueError, match="contamination screen hash"):
        validate_pb_case_expansion_0c_closeout_bundle(
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
            lineage_registration=lineage_registration,
            readiness_summary=readiness_summary,
            matrix_candidate_handoff=matrix_handoff,
            family_closeout_alignment=closeout,
        )


def test_pb_case_expansion_0c_rejects_soft_scoring_language() -> None:
    with pytest.raises(ValidationError, match="benchmark-like scoring"):
        ProgrambenchLocalCaseExpansionReadinessSummary.model_validate(
            _load_c_fixture(
                "programbench_local_case_expansion_v265_reject_ready_count_pass_rate.json"
            )
        )


def test_pb_case_expansion_0c_rejects_direct_matrix_inclusion_handoff() -> None:
    with pytest.raises(ValidationError):
        ProgrambenchLocalCaseMatrixCandidateHandoff.model_validate(
            _load_c_fixture(
                "programbench_local_case_expansion_v265_reject_handoff_direct_matrix_inclusion.json"
            )
        )


def test_pb_case_expansion_0c_rejects_incomplete_family_closeout() -> None:
    with pytest.raises(ValidationError):
        ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment.model_validate(
            _load_c_fixture(
                "programbench_local_case_expansion_v265_reject_closeout_missing_slice.json"
            )
        )


def test_pb_case_expansion_0c_schema_exports_are_current() -> None:
    export_schema_main()
    for _, authoritative_path, mirror_path in _schema_pairs():
        assert authoritative_path.read_text(encoding="utf-8") == mirror_path.read_text(
            encoding="utf-8"
        )
