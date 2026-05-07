from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_SCHEMA,
    PROGRAMBENCH_PROBE_EQUIVALENCE_AUDIT_SCHEMA,
    PROGRAMBENCH_REALIZATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_COMPARISON_PACKET_SCHEMA,
    ConceptRealizationRecord,
    ProgrambenchCleanroomEvidenceSourceIndex,
    ProgrambenchCleanroomReconstructionProfile,
    ProgrambenchLocalCleanroomFixture,
    ProgrambenchLocalCleanroomFixtureContract,
    ProgrambenchProbeEquivalenceAudit,
    ProgrambenchRealizationFamilyCloseoutAlignment,
    ProgrambenchReconstructionComparisonPacket,
    ProgrambenchReconstructionNonAuthorityGuardrail,
    ProgramOdeuConceptBoundarySeed,
    PythonRealizationWitnessTemplate,
    PythonReconstructionPlan,
    PythonReconstructionRealizationPack,
    validate_pb_py_0c_local_fixture_comparison_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(slice_ref: str) -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / slice_ref


def _load_fixture(slice_ref: str, name: str) -> dict[str, Any]:
    payload = json.loads((_fixture_root(slice_ref) / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture("vnext_plus242", name)


def _load_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture("vnext_plus243", name)


def _load_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture("vnext_plus244", name)


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
            PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_cleanroom_fixture.v1.json",
            root / "spec" / "programbench_local_cleanroom_fixture.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_COMPARISON_PACKET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_comparison_packet.v1.json",
            root / "spec" / "programbench_reconstruction_comparison_packet.schema.json",
        ),
        (
            PROGRAMBENCH_PROBE_EQUIVALENCE_AUDIT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_probe_equivalence_audit.v1.json",
            root / "spec" / "programbench_probe_equivalence_audit.schema.json",
        ),
        (
            PROGRAMBENCH_REALIZATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_realization_family_closeout_alignment.v1.json",
            root / "spec" / "programbench_realization_family_closeout_alignment.schema.json",
        ),
    ]


def _load_a_bundle() -> tuple[
    ProgrambenchCleanroomReconstructionProfile,
    ProgramOdeuConceptBoundarySeed,
    ProgrambenchCleanroomEvidenceSourceIndex,
    ProgrambenchReconstructionNonAuthorityGuardrail,
    ProgrambenchLocalCleanroomFixtureContract,
]:
    profile = ProgrambenchCleanroomReconstructionProfile.model_validate(
        _load_a_fixture("programbench_cleanroom_reconstruction_profile_v242_reference.json")
    )
    concept_seed = ProgramOdeuConceptBoundarySeed.model_validate(
        _load_a_fixture("program_odeu_concept_boundary_seed_v242_reference.json")
    )
    source_index = ProgrambenchCleanroomEvidenceSourceIndex.model_validate(
        _load_a_fixture("programbench_cleanroom_evidence_source_index_v242_reference.json")
    )
    guardrail = ProgrambenchReconstructionNonAuthorityGuardrail.model_validate(
        _load_a_fixture("programbench_reconstruction_non_authority_guardrail_v242_reference.json")
    )
    fixture_contract = ProgrambenchLocalCleanroomFixtureContract.model_validate(
        _load_a_fixture("programbench_local_cleanroom_fixture_contract_v242_reference.json")
    )
    return profile, concept_seed, source_index, guardrail, fixture_contract


def _load_b_bundle() -> tuple[
    list[ConceptRealizationRecord],
    PythonReconstructionRealizationPack,
    PythonReconstructionPlan,
    list[PythonRealizationWitnessTemplate],
]:
    realization_records = [
        ConceptRealizationRecord.model_validate(
            _load_b_fixture("concept_realization_record_v243_reference.json")
        )
    ]
    realization_pack = PythonReconstructionRealizationPack.model_validate(
        _load_b_fixture("python_reconstruction_realization_pack_v243_reference.json")
    )
    reconstruction_plan = PythonReconstructionPlan.model_validate(
        _load_b_fixture("python_reconstruction_plan_v243_reference.json")
    )
    witness_templates = [
        PythonRealizationWitnessTemplate.model_validate(
            _load_b_fixture("python_realization_witness_template_v243_reference.json")
        )
    ]
    return realization_records, realization_pack, reconstruction_plan, witness_templates


def _load_c_bundle() -> tuple[
    ProgrambenchLocalCleanroomFixture,
    ProgrambenchReconstructionComparisonPacket,
    ProgrambenchProbeEquivalenceAudit,
    ProgrambenchRealizationFamilyCloseoutAlignment,
]:
    local_fixture = ProgrambenchLocalCleanroomFixture.model_validate(
        _load_c_fixture("programbench_local_cleanroom_fixture_v244_reference.json")
    )
    comparison_packet = ProgrambenchReconstructionComparisonPacket.model_validate(
        _load_c_fixture("programbench_reconstruction_comparison_packet_v244_reference.json")
    )
    probe_audit = ProgrambenchProbeEquivalenceAudit.model_validate(
        _load_c_fixture("programbench_probe_equivalence_audit_v244_reference.json")
    )
    family_closeout = ProgrambenchRealizationFamilyCloseoutAlignment.model_validate(
        _load_c_fixture("programbench_realization_family_closeout_alignment_v244_reference.json")
    )
    return local_fixture, comparison_packet, probe_audit, family_closeout


def test_pb_py_0c_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()
    for schema_name, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))
        assert authoritative == mirror
        assert authoritative["properties"]["schema"]["const"] == schema_name


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_SCHEMA,
            "programbench_local_cleanroom_fixture.v1.json",
            "programbench_local_cleanroom_fixture_v244_reference.json",
            ProgrambenchLocalCleanroomFixture,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_COMPARISON_PACKET_SCHEMA,
            "programbench_reconstruction_comparison_packet.v1.json",
            "programbench_reconstruction_comparison_packet_v244_reference.json",
            ProgrambenchReconstructionComparisonPacket,
        ),
        (
            PROGRAMBENCH_PROBE_EQUIVALENCE_AUDIT_SCHEMA,
            "programbench_probe_equivalence_audit.v1.json",
            "programbench_probe_equivalence_audit_v244_reference.json",
            ProgrambenchProbeEquivalenceAudit,
        ),
        (
            PROGRAMBENCH_REALIZATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_realization_family_closeout_alignment.v1.json",
            "programbench_realization_family_closeout_alignment_v244_reference.json",
            ProgrambenchRealizationFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_py_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_c_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_py_0c_reference_bundle_preserves_local_fixture_boundary() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()
    local_fixture, comparison_packet, probe_audit, family_closeout = _load_c_bundle()

    validate_pb_py_0c_local_fixture_comparison_bundle(
        profile=profile,
        concept_seed=concept_seed,
        source_index=source_index,
        guardrail=guardrail,
        fixture_contract=fixture_contract,
        realization_records=realization_records,
        realization_pack=realization_pack,
        reconstruction_plan=reconstruction_plan,
        witness_templates=witness_templates,
        local_fixture=local_fixture,
        comparison_packet=comparison_packet,
        probe_audit=probe_audit,
        family_closeout=family_closeout,
    )

    assert local_fixture.fixture_origin_posture == "synthetic_local_fixture"
    assert comparison_packet.comparison_contamination_status == "same_condition_controls_closed"
    assert [row.lane_id for row in comparison_packet.comparison_lane_rows] == [
        "base_adeu_harness",
        "adeu_plus_conceptual_profile",
        "adeu_plus_conceptual_profile_plus_python_overlay",
    ]
    assert probe_audit.hidden_test_equivalence_posture == (
        "local_probe_pass_not_hidden_test_equivalence"
    )
    assert family_closeout.future_family_selection_status == (
        "no_future_family_selected_by_pb_py_0"
    )


def test_pb_py_0c_comparison_can_mark_contamination_without_clean_claim() -> None:
    payload = deepcopy(
        _load_c_fixture("programbench_reconstruction_comparison_packet_v244_reference.json")
    )
    payload["comparison_lane_rows"][1]["budget_policy"] = "shared-budget:pb-py-0c:expanded"
    payload["comparison_contamination_status"] = "contaminated_conditions_detected"

    comparison_packet = ProgrambenchReconstructionComparisonPacket.model_validate(payload)

    assert comparison_packet.comparison_contamination_status == "contaminated_conditions_detected"


def test_pb_py_0c_bundle_rejects_missing_released_b_pack_ref() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()
    local_fixture, comparison_packet, probe_audit, family_closeout = _load_c_bundle()
    comparison_payload = comparison_packet.model_dump(mode="json", by_alias=True)
    comparison_payload["realization_pack_refs"] = ["realization-pack:pb-py-0b:missing-pack"]
    comparison_packet = ProgrambenchReconstructionComparisonPacket.model_validate(
        comparison_payload
    )

    with pytest.raises(ValueError, match="realization pack refs missing"):
        validate_pb_py_0c_local_fixture_comparison_bundle(
            profile=profile,
            concept_seed=concept_seed,
            source_index=source_index,
            guardrail=guardrail,
            fixture_contract=fixture_contract,
            realization_records=realization_records,
            realization_pack=realization_pack,
            reconstruction_plan=reconstruction_plan,
            witness_templates=witness_templates,
            local_fixture=local_fixture,
            comparison_packet=comparison_packet,
            probe_audit=probe_audit,
            family_closeout=family_closeout,
        )


def test_pb_py_0c_bundle_rejects_missing_probe_audit_ref() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()
    local_fixture, comparison_packet, probe_audit, family_closeout = _load_c_bundle()
    comparison_payload = comparison_packet.model_dump(mode="json", by_alias=True)
    comparison_payload["local_probe_refs"] = ["probe:pb-py-0c:missing-probe"]
    comparison_packet = ProgrambenchReconstructionComparisonPacket.model_validate(
        comparison_payload
    )

    with pytest.raises(ValueError, match="local probe refs missing"):
        validate_pb_py_0c_local_fixture_comparison_bundle(
            profile=profile,
            concept_seed=concept_seed,
            source_index=source_index,
            guardrail=guardrail,
            fixture_contract=fixture_contract,
            realization_records=realization_records,
            realization_pack=realization_pack,
            reconstruction_plan=reconstruction_plan,
            witness_templates=witness_templates,
            local_fixture=local_fixture,
            comparison_packet=comparison_packet,
            probe_audit=probe_audit,
            family_closeout=family_closeout,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_fixture_v244_reject_official_programbench_task.json",
            ProgrambenchLocalCleanroomFixture,
        ),
        (
            "programbench_cleanroom_fixture_v244_reject_hidden_test_worker_visible.json",
            ProgrambenchLocalCleanroomFixture,
        ),
        (
            "programbench_cleanroom_fixture_v244_reject_internet_probe_command.json",
            ProgrambenchLocalCleanroomFixture,
        ),
        (
            "programbench_cleanroom_fixture_v244_reject_comparison_missing_controls.json",
            ProgrambenchReconstructionComparisonPacket,
        ),
        (
            "programbench_cleanroom_fixture_v244_reject_comparison_contaminated_clean.json",
            ProgrambenchReconstructionComparisonPacket,
        ),
        (
            "programbench_cleanroom_fixture_v244_reject_model_ranking.json",
            ProgrambenchReconstructionComparisonPacket,
        ),
        (
            "programbench_cleanroom_fixture_v244_reject_audit_hidden_test_equivalence.json",
            ProgrambenchProbeEquivalenceAudit,
        ),
        (
            "programbench_cleanroom_fixture_v244_reject_family_future_selection.json",
            ProgrambenchRealizationFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_py_0c_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_c_fixture(fixture_name))
