from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_ADAPTER_HANDOFF_SCHEMA,
    PROGRAMBENCH_ADAPTER_READINESS_SUMMARY_SCHEMA,
    PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_CASE_PACKET_SCHEMA,
    ProgrambenchAdapterHandoff,
    ProgrambenchAdapterNonAuthorityGuardrail,
    ProgrambenchAdapterProbePlan,
    ProgrambenchAdapterReadinessSummary,
    ProgrambenchAdapterWorkerAccessContract,
    ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
    ProgrambenchCleanroomTaskIntake,
    ProgrambenchFilesystemSideEffectObservation,
    ProgrambenchIOArtifactObservationIndex,
    ProgrambenchProbeObservationLog,
    ProgrambenchReconstructionCasePacket,
    ProgrambenchTaskArtifactManifest,
    ProgrambenchTaskVisibilityManifest,
    validate_pb_adapter_0c_case_packet_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus245"


def _fixture_root_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus246"


def _fixture_root_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus247"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_a(), name)


def _load_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_b(), name)


def _load_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_c(), name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_benchmarking" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = _repo_root()
    return [
        (
            PROGRAMBENCH_RECONSTRUCTION_CASE_PACKET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_case_packet.v1.json",
            root / "spec" / "programbench_reconstruction_case_packet.schema.json",
        ),
        (
            PROGRAMBENCH_ADAPTER_READINESS_SUMMARY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_readiness_summary.v1.json",
            root / "spec" / "programbench_adapter_readiness_summary.schema.json",
        ),
        (
            PROGRAMBENCH_ADAPTER_HANDOFF_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_handoff.v1.json",
            root / "spec" / "programbench_adapter_handoff.schema.json",
        ),
        (
            PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_cleanroom_adapter_family_closeout_alignment.v1.json",
            root / "spec" / "programbench_cleanroom_adapter_family_closeout_alignment.schema.json",
        ),
    ]


def _load_a_bundle() -> tuple[
    ProgrambenchCleanroomTaskIntake,
    ProgrambenchTaskArtifactManifest,
    ProgrambenchTaskVisibilityManifest,
    ProgrambenchAdapterWorkerAccessContract,
    ProgrambenchAdapterNonAuthorityGuardrail,
]:
    return (
        ProgrambenchCleanroomTaskIntake.model_validate(
            _load_a_fixture("programbench_cleanroom_task_intake_v245_reference.json")
        ),
        ProgrambenchTaskArtifactManifest.model_validate(
            _load_a_fixture("programbench_task_artifact_manifest_v245_reference.json")
        ),
        ProgrambenchTaskVisibilityManifest.model_validate(
            _load_a_fixture("programbench_task_visibility_manifest_v245_reference.json")
        ),
        ProgrambenchAdapterWorkerAccessContract.model_validate(
            _load_a_fixture("programbench_adapter_worker_access_contract_v245_reference.json")
        ),
        ProgrambenchAdapterNonAuthorityGuardrail.model_validate(
            _load_a_fixture("programbench_adapter_non_authority_guardrail_v245_reference.json")
        ),
    )


def _load_b_bundle() -> tuple[
    ProgrambenchAdapterProbePlan,
    list[ProgrambenchProbeObservationLog],
    ProgrambenchIOArtifactObservationIndex,
    list[ProgrambenchFilesystemSideEffectObservation],
]:
    return (
        ProgrambenchAdapterProbePlan.model_validate(
            _load_b_fixture("programbench_adapter_probe_plan_v246_reference.json")
        ),
        [
            ProgrambenchProbeObservationLog.model_validate(
                _load_b_fixture("programbench_probe_observation_log_v246_reference.json")
            )
        ],
        ProgrambenchIOArtifactObservationIndex.model_validate(
            _load_b_fixture("programbench_io_artifact_observation_index_v246_reference.json")
        ),
        [
            ProgrambenchFilesystemSideEffectObservation.model_validate(
                _load_b_fixture(
                    "programbench_filesystem_side_effect_observation_v246_reference.json"
                )
            )
        ],
    )


def _load_c_bundle() -> tuple[
    ProgrambenchReconstructionCasePacket,
    ProgrambenchAdapterReadinessSummary,
    ProgrambenchAdapterHandoff,
    ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchReconstructionCasePacket.model_validate(
            _load_c_fixture("programbench_reconstruction_case_packet_v247_reference.json")
        ),
        ProgrambenchAdapterReadinessSummary.model_validate(
            _load_c_fixture("programbench_adapter_readiness_summary_v247_reference.json")
        ),
        ProgrambenchAdapterHandoff.model_validate(
            _load_c_fixture("programbench_adapter_handoff_v247_reference.json")
        ),
        ProgrambenchCleanroomAdapterFamilyCloseoutAlignment.model_validate(
            _load_c_fixture(
                "programbench_cleanroom_adapter_family_closeout_alignment_v247_reference.json"
            )
        ),
    )


def _assert_pb_adapter_0c_bundle_rejects_case_payload(
    case_payload: dict[str, Any],
    *,
    match: str,
) -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    _, readiness_summary, handoff, family_closeout = _load_c_bundle()
    case_packet = ProgrambenchReconstructionCasePacket.model_validate(case_payload)

    with pytest.raises(ValueError, match=match):
        validate_pb_adapter_0c_case_packet_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
            probe_plan=probe_plan,
            observation_logs=observation_logs,
            io_artifact_index=io_artifact_index,
            filesystem_side_effect_observations=filesystem_side_effect_observations,
            case_packet=case_packet,
            readiness_summary=readiness_summary,
            handoff=handoff,
            family_closeout=family_closeout,
        )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_RECONSTRUCTION_CASE_PACKET_SCHEMA,
            "programbench_reconstruction_case_packet.v1.json",
            "programbench_reconstruction_case_packet_v247_reference.json",
            ProgrambenchReconstructionCasePacket,
        ),
        (
            PROGRAMBENCH_ADAPTER_READINESS_SUMMARY_SCHEMA,
            "programbench_adapter_readiness_summary.v1.json",
            "programbench_adapter_readiness_summary_v247_reference.json",
            ProgrambenchAdapterReadinessSummary,
        ),
        (
            PROGRAMBENCH_ADAPTER_HANDOFF_SCHEMA,
            "programbench_adapter_handoff.v1.json",
            "programbench_adapter_handoff_v247_reference.json",
            ProgrambenchAdapterHandoff,
        ),
        (
            PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_cleanroom_adapter_family_closeout_alignment.v1.json",
            "programbench_cleanroom_adapter_family_closeout_alignment_v247_reference.json",
            ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_adapter_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_c_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_adapter_0c_reference_bundle_preserves_case_packet_boundary() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    case_packet, readiness_summary, handoff, family_closeout = _load_c_bundle()

    validate_pb_adapter_0c_case_packet_bundle(
        task_intake=task_intake,
        artifact_manifest=artifact_manifest,
        visibility_manifest=visibility_manifest,
        worker_access_contract=worker_access_contract,
        guardrail=guardrail,
        probe_plan=probe_plan,
        observation_logs=observation_logs,
        io_artifact_index=io_artifact_index,
        filesystem_side_effect_observations=filesystem_side_effect_observations,
        case_packet=case_packet,
        readiness_summary=readiness_summary,
        handoff=handoff,
        family_closeout=family_closeout,
    )

    assert case_packet.case_packet_scope_posture == "released_adapter_refs_packet_only"
    assert readiness_summary.contamination_status == "clean"
    assert readiness_summary.readiness_posture == (
        "ready_for_later_cleanroom_reconstruction_review"
    )
    assert handoff.execution_authority_posture == (
        "no_execution_authority_granted_by_pb_adapter_0c"
    )
    assert family_closeout.closed_slice_refs == [
        "PB-ADAPTER-0-A",
        "PB-ADAPTER-0-B",
        "PB-ADAPTER-0-C",
    ]


def test_pb_adapter_0c_bundle_rejects_unreleased_visibility_manifest_ref() -> None:
    _assert_pb_adapter_0c_bundle_rejects_case_payload(
        _load_c_fixture("programbench_cleanroom_adapter_v247_reject_missing_visibility_manifest.json"),
        match="released visibility manifest",
    )


def test_pb_adapter_0c_bundle_rejects_missing_readiness_coverage() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    case_packet, readiness_summary, handoff, family_closeout = _load_c_bundle()
    drifted_summary = readiness_summary.model_copy(
        update={"coverage_summary_rows": readiness_summary.coverage_summary_rows[:1]}
    )

    with pytest.raises(ValueError, match="readiness coverage missing required ref/kind pairs"):
        validate_pb_adapter_0c_case_packet_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
            probe_plan=probe_plan,
            observation_logs=observation_logs,
            io_artifact_index=io_artifact_index,
            filesystem_side_effect_observations=filesystem_side_effect_observations,
            case_packet=case_packet,
            readiness_summary=drifted_summary,
            handoff=handoff,
            family_closeout=family_closeout,
        )


def test_pb_adapter_0c_bundle_rejects_wrong_readiness_coverage_kind() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    case_packet, readiness_summary, handoff, family_closeout = _load_c_bundle()
    drifted_rows = list(readiness_summary.coverage_summary_rows)
    drifted_rows[1] = drifted_rows[1].model_copy(
        update={"coverage_kind": "visibility_manifest"}
    )
    drifted_summary = readiness_summary.model_copy(
        update={"coverage_summary_rows": drifted_rows}
    )

    with pytest.raises(ValueError, match="readiness coverage missing required ref/kind pairs"):
        validate_pb_adapter_0c_case_packet_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
            probe_plan=probe_plan,
            observation_logs=observation_logs,
            io_artifact_index=io_artifact_index,
            filesystem_side_effect_observations=filesystem_side_effect_observations,
            case_packet=case_packet,
            readiness_summary=drifted_summary,
            handoff=handoff,
            family_closeout=family_closeout,
        )


def test_pb_adapter_0c_readiness_rejects_sparse_contamination_status() -> None:
    payload = _load_c_fixture("programbench_adapter_readiness_summary_v247_reference.json")
    payload["contamination_status"] = "forbidden_source_exposure"
    payload["forbidden_evidence_exposure_posture"] = "forbidden_evidence_exposure_detected"
    payload["forbidden_source_exposure_refs"] = ["store:original-source"]
    payload["readiness_posture"] = "blocked_by_forbidden_evidence_exposure"

    with pytest.raises(ValidationError, match="must carry contamination rows"):
        ProgrambenchAdapterReadinessSummary.model_validate(payload)


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_adapter_v247_reject_readiness_forbidden_exposure.json",
            ProgrambenchAdapterReadinessSummary,
        ),
        (
            "programbench_cleanroom_adapter_v247_reject_warning_hidden_test_violation.json",
            ProgrambenchAdapterReadinessSummary,
        ),
        (
            "programbench_cleanroom_adapter_v247_reject_handoff_execution_authority.json",
            ProgrambenchAdapterHandoff,
        ),
        (
            "programbench_cleanroom_adapter_v247_reject_family_future_selection.json",
            ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_adapter_0c_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_c_fixture(fixture_name))


def test_pb_adapter_0c_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
