from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_RECONSTRUCTION_CANDIDATE_ARTIFACT_MANIFEST_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_LOCAL_RUN_TRACE_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_PROBE_RESULT_LOG_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_REMAND_CORRECTION_RECORD_SCHEMA,
    ProgrambenchReconstructionCandidateArtifactManifest,
    ProgrambenchReconstructionContextExclusionManifest,
    ProgrambenchReconstructionLocalRunTrace,
    ProgrambenchReconstructionProbeResultLog,
    ProgrambenchReconstructionRemandCorrectionRecord,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    ProgrambenchReconstructionWorkerContextPacket,
    ProgrambenchReconstructionWorkOrder,
    validate_pb_recon_0b_local_evidence_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_recon_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus248"


def _fixture_root_recon_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus249"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_recon_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_a(), name)


def _load_recon_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_b(), name)


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
            PROGRAMBENCH_RECONSTRUCTION_CANDIDATE_ARTIFACT_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_candidate_artifact_manifest.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_candidate_artifact_manifest.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_LOCAL_RUN_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_local_run_trace.v1.json",
            root / "spec" / "programbench_reconstruction_local_run_trace.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_PROBE_RESULT_LOG_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_probe_result_log.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_probe_result_log.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_REMAND_CORRECTION_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_remand_correction_record.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_remand_correction_record.schema.json",
        ),
    ]


def _load_recon_a_bundle() -> tuple[
    ProgrambenchReconstructionWorkOrder,
    ProgrambenchReconstructionWorkerContextPacket,
    ProgrambenchReconstructionContextExclusionManifest,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
]:
    return (
        ProgrambenchReconstructionWorkOrder.model_validate(
            _load_recon_a_fixture("programbench_reconstruction_work_order_v248_reference.json")
        ),
        ProgrambenchReconstructionWorkerContextPacket.model_validate(
            _load_recon_a_fixture(
                "programbench_reconstruction_worker_context_packet_v248_reference.json"
            )
        ),
        ProgrambenchReconstructionContextExclusionManifest.model_validate(
            _load_recon_a_fixture(
                "programbench_reconstruction_context_exclusion_manifest_v248_reference.json"
            )
        ),
        ProgrambenchReconstructionSandboxPolicy.model_validate(
            _load_recon_a_fixture(
                "programbench_reconstruction_sandbox_policy_v248_reference.json"
            )
        ),
        ProgrambenchReconstructionRunBudget.model_validate(
            _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
        ),
        ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail.model_validate(
            _load_recon_a_fixture(
                "programbench_reconstruction_workbench_non_authority_guardrail_v248_reference.json"
            )
        ),
    )


def _load_recon_b_bundle() -> tuple[
    ProgrambenchReconstructionCandidateArtifactManifest,
    list[ProgrambenchReconstructionLocalRunTrace],
    ProgrambenchReconstructionProbeResultLog,
    list[ProgrambenchReconstructionRemandCorrectionRecord],
]:
    return (
        ProgrambenchReconstructionCandidateArtifactManifest.model_validate(
            _load_recon_b_fixture(
                "programbench_reconstruction_candidate_artifact_manifest_v249_reference.json"
            )
        ),
        [
            ProgrambenchReconstructionLocalRunTrace.model_validate(
                _load_recon_b_fixture(
                    "programbench_reconstruction_local_run_trace_v249_reference.json"
                )
            )
        ],
        ProgrambenchReconstructionProbeResultLog.model_validate(
            _load_recon_b_fixture(
                "programbench_reconstruction_probe_result_log_v249_reference.json"
            )
        ),
        [
            ProgrambenchReconstructionRemandCorrectionRecord.model_validate(
                _load_recon_b_fixture(
                    "programbench_reconstruction_remand_correction_record_v249_reference.json"
                )
            )
        ],
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_RECONSTRUCTION_CANDIDATE_ARTIFACT_MANIFEST_SCHEMA,
            "programbench_reconstruction_candidate_artifact_manifest.v1.json",
            "programbench_reconstruction_candidate_artifact_manifest_v249_reference.json",
            ProgrambenchReconstructionCandidateArtifactManifest,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_LOCAL_RUN_TRACE_SCHEMA,
            "programbench_reconstruction_local_run_trace.v1.json",
            "programbench_reconstruction_local_run_trace_v249_reference.json",
            ProgrambenchReconstructionLocalRunTrace,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_PROBE_RESULT_LOG_SCHEMA,
            "programbench_reconstruction_probe_result_log.v1.json",
            "programbench_reconstruction_probe_result_log_v249_reference.json",
            ProgrambenchReconstructionProbeResultLog,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_REMAND_CORRECTION_RECORD_SCHEMA,
            "programbench_reconstruction_remand_correction_record.v1.json",
            "programbench_reconstruction_remand_correction_record_v249_reference.json",
            ProgrambenchReconstructionRemandCorrectionRecord,
        ),
    ],
)
def test_pb_recon_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_recon_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_recon_0b_reference_bundle_preserves_local_evidence_boundary() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    (
        candidate_artifact_manifest,
        local_run_traces,
        probe_result_log,
        remand_correction_records,
    ) = _load_recon_b_bundle()

    validate_pb_recon_0b_local_evidence_bundle(
        work_order=work_order,
        worker_context_packet=worker_context_packet,
        context_exclusion_manifest=context_exclusion_manifest,
        sandbox_policy=sandbox_policy,
        run_budget=run_budget,
        guardrail=guardrail,
        candidate_artifact_manifest=candidate_artifact_manifest,
        local_run_traces=local_run_traces,
        probe_result_log=probe_result_log,
        remand_correction_records=remand_correction_records,
    )

    assert candidate_artifact_manifest.submission_authority_posture == (
        "no_official_submission_authority_by_pb_recon_0b"
    )
    assert local_run_traces[0].hidden_test_posture == (
        "hidden_tests_not_visible_not_inference_evidence"
    )
    assert probe_result_log.probe_truth_posture == (
        "local_probe_evidence_only_not_benchmark_truth"
    )
    assert remand_correction_records[0].remand_reason_source == "local_probe_failure"


def test_pb_recon_0b_bundle_requires_released_work_order_ref() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    (
        candidate_artifact_manifest,
        local_run_traces,
        probe_result_log,
        remand_correction_records,
    ) = _load_recon_b_bundle()
    drifted_manifest = candidate_artifact_manifest.model_copy(
        update={"work_order_ref": "work-order:pb-recon-0a:missing"}
    )

    with pytest.raises(ValueError, match="candidate artifact manifest must reference"):
        validate_pb_recon_0b_local_evidence_bundle(
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
            candidate_artifact_manifest=drifted_manifest,
            local_run_traces=local_run_traces,
            probe_result_log=probe_result_log,
            remand_correction_records=remand_correction_records,
        )


def test_pb_recon_0b_bundle_rejects_candidate_artifact_budget_overrun() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    (
        candidate_artifact_manifest,
        local_run_traces,
        probe_result_log,
        remand_correction_records,
    ) = _load_recon_b_bundle()
    extra_file = candidate_artifact_manifest.generated_file_rows[0].model_copy(
        update={
            "generated_file_ref": "generated-file:pb-recon-0b:extra",
            "path_ref": "path:pb-recon-0a:candidate-output/extra.py",
        }
    )
    expanded_manifest = candidate_artifact_manifest.model_copy(
        update={
            "generated_file_rows": [
                extra_file,
                candidate_artifact_manifest.generated_file_rows[0],
            ]
        }
    )

    with pytest.raises(ValueError, match="exceeds candidate artifact budget"):
        validate_pb_recon_0b_local_evidence_bundle(
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
            candidate_artifact_manifest=expanded_manifest,
            local_run_traces=local_run_traces,
            probe_result_log=probe_result_log,
            remand_correction_records=remand_correction_records,
        )


def test_pb_recon_0b_bundle_rejects_candidate_artifact_outside_write_scope() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    (
        candidate_artifact_manifest,
        local_run_traces,
        probe_result_log,
        remand_correction_records,
    ) = _load_recon_b_bundle()
    out_of_scope_file = candidate_artifact_manifest.generated_file_rows[0].model_copy(
        update={"write_scope_ref": "workspace:host-secret-outside-sandbox"}
    )
    drifted_manifest = candidate_artifact_manifest.model_copy(
        update={"generated_file_rows": [out_of_scope_file]}
    )

    with pytest.raises(ValueError, match="write scopes must be allowed"):
        validate_pb_recon_0b_local_evidence_bundle(
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
            candidate_artifact_manifest=drifted_manifest,
            local_run_traces=local_run_traces,
            probe_result_log=probe_result_log,
            remand_correction_records=remand_correction_records,
        )


def test_pb_recon_0b_bundle_rejects_sandbox_violation_as_passed_probe() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    (
        candidate_artifact_manifest,
        local_run_traces,
        probe_result_log,
        remand_correction_records,
    ) = _load_recon_b_bundle()
    violated_trace = local_run_traces[0].model_copy(
        update={"sandbox_violation_refs": ["sandbox-violation:pb-recon-0b:network"]}
    )
    passed_row = probe_result_log.probe_result_rows[0].model_copy(
        update={"result_posture": "passed_local_probe"}
    )
    drifted_log = probe_result_log.model_copy(update={"probe_result_rows": [passed_row]})

    with pytest.raises(ValueError, match="sandbox violations cannot be treated"):
        validate_pb_recon_0b_local_evidence_bundle(
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
            candidate_artifact_manifest=candidate_artifact_manifest,
            local_run_traces=[violated_trace],
            probe_result_log=drifted_log,
            remand_correction_records=remand_correction_records,
        )


def test_pb_recon_0b_bundle_rejects_remand_budget_overrun() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    (
        candidate_artifact_manifest,
        local_run_traces,
        probe_result_log,
        remand_correction_records,
    ) = _load_recon_b_bundle()
    duplicate_remand = remand_correction_records[0].model_copy(
        update={"remand_correction_record_ref": "remand:pb-recon-0b:attempt-1-zz"}
    )

    with pytest.raises(ValueError, match="exceed released remand budget"):
        validate_pb_recon_0b_local_evidence_bundle(
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
            candidate_artifact_manifest=candidate_artifact_manifest,
            local_run_traces=local_run_traces,
            probe_result_log=probe_result_log,
            remand_correction_records=[
                remand_correction_records[0],
                duplicate_remand,
            ],
        )


def test_pb_recon_0b_candidate_manifest_rejects_duplicate_file_hash_rows() -> None:
    payload = _load_recon_b_fixture(
        "programbench_reconstruction_candidate_artifact_manifest_v249_reference.json"
    )
    duplicate_hash = dict(payload["generated_artifact_hash_rows"][0])
    duplicate_hash["artifact_hash_ref"] = "artifact-hash:pb-recon-0b:zz-duplicate"
    duplicate_hash["content_hash"] = (
        "sha256:7777777777777777777777777777777777777777777777777777777777777777"
    )
    payload["generated_artifact_hash_rows"].append(duplicate_hash)

    with pytest.raises(ValidationError, match="generated_artifact_hash_file_refs"):
        ProgrambenchReconstructionCandidateArtifactManifest.model_validate(payload)


def test_pb_recon_0b_local_run_trace_requires_argv_rows_sorted_by_index() -> None:
    payload = _load_recon_b_fixture(
        "programbench_reconstruction_local_run_trace_v249_reference.json"
    )
    payload["command_argv_rows"][0]["arg_index"] = 1
    payload["command_argv_rows"][1]["arg_index"] = 0

    with pytest.raises(ValidationError, match="sorted by arg_index"):
        ProgrambenchReconstructionLocalRunTrace.model_validate(payload)


def test_pb_recon_0b_remand_record_allows_no_correction_outcome_without_attempts() -> None:
    payload = _load_recon_b_fixture(
        "programbench_reconstruction_remand_correction_record_v249_reference.json"
    )
    payload["correction_attempt_rows"] = []
    payload["remand_outcome_posture"] = "remand_recorded_no_correction"

    record = ProgrambenchReconstructionRemandCorrectionRecord.model_validate(payload)

    assert record.correction_attempt_rows == []
    assert record.remand_outcome_posture == "remand_recorded_no_correction"


def test_pb_recon_0b_corrected_remand_record_requires_correction_attempts() -> None:
    payload = _load_recon_b_fixture(
        "programbench_reconstruction_remand_correction_record_v249_reference.json"
    )
    payload["correction_attempt_rows"] = []

    with pytest.raises(ValidationError, match="require correction attempts"):
        ProgrambenchReconstructionRemandCorrectionRecord.model_validate(payload)


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_reconstruction_v249_reject_candidate_official_submission.json",
            ProgrambenchReconstructionCandidateArtifactManifest,
        ),
        (
            "programbench_cleanroom_reconstruction_v249_reject_local_run_not_run_plan_only.json",
            ProgrambenchReconstructionLocalRunTrace,
        ),
        (
            "programbench_cleanroom_reconstruction_v249_reject_probe_hidden_test_equivalence.json",
            ProgrambenchReconstructionProbeResultLog,
        ),
        (
            "programbench_cleanroom_reconstruction_v249_reject_probe_benchmark_truth.json",
            ProgrambenchReconstructionProbeResultLog,
        ),
        (
            "programbench_cleanroom_reconstruction_v249_reject_remand_hidden_test_failure.json",
            ProgrambenchReconstructionRemandCorrectionRecord,
        ),
        (
            "programbench_cleanroom_reconstruction_v249_reject_remand_case_packet_mutation.json",
            ProgrambenchReconstructionRemandCorrectionRecord,
        ),
    ],
)
def test_pb_recon_0b_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_recon_b_fixture(fixture_name))


def test_pb_recon_0b_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
