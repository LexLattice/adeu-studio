from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_RECONSTRUCTION_EQUIVALENCE_AUDIT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_HANDOFF_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_RESULT_SUMMARY_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    ProgrambenchReconstructionCandidateArtifactManifest,
    ProgrambenchReconstructionContextExclusionManifest,
    ProgrambenchReconstructionEquivalenceAudit,
    ProgrambenchReconstructionHandoff,
    ProgrambenchReconstructionLocalRunTrace,
    ProgrambenchReconstructionProbeResultLog,
    ProgrambenchReconstructionRemandCorrectionRecord,
    ProgrambenchReconstructionResultSummary,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
    ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    ProgrambenchReconstructionWorkerContextPacket,
    ProgrambenchReconstructionWorkOrder,
    validate_pb_recon_0c_local_audit_bundle,
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


def _fixture_root_recon_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus250"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_recon_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_a(), name)


def _load_recon_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_b(), name)


def _load_recon_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_c(), name)


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
            PROGRAMBENCH_RECONSTRUCTION_EQUIVALENCE_AUDIT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_equivalence_audit.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_equivalence_audit.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_RESULT_SUMMARY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_result_summary.v1.json",
            root / "spec" / "programbench_reconstruction_result_summary.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_HANDOFF_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_handoff.v1.json",
            root / "spec" / "programbench_reconstruction_handoff.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_workbench_family_closeout_alignment.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_workbench_family_closeout_alignment.schema.json",
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


def _load_recon_c_bundle() -> tuple[
    ProgrambenchReconstructionEquivalenceAudit,
    ProgrambenchReconstructionResultSummary,
    ProgrambenchReconstructionHandoff,
    ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchReconstructionEquivalenceAudit.model_validate(
            _load_recon_c_fixture(
                "programbench_reconstruction_equivalence_audit_v250_reference.json"
            )
        ),
        ProgrambenchReconstructionResultSummary.model_validate(
            _load_recon_c_fixture(
                "programbench_reconstruction_result_summary_v250_reference.json"
            )
        ),
        ProgrambenchReconstructionHandoff.model_validate(
            _load_recon_c_fixture("programbench_reconstruction_handoff_v250_reference.json")
        ),
        ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment.model_validate(
            _load_recon_c_fixture(
                "programbench_reconstruction_workbench_family_closeout_alignment_v250_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_RECONSTRUCTION_EQUIVALENCE_AUDIT_SCHEMA,
            "programbench_reconstruction_equivalence_audit.v1.json",
            "programbench_reconstruction_equivalence_audit_v250_reference.json",
            ProgrambenchReconstructionEquivalenceAudit,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_RESULT_SUMMARY_SCHEMA,
            "programbench_reconstruction_result_summary.v1.json",
            "programbench_reconstruction_result_summary_v250_reference.json",
            ProgrambenchReconstructionResultSummary,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_HANDOFF_SCHEMA,
            "programbench_reconstruction_handoff.v1.json",
            "programbench_reconstruction_handoff_v250_reference.json",
            ProgrambenchReconstructionHandoff,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_reconstruction_workbench_family_closeout_alignment.v1.json",
            "programbench_reconstruction_workbench_family_closeout_alignment_v250_reference.json",
            ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_recon_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_recon_c_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_recon_0c_reference_bundle_records_local_remand_only() -> None:
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
    (
        equivalence_audit,
        result_summary,
        handoff,
        family_closeout,
    ) = _load_recon_c_bundle()

    validate_pb_recon_0c_local_audit_bundle(
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
        equivalence_audit=equivalence_audit,
        result_summary=result_summary,
        handoff=handoff,
        family_closeout=family_closeout,
    )

    assert equivalence_audit.hidden_test_equivalence_posture == "not_hidden_test_equivalence"
    assert result_summary.result_posture == "local_remand_required"
    assert result_summary.benchmark_truth_posture == "not_benchmark_truth"
    assert handoff.handoff_target == "blocked_no_handoff"
    assert family_closeout.closed_family_ref == "PB-RECON-0"


def test_pb_recon_0c_accepts_synthetic_local_accepted_when_all_gates_clean() -> None:
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
    (
        equivalence_audit,
        result_summary,
        handoff,
        family_closeout,
    ) = _load_recon_c_bundle()
    passed_probe_row = probe_result_log.probe_result_rows[0].model_copy(
        update={"result_posture": "passed_local_probe"}
    )
    passed_probe_log = probe_result_log.model_copy(
        update={
            "exit_code_posture": "exit_code_expectation_satisfied",
            "filesystem_side_effect_posture": "not_applicable_with_reason",
            "probe_result_rows": [passed_probe_row],
            "stdout_stderr_separation_posture": "stdout_stderr_separation_satisfied",
        }
    )
    passed_audit_row = equivalence_audit.positive_probe_rows[0].model_copy(
        update={"probe_pass_posture": "passed_local_probe"}
    )
    passed_audit = equivalence_audit.model_copy(
        update={
            "local_equivalence_posture": "local_equivalence_satisfied",
            "positive_probe_rows": [passed_audit_row],
        }
    )
    accepted_summary = result_summary.model_copy(
        update={
            "carried_blocker_refs": [],
            "local_acceptance_scope_posture": (
                "accepted_only_against_declared_local_probe_set_not_hidden_tests"
            ),
            "result_posture": "local_accepted",
        }
    )
    accepted_handoff = handoff.model_copy(
        update={
            "handoff_sequence_posture": "handoff_pressure_only_no_selection",
            "handoff_target": "future_cleanroom_reconstruction_review",
        }
    )

    validate_pb_recon_0c_local_audit_bundle(
        work_order=work_order,
        worker_context_packet=worker_context_packet,
        context_exclusion_manifest=context_exclusion_manifest,
        sandbox_policy=sandbox_policy,
        run_budget=run_budget,
        guardrail=guardrail,
        candidate_artifact_manifest=candidate_artifact_manifest,
        local_run_traces=local_run_traces,
        probe_result_log=passed_probe_log,
        remand_correction_records=remand_correction_records,
        equivalence_audit=passed_audit,
        result_summary=accepted_summary,
        handoff=accepted_handoff,
        family_closeout=family_closeout,
    )


def test_pb_recon_0c_local_accepted_requires_satisfied_local_audit() -> None:
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
    (
        equivalence_audit,
        result_summary,
        handoff,
        family_closeout,
    ) = _load_recon_c_bundle()
    invalid_summary = result_summary.model_copy(
        update={
            "carried_blocker_refs": [],
            "local_acceptance_scope_posture": (
                "accepted_only_against_declared_local_probe_set_not_hidden_tests"
            ),
            "result_posture": "local_accepted",
        }
    )

    with pytest.raises(ValueError, match="satisfied local equivalence audit"):
        validate_pb_recon_0c_local_audit_bundle(
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
            equivalence_audit=equivalence_audit,
            result_summary=invalid_summary,
            handoff=handoff,
            family_closeout=family_closeout,
        )


def test_pb_recon_0c_result_summary_must_match_trace_sandbox_violations() -> None:
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
    (
        equivalence_audit,
        result_summary,
        handoff,
        family_closeout,
    ) = _load_recon_c_bundle()
    violated_trace = local_run_traces[0].model_copy(
        update={"sandbox_violation_refs": ["sandbox-violation:pb-recon-0c:network"]}
    )

    with pytest.raises(ValueError, match="sandbox violations must match"):
        validate_pb_recon_0c_local_audit_bundle(
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
            candidate_artifact_manifest=candidate_artifact_manifest,
            local_run_traces=[violated_trace],
            probe_result_log=probe_result_log,
            remand_correction_records=remand_correction_records,
            equivalence_audit=equivalence_audit,
            result_summary=result_summary,
            handoff=handoff,
            family_closeout=family_closeout,
        )


def test_pb_recon_0c_equivalence_audit_must_cover_released_probe_log() -> None:
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
    (
        equivalence_audit,
        result_summary,
        handoff,
        family_closeout,
    ) = _load_recon_c_bundle()
    drifted_audit = equivalence_audit.model_copy(
        update={"probe_result_log_refs": ["probe-result-log:pb-recon-0c:unreleased"]}
    )

    with pytest.raises(ValueError, match="released probe result log"):
        validate_pb_recon_0c_local_audit_bundle(
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
            equivalence_audit=drifted_audit,
            result_summary=result_summary,
            handoff=handoff,
            family_closeout=family_closeout,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_reconstruction_v250_reject_equivalence_hidden_test_equivalence.json",
            ProgrambenchReconstructionEquivalenceAudit,
        ),
        (
            "programbench_cleanroom_reconstruction_v250_reject_result_benchmark_truth.json",
            ProgrambenchReconstructionResultSummary,
        ),
        (
            "programbench_cleanroom_reconstruction_v250_reject_result_model_ranking.json",
            ProgrambenchReconstructionResultSummary,
        ),
        (
            "programbench_cleanroom_reconstruction_v250_reject_result_official_submission.json",
            ProgrambenchReconstructionResultSummary,
        ),
        (
            "programbench_cleanroom_reconstruction_v250_reject_handoff_official_authority.json",
            ProgrambenchReconstructionHandoff,
        ),
        (
            "programbench_cleanroom_reconstruction_v250_reject_family_closeout_future_family_selection.json",
            ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_recon_0c_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_recon_c_fixture(fixture_name))


def test_pb_recon_0c_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
