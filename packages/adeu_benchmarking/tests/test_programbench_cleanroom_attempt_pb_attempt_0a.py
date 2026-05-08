from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_DISPATCH_PREFLIGHT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REQUEST_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INPUT_PACKET_SCHEMA,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptExcludedRefSummaryRow,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    ProgrambenchReconstructionContextExclusionManifest,
    ProgrambenchReconstructionResultSummary,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
    ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    ProgrambenchReconstructionWorkerContextPacket,
    ProgrambenchReconstructionWorkOrder,
    validate_pb_attempt_0a_attempt_bundle,
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


def _fixture_root_recon_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus250"


def _fixture_root_attempt_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus251"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_recon_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_a(), name)


def _load_recon_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_c(), name)


def _load_attempt_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_a(), name)


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
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REQUEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_request.v1.json",
            root / "spec" / "programbench_reconstruction_attempt_request.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INPUT_PACKET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_worker_input_packet.v1.json",
            root / "spec" / "programbench_reconstruction_attempt_worker_input_packet.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_DISPATCH_PREFLIGHT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_dispatch_preflight.v1.json",
            root / "spec" / "programbench_reconstruction_attempt_dispatch_preflight.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_non_authority_guardrail.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_attempt_non_authority_guardrail.schema.json",
        ),
    ]


def _load_workbench_rows() -> tuple[
    ProgrambenchReconstructionWorkOrder,
    ProgrambenchReconstructionWorkerContextPacket,
    ProgrambenchReconstructionContextExclusionManifest,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    ProgrambenchReconstructionResultSummary,
    ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
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
            _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
        ),
        ProgrambenchReconstructionRunBudget.model_validate(
            _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
        ),
        ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail.model_validate(
            _load_recon_a_fixture(
                "programbench_reconstruction_workbench_non_authority_guardrail_v248_reference.json"
            )
        ),
        ProgrambenchReconstructionResultSummary.model_validate(
            _load_recon_c_fixture("programbench_reconstruction_result_summary_v250_reference.json")
        ),
        ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment.model_validate(
            _load_recon_c_fixture(
                "programbench_reconstruction_workbench_family_closeout_alignment_v250_reference.json"
            )
        ),
    )


def _load_attempt_rows() -> tuple[
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
]:
    return (
        ProgrambenchReconstructionAttemptRequest.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_request_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptWorkerInputPacket.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_worker_input_packet_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptDispatchPreflight.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptNonAuthorityGuardrail.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_non_authority_guardrail_v251_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REQUEST_SCHEMA,
            "programbench_reconstruction_attempt_request.v1.json",
            "programbench_reconstruction_attempt_request_v251_reference.json",
            ProgrambenchReconstructionAttemptRequest,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INPUT_PACKET_SCHEMA,
            "programbench_reconstruction_attempt_worker_input_packet.v1.json",
            "programbench_reconstruction_attempt_worker_input_packet_v251_reference.json",
            ProgrambenchReconstructionAttemptWorkerInputPacket,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_DISPATCH_PREFLIGHT_SCHEMA,
            "programbench_reconstruction_attempt_dispatch_preflight.v1.json",
            "programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json",
            ProgrambenchReconstructionAttemptDispatchPreflight,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_reconstruction_attempt_non_authority_guardrail.v1.json",
            "programbench_reconstruction_attempt_non_authority_guardrail_v251_reference.json",
            ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_attempt_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_attempt_a_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_attempt_0a_reference_bundle_preserves_non_dispatch_boundary() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        workbench_guardrail,
        result_summary,
        workbench_family_closeout,
    ) = _load_workbench_rows()
    (
        attempt_request,
        worker_input_packet,
        dispatch_preflight,
        guardrail,
    ) = _load_attempt_rows()

    validate_pb_attempt_0a_attempt_bundle(
        work_order=work_order,
        worker_context_packet=worker_context_packet,
        context_exclusion_manifest=context_exclusion_manifest,
        sandbox_policy=sandbox_policy,
        run_budget=run_budget,
        workbench_guardrail=workbench_guardrail,
        result_summary=result_summary,
        workbench_family_closeout=workbench_family_closeout,
        attempt_request=attempt_request,
        worker_input_packet=worker_input_packet,
        dispatch_preflight=dispatch_preflight,
        guardrail=guardrail,
    )

    assert attempt_request.dispatch_authority_posture == (
        "no_worker_dispatch_authority_granted_by_pb_attempt_0a"
    )
    assert dispatch_preflight.preflight_scope_posture == ("eligibility_review_only_no_invocation")
    assert set(dispatch_preflight.budget_enforcement_requirement_refs) == {
        "bounded_filesystem_budget_declared",
        "bounded_timeout_budget_declared",
        "bounded_token_budget_declared",
        "max_candidate_artifact_count_declared",
        "max_local_run_count_declared",
        "max_probe_run_count_declared",
        "max_remand_count_declared",
    }
    assert worker_input_packet.worker_visible_ref_count == 14
    assert worker_input_packet.input_materialization_posture == (
        "no_candidate_materialization_by_pb_attempt_0a"
    )
    assert guardrail.future_family_selection_posture == (
        "no_future_family_selected_by_pb_attempt_0a"
    )


def test_pb_attempt_0a_bundle_rejects_excluded_ref_in_worker_input() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        workbench_guardrail,
        result_summary,
        workbench_family_closeout,
    ) = _load_workbench_rows()
    (
        attempt_request,
        _worker_input_packet,
        dispatch_preflight,
        guardrail,
    ) = _load_attempt_rows()
    worker_input_packet = ProgrambenchReconstructionAttemptWorkerInputPacket.model_validate(
        _load_attempt_a_fixture(
            "programbench_cleanroom_attempt_v251_reject_worker_input_excluded_ref.json"
        )
    )
    leaking_context = worker_context_packet.model_copy(
        update={
            "worker_visible_source_refs": sorted(
                [
                    *worker_context_packet.worker_visible_source_refs,
                    "store:pb-adapter-0a:original-source",
                ]
            )
        }
    )

    with pytest.raises(ValueError, match="auditor-only or forbidden refs"):
        validate_pb_attempt_0a_attempt_bundle(
            work_order=work_order,
            worker_context_packet=leaking_context,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            workbench_guardrail=workbench_guardrail,
            result_summary=result_summary,
            workbench_family_closeout=workbench_family_closeout,
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
        )


def test_pb_attempt_0a_bundle_rejects_unreleased_workbench_guardrail_ref() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        workbench_guardrail,
        result_summary,
        workbench_family_closeout,
    ) = _load_workbench_rows()
    (
        attempt_request,
        worker_input_packet,
        dispatch_preflight,
        guardrail,
    ) = _load_attempt_rows()
    drifted_work_order = work_order.model_copy(
        update={"guardrail_refs": ["guardrail:pb-recon-0a:stale"]}
    )

    with pytest.raises(ValueError, match="released workbench guardrail"):
        validate_pb_attempt_0a_attempt_bundle(
            work_order=drifted_work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            workbench_guardrail=workbench_guardrail,
            result_summary=result_summary,
            workbench_family_closeout=workbench_family_closeout,
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
        )


def test_pb_attempt_0a_bundle_rejects_local_accepted_result_for_remand_attempt() -> None:
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        workbench_guardrail,
        result_summary,
        workbench_family_closeout,
    ) = _load_workbench_rows()
    attempt_request = ProgrambenchReconstructionAttemptRequest.model_validate(
        _load_attempt_a_fixture(
            "programbench_cleanroom_attempt_v251_reject_local_accepted_remand_request.json"
        )
    )
    (
        _attempt_request,
        worker_input_packet,
        dispatch_preflight,
        guardrail,
    ) = _load_attempt_rows()
    accepted_summary = result_summary.model_copy(
        update={
            "carried_blocker_refs": [],
            "local_acceptance_scope_posture": (
                "accepted_only_against_declared_local_probe_set_not_hidden_tests"
            ),
            "result_posture": "local_accepted",
        }
    )

    with pytest.raises(ValueError, match="compatible PB-RECON-0 result summary posture"):
        validate_pb_attempt_0a_attempt_bundle(
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            workbench_guardrail=workbench_guardrail,
            result_summary=accepted_summary,
            workbench_family_closeout=workbench_family_closeout,
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_attempt_v251_reject_dispatch_authority.json",
            ProgrambenchReconstructionAttemptDispatchPreflight,
        ),
        (
            "programbench_cleanroom_attempt_v251_reject_official_programbench_authority.json",
            ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
        ),
        (
            "programbench_cleanroom_attempt_v251_reject_future_slice_artifact_kind.json",
            ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_attempt_0a_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_attempt_a_fixture(fixture_name))


def test_pb_attempt_0a_rejects_content_bearing_exclusion_summary() -> None:
    with pytest.raises(ValidationError):
        ProgrambenchReconstructionAttemptExcludedRefSummaryRow.model_validate(
            _load_attempt_a_fixture(
                "programbench_cleanroom_attempt_v251_reject_exclusion_summary_source_name.json"
            )
        )


def test_pb_attempt_0a_rejects_preflight_without_budget_enforcement_refs() -> None:
    payload = _load_attempt_a_fixture(
        "programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json"
    )
    payload.pop("budget_enforcement_requirement_refs")

    with pytest.raises(ValidationError):
        ProgrambenchReconstructionAttemptDispatchPreflight.model_validate(payload)


def test_pb_attempt_0a_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
