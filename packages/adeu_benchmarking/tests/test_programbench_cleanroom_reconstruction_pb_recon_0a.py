from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_RECONSTRUCTION_CONTEXT_EXCLUSION_MANIFEST_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_RUN_BUDGET_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_SANDBOX_POLICY_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORK_ORDER_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORKER_CONTEXT_PACKET_SCHEMA,
    ProgrambenchAdapterHandoff,
    ProgrambenchAdapterReadinessSummary,
    ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
    ProgrambenchReconstructionCasePacket,
    ProgrambenchReconstructionContextExclusionManifest,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    ProgrambenchReconstructionWorkerContextPacket,
    ProgrambenchReconstructionWorkOrder,
    validate_pb_recon_0a_work_order_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus247"


def _fixture_root_recon_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus248"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_c(), name)


def _load_recon_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_a(), name)


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
            PROGRAMBENCH_RECONSTRUCTION_WORK_ORDER_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_work_order.v1.json",
            root / "spec" / "programbench_reconstruction_work_order.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_WORKER_CONTEXT_PACKET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_worker_context_packet.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_worker_context_packet.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_CONTEXT_EXCLUSION_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_context_exclusion_manifest.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_context_exclusion_manifest.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_SANDBOX_POLICY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_sandbox_policy.v1.json",
            root / "spec" / "programbench_reconstruction_sandbox_policy.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_RUN_BUDGET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_run_budget.v1.json",
            root / "spec" / "programbench_reconstruction_run_budget.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_workbench_non_authority_guardrail.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_workbench_non_authority_guardrail.schema.json",
        ),
    ]


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


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_RECONSTRUCTION_WORK_ORDER_SCHEMA,
            "programbench_reconstruction_work_order.v1.json",
            "programbench_reconstruction_work_order_v248_reference.json",
            ProgrambenchReconstructionWorkOrder,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_WORKER_CONTEXT_PACKET_SCHEMA,
            "programbench_reconstruction_worker_context_packet.v1.json",
            "programbench_reconstruction_worker_context_packet_v248_reference.json",
            ProgrambenchReconstructionWorkerContextPacket,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_CONTEXT_EXCLUSION_MANIFEST_SCHEMA,
            "programbench_reconstruction_context_exclusion_manifest.v1.json",
            "programbench_reconstruction_context_exclusion_manifest_v248_reference.json",
            ProgrambenchReconstructionContextExclusionManifest,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_SANDBOX_POLICY_SCHEMA,
            "programbench_reconstruction_sandbox_policy.v1.json",
            "programbench_reconstruction_sandbox_policy_v248_reference.json",
            ProgrambenchReconstructionSandboxPolicy,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_RUN_BUDGET_SCHEMA,
            "programbench_reconstruction_run_budget.v1.json",
            "programbench_reconstruction_run_budget_v248_reference.json",
            ProgrambenchReconstructionRunBudget,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_reconstruction_workbench_non_authority_guardrail.v1.json",
            "programbench_reconstruction_workbench_non_authority_guardrail_v248_reference.json",
            ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_recon_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_recon_a_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_recon_0a_reference_bundle_preserves_workbench_boundary() -> None:
    case_packet, readiness_summary, adapter_handoff, adapter_family_closeout = _load_c_bundle()
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()

    validate_pb_recon_0a_work_order_bundle(
        case_packet=case_packet,
        readiness_summary=readiness_summary,
        adapter_handoff=adapter_handoff,
        adapter_family_closeout=adapter_family_closeout,
        work_order=work_order,
        worker_context_packet=worker_context_packet,
        context_exclusion_manifest=context_exclusion_manifest,
        sandbox_policy=sandbox_policy,
        run_budget=run_budget,
        guardrail=guardrail,
    )

    assert work_order.dispatch_authority_posture == (
        "no_worker_dispatch_authority_granted_by_pb_recon_0a"
    )
    assert worker_context_packet.context_visibility_posture == (
        "worker_context_cleanroom_visible_only"
    )
    assert context_exclusion_manifest.auditor_only_posture == "auditor_only_not_worker_visible"
    assert sandbox_policy.network_policy == "network_disabled"
    assert run_budget.budget_authority_posture == (
        "budget_constraints_only_no_execution_authority_by_pb_recon_0a"
    )
    assert guardrail.future_family_selection_posture == (
        "no_future_family_selected_by_pb_recon_0a"
    )


def test_pb_recon_0a_bundle_rejects_contaminated_adapter_readiness() -> None:
    case_packet, readiness_summary, adapter_handoff, adapter_family_closeout = _load_c_bundle()
    contaminated = readiness_summary.model_copy(
        update={
            "contamination_status": "forbidden_source_exposure",
            "readiness_posture": "blocked_by_forbidden_evidence_exposure",
            "forbidden_source_exposure_refs": ["store:pb-adapter-0a:original-source"],
        }
    )
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()

    with pytest.raises(ValueError, match="clean adapter readiness contamination"):
        validate_pb_recon_0a_work_order_bundle(
            case_packet=case_packet,
            readiness_summary=contaminated,
            adapter_handoff=adapter_handoff,
            adapter_family_closeout=adapter_family_closeout,
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
        )


def test_pb_recon_0a_bundle_rejects_forbidden_ref_in_worker_context() -> None:
    case_packet, readiness_summary, adapter_handoff, adapter_family_closeout = _load_c_bundle()
    (
        work_order,
        _worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    worker_context_packet = ProgrambenchReconstructionWorkerContextPacket.model_validate(
        _load_recon_a_fixture(
            "programbench_cleanroom_reconstruction_v248_reject_worker_context_forbidden_ref.json"
        )
    )

    with pytest.raises(ValueError, match="non-worker-visible refs"):
        validate_pb_recon_0a_work_order_bundle(
            case_packet=case_packet,
            readiness_summary=readiness_summary,
            adapter_handoff=adapter_handoff,
            adapter_family_closeout=adapter_family_closeout,
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
        )


def test_pb_recon_0a_bundle_rejects_forbidden_summary_in_worker_context() -> None:
    case_packet, readiness_summary, adapter_handoff, adapter_family_closeout = _load_c_bundle()
    (
        work_order,
        _worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    worker_context_packet = ProgrambenchReconstructionWorkerContextPacket.model_validate(
        _load_recon_a_fixture(
            "programbench_cleanroom_reconstruction_v248_reject_worker_context_forbidden_summary.json"
        )
    )

    with pytest.raises(ValueError, match="non-worker-visible refs"):
        validate_pb_recon_0a_work_order_bundle(
            case_packet=case_packet,
            readiness_summary=readiness_summary,
            adapter_handoff=adapter_handoff,
            adapter_family_closeout=adapter_family_closeout,
            work_order=work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
        )


def test_pb_recon_0a_bundle_rejects_dangling_forward_ref() -> None:
    case_packet, readiness_summary, adapter_handoff, adapter_family_closeout = _load_c_bundle()
    (
        work_order,
        worker_context_packet,
        context_exclusion_manifest,
        sandbox_policy,
        run_budget,
        guardrail,
    ) = _load_recon_a_bundle()
    drifted_work_order = work_order.model_copy(
        update={"worker_context_packet_ref": "worker-context:pb-recon-0a:drifted"}
    )

    with pytest.raises(ValueError, match="work order must reference worker context packet"):
        validate_pb_recon_0a_work_order_bundle(
            case_packet=case_packet,
            readiness_summary=readiness_summary,
            adapter_handoff=adapter_handoff,
            adapter_family_closeout=adapter_family_closeout,
            work_order=drifted_work_order,
            worker_context_packet=worker_context_packet,
            context_exclusion_manifest=context_exclusion_manifest,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            guardrail=guardrail,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_reconstruction_v248_reject_blocked_case_packet_work_order.json",
            ProgrambenchReconstructionWorkOrder,
        ),
        (
            "programbench_cleanroom_reconstruction_v248_reject_exclusion_manifest_worker_visible.json",
            ProgrambenchReconstructionContextExclusionManifest,
        ),
        (
            "programbench_cleanroom_reconstruction_v248_reject_sandbox_network_enabled.json",
            ProgrambenchReconstructionSandboxPolicy,
        ),
        (
            "programbench_cleanroom_reconstruction_v248_reject_run_budget_execution_authority.json",
            ProgrambenchReconstructionRunBudget,
        ),
        (
            "programbench_cleanroom_reconstruction_v248_reject_guardrail_future_family_selection.json",
            ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
        ),
        (
            "programbench_cleanroom_reconstruction_v248_reject_guardrail_missing_future_artifact.json",
            ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_recon_0a_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_recon_a_fixture(fixture_name))


def test_pb_recon_0a_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
