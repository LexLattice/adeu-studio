from __future__ import annotations

import json
from pathlib import Path

from adeu_agent_harness.export_schema import main as export_schema_main
from adeu_agent_harness.worker_execution_envelope import (
    TASK_RUN_BOUNDARY_INSTANCE_SCHEMA,
    WORKER_EXECUTION_ATTESTATION_SCHEMA,
    WORKER_EXECUTION_PROVENANCE_SCHEMA,
)
from adeu_ir.repo import repo_root


def _schema_pairs() -> list[tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            root
            / "packages"
            / "adeu_agent_harness"
            / "schema"
            / "task_run_boundary_instance.v1.json",
            root / "spec" / "task_run_boundary_instance.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_agent_harness"
            / "schema"
            / "worker_execution_attestation.v1.json",
            root / "spec" / "worker_execution_attestation.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_agent_harness"
            / "schema"
            / "worker_execution_provenance.v1.json",
            root / "spec" / "worker_execution_provenance.schema.json",
        ),
    ]


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for authoritative, mirror in _schema_pairs():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    before = {
        path: path.read_bytes()
        for pair in _schema_pairs()
        for path in pair
    }

    export_schema_main()
    after_first = {path: path.read_bytes() for path in before}

    export_schema_main()
    after_second = {path: path.read_bytes() for path in before}

    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    boundary_schema = json.loads(_schema_pairs()[0][0].read_text(encoding="utf-8"))
    attestation_schema = json.loads(_schema_pairs()[1][0].read_text(encoding="utf-8"))
    provenance_schema = json.loads(_schema_pairs()[2][0].read_text(encoding="utf-8"))

    assert boundary_schema["properties"]["schema"]["const"] == TASK_RUN_BOUNDARY_INSTANCE_SCHEMA
    assert boundary_schema["properties"]["compiled_binding_source_kind"]["const"] == (
        "released_compiled_policy_taskpack_binding_ref"
    )
    assert boundary_schema["properties"]["repo_ref_kind"]["const"] == (
        "exact_execution_repository_identity"
    )
    assert boundary_schema["properties"]["worker_subject_kind"]["const"] == (
        "repo_internal_single_codex_worker"
    )
    assert boundary_schema["properties"]["execution_adapter_kind"]["const"] == (
        "released_taskpack_runner_adapter"
    )

    assert (
        attestation_schema["properties"]["schema"]["const"]
        == WORKER_EXECUTION_ATTESTATION_SCHEMA
    )
    assert attestation_schema["properties"]["prompt_authority_posture"]["const"] == (
        "projection_only_conflict_fail_closed"
    )

    assert (
        provenance_schema["properties"]["schema"]["const"]
        == WORKER_EXECUTION_PROVENANCE_SCHEMA
    )
    assert provenance_schema["properties"]["emitted_artifact_refs"]["type"] == "array"
