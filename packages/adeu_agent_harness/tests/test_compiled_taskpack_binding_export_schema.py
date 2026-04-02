from __future__ import annotations

import json
from pathlib import Path

from adeu_agent_harness.compiled_taskpack_binding import COMPILED_POLICY_TASKPACK_BINDING_SCHEMA
from adeu_agent_harness.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root


def _schema_pair() -> tuple[Path, Path]:
    root = repo_root(anchor=Path(__file__))
    return (
        root
        / "packages"
        / "adeu_agent_harness"
        / "schema"
        / "compiled_policy_taskpack_binding.v1.json",
        root / "spec" / "compiled_policy_taskpack_binding.schema.json",
    )


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    authoritative, mirror = _schema_pair()
    assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    authoritative, mirror = _schema_pair()
    before = {
        authoritative: authoritative.read_bytes(),
        mirror: mirror.read_bytes(),
    }

    export_schema_main()
    after_first = {path: path.read_bytes() for path in before}

    export_schema_main()
    after_second = {path: path.read_bytes() for path in before}

    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    authoritative, _ = _schema_pair()
    schema_payload = json.loads(authoritative.read_text(encoding="utf-8"))

    assert (
        schema_payload["properties"]["schema"]["const"]
        == COMPILED_POLICY_TASKPACK_BINDING_SCHEMA
    )
    assert schema_payload["properties"]["binding_profile_source_kind"]["const"] == (
        "released_anm_taskpack_binding_profile_ref"
    )
    assert schema_payload["properties"]["compiler_selection_kind"]["const"] == (
        "released_adeu_agent_harness_taskpack_compiler"
    )
    assert schema_payload["properties"]["kernel_bridge_posture"]["const"] == (
        "released_pipeline_profile_and_registry_then_compile_taskpack"
    )
    assert schema_payload["properties"]["compiled_component_set_kind"]["const"] == (
        "released_taskpack_bundle_component_set"
    )
    assert schema_payload["properties"]["compiled_boundary_identity_posture"]["const"] == (
        "binding_lineage_plus_task_identity_hash"
    )
    assert schema_payload["properties"]["unsupported_compilation_posture"]["const"] == (
        "fail_closed"
    )
