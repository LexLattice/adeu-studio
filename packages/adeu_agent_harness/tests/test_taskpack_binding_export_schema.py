from __future__ import annotations

import json
import re
from pathlib import Path

import pytest
from adeu_agent_harness.export_schema import (
    _assert_no_absolute_path_material,
)
from adeu_agent_harness.export_schema import (
    main as export_schema_main,
)
from adeu_agent_harness.taskpack_binding import ANM_TASKPACK_BINDING_PROFILE_SCHEMA
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_pair() -> tuple[Path, Path]:
    root = repo_root(anchor=Path(__file__))
    return (
        root
        / "packages"
        / "adeu_agent_harness"
        / "schema"
        / "anm_taskpack_binding_profile.v1.json",
        root / "spec" / "anm_taskpack_binding_profile.schema.json",
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

    assert schema_payload["properties"]["schema"]["const"] == ANM_TASKPACK_BINDING_PROFILE_SCHEMA
    assert schema_payload["properties"]["policy_binding_source_kind"]["const"] == (
        "released_v47e_policy_consumer_row_ref"
    )
    assert schema_payload["properties"]["scope_binding_source_kind"]["const"] == (
        "released_v45_scope_surface_ref"
    )
    assert schema_payload["properties"]["scope_binding_authority_kind"]["const"] == (
        "released_v45f_binding_entry_ref"
    )
    assert schema_payload["properties"]["worker_subject_kind"]["const"] == (
        "repo_internal_single_codex_worker"
    )
    forbidden_ref = schema_payload["properties"]["forbidden_projection"]["$ref"]
    command_ref = schema_payload["properties"]["command_projection"]["items"]["$ref"]
    evidence_ref = schema_payload["properties"]["evidence_slot_projection"]["items"]["$ref"]
    assert forbidden_ref.endswith("/TaskpackForbiddenProjection")
    assert command_ref.endswith("/TaskpackCommandProjection")
    assert evidence_ref.endswith("/TaskpackEvidenceSlotProjection")
    assert (
        schema_payload["$defs"]["TaskpackCommandProjection"]["required"]
        == [
            "command_id",
            "run",
            "working_directory_or_repo_root",
        ]
    )
    assert schema_payload["$defs"]["TaskpackEvidenceSlotProjection"]["required"] == [
        "slot_id",
        "description",
        "required",
    ]


def test_exported_schema_contains_no_absolute_path_material() -> None:
    authoritative, mirror = _schema_pair()
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()

    for path in (authoritative, mirror):
        payload_text = path.read_text(encoding="utf-8")
        assert root_text not in payload_text
        assert "/home/" not in payload_text
        assert "/Users/" not in payload_text
        assert _WINDOWS_ABSOLUTE_PATH_RE.search(payload_text) is None


def test_absolute_path_guard_rejects_single_backslash_windows_paths() -> None:
    root = repo_root(anchor=Path(__file__))

    with pytest.raises(RuntimeError, match="Windows absolute path material"):
        _assert_no_absolute_path_material(
            {"bad_path": r"C:\Users\alice\repo\artifact.json"},
            repo_root_path=root,
        )
