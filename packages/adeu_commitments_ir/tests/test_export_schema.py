from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_commitments_ir import ADEU_COMMITMENTS_IR_SCHEMA
from adeu_commitments_ir.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _paths() -> tuple[Path, Path]:
    root = repo_root(anchor=Path(__file__))
    authoritative = (
        root
        / "packages"
        / "adeu_commitments_ir"
        / "schema"
        / "adeu_commitments_ir.v0_1.json"
    )
    mirror = root / "spec" / "adeu_commitments_ir.schema.json"
    return authoritative, mirror


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    authoritative, mirror = _paths()
    assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    authoritative, mirror = _paths()
    authoritative_before = authoritative.read_bytes()
    mirror_before = mirror.read_bytes()

    export_schema_main()
    authoritative_after_first = authoritative.read_bytes()
    mirror_after_first = mirror.read_bytes()

    export_schema_main()
    authoritative_after_second = authoritative.read_bytes()
    mirror_after_second = mirror.read_bytes()

    assert authoritative_before == authoritative_after_first == authoritative_after_second
    assert mirror_before == mirror_after_first == mirror_after_second


def test_exported_schema_uses_frozen_writer_profile() -> None:
    authoritative, mirror = _paths()
    authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
    mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))

    expected_authoritative = json.dumps(authoritative_payload, indent=2, sort_keys=True) + "\n"
    expected_mirror = json.dumps(mirror_payload, indent=2, sort_keys=True) + "\n"
    assert authoritative.read_text(encoding="utf-8") == expected_authoritative
    assert mirror.read_text(encoding="utf-8") == expected_mirror


def test_exported_schema_has_stable_contract_markers() -> None:
    authoritative, _ = _paths()
    payload = json.loads(authoritative.read_text(encoding="utf-8"))

    assert payload["properties"]["schema"]["const"] == ADEU_COMMITMENTS_IR_SCHEMA
    discriminator = payload["properties"]["modules"]["items"]["discriminator"]
    assert discriminator["propertyName"] == "module_kind"
    assert sorted(discriminator["mapping"].keys()) == ["arc_lock", "slice_spec", "stop_gate"]


def test_exported_schema_has_no_absolute_path_material() -> None:
    authoritative, mirror = _paths()
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()

    def _check_node(node: object) -> None:
        if isinstance(node, dict):
            for key in sorted(node):
                _check_node(node[key])
            return
        if isinstance(node, list):
            for item in node:
                _check_node(item)
            return
        if not isinstance(node, str):
            return

        normalized = node.replace("\\", "/")
        assert root_text not in normalized
        assert not normalized.startswith("/home/")
        assert not normalized.startswith("/Users/")
        assert _WINDOWS_ABSOLUTE_PATH_RE.search(node) is None

    for path in (authoritative, mirror):
        payload = json.loads(path.read_text(encoding="utf-8"))
        _check_node(payload)
