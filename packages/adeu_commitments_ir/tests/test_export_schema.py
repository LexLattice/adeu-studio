from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_commitments_ir import (
    ADEU_COMMITMENTS_IR_SCHEMA,
    CHECKER_FACT_BUNDLE_SCHEMA,
    D1_NORMALIZED_IR_SCHEMA,
    POLICY_EVALUATION_RESULT_SET_SCHEMA,
    POLICY_OBLIGATION_LEDGER_SCHEMA,
    PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA,
)
from adeu_commitments_ir.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            ADEU_COMMITMENTS_IR_SCHEMA,
            root / "packages" / "adeu_commitments_ir" / "schema" / "adeu_commitments_ir.v0_1.json",
            root / "spec" / "adeu_commitments_ir.schema.json",
        ),
        (
            D1_NORMALIZED_IR_SCHEMA,
            root / "packages" / "adeu_commitments_ir" / "schema" / "d1_normalized_ir.v1.json",
            root / "spec" / "d1_normalized_ir.schema.json",
        ),
        (
            PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "predicate_contracts_bootstrap.v1.json",
            root / "spec" / "predicate_contracts_bootstrap.schema.json",
        ),
        (
            CHECKER_FACT_BUNDLE_SCHEMA,
            root / "packages" / "adeu_commitments_ir" / "schema" / "checker_fact_bundle.v1.json",
            root / "spec" / "checker_fact_bundle.schema.json",
        ),
        (
            POLICY_EVALUATION_RESULT_SET_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "policy_evaluation_result_set.v1.json",
            root / "spec" / "policy_evaluation_result_set.schema.json",
        ),
        (
            POLICY_OBLIGATION_LEDGER_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "policy_obligation_ledger.v1.json",
            root / "spec" / "policy_obligation_ledger.schema.json",
        ),
    ]


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for _, authoritative, mirror in _schema_pairs():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    before = {
        authoritative: authoritative.read_bytes()
        for _, authoritative, _ in _schema_pairs()
    }
    before.update(
        {
            mirror: mirror.read_bytes()
            for _, _, mirror in _schema_pairs()
        }
    )

    export_schema_main()
    after_first = {path: path.read_bytes() for path in before}

    export_schema_main()
    after_second = {path: path.read_bytes() for path in before}

    assert before == after_first == after_second


def test_exported_schema_uses_frozen_writer_profile() -> None:
    for _, authoritative, mirror in _schema_pairs():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))

        expected_authoritative = json.dumps(authoritative_payload, indent=2, sort_keys=True) + "\n"
        expected_mirror = json.dumps(mirror_payload, indent=2, sort_keys=True) + "\n"
        assert authoritative.read_text(encoding="utf-8") == expected_authoritative
        assert mirror.read_text(encoding="utf-8") == expected_mirror


def test_exported_schema_has_stable_contract_markers() -> None:
    schema_payloads = {
        schema_label: json.loads(authoritative.read_text(encoding="utf-8"))
        for schema_label, authoritative, _ in _schema_pairs()
    }

    commitments_schema = schema_payloads[ADEU_COMMITMENTS_IR_SCHEMA]
    assert commitments_schema["properties"]["schema"]["const"] == ADEU_COMMITMENTS_IR_SCHEMA
    discriminator = commitments_schema["properties"]["modules"]["items"]["discriminator"]
    assert discriminator["propertyName"] == "module_kind"
    assert sorted(discriminator["mapping"].keys()) == ["arc_lock", "slice_spec", "stop_gate"]
    assert (
        schema_payloads[D1_NORMALIZED_IR_SCHEMA]["properties"]["schema"]["const"]
        == D1_NORMALIZED_IR_SCHEMA
    )
    assert (
        schema_payloads[PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA]["properties"]["schema"]["const"]
        == PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA
    )
    assert (
        schema_payloads[CHECKER_FACT_BUNDLE_SCHEMA]["properties"]["schema"]["const"]
        == CHECKER_FACT_BUNDLE_SCHEMA
    )
    assert (
        schema_payloads[POLICY_EVALUATION_RESULT_SET_SCHEMA]["properties"]["schema"]["const"]
        == POLICY_EVALUATION_RESULT_SET_SCHEMA
    )
    assert (
        schema_payloads[POLICY_OBLIGATION_LEDGER_SCHEMA]["properties"]["schema"]["const"]
        == POLICY_OBLIGATION_LEDGER_SCHEMA
    )


def test_exported_schema_has_no_absolute_path_material() -> None:
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

    for _, authoritative, mirror in _schema_pairs():
        for path in (authoritative, mirror):
            payload = json.loads(path.read_text(encoding="utf-8"))
            _check_node(payload)
