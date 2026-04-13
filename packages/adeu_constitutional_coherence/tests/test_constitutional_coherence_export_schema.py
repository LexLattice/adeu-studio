from __future__ import annotations

import json
from pathlib import Path

from adeu_constitutional_coherence import (
    CONSTITUTIONAL_COHERENCE_LANE_DRIFT_RECORD_SCHEMA,
    CONSTITUTIONAL_COHERENCE_REPORT_SCHEMA,
    CONSTITUTIONAL_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA,
    CONSTITUTIONAL_MIGRATION_DECISION_REGISTER_SCHEMA,
    CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA,
    CONSTITUTIONAL_UNRESOLVED_SEAM_REGISTER_SCHEMA,
)
from adeu_constitutional_coherence.export_schema import (
    _assert_no_absolute_path_material,
)
from adeu_constitutional_coherence.export_schema import (
    main as export_schema_main,
)
from adeu_ir.repo import repo_root


def _schema_pairs() -> dict[str, tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return {
        CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_support_admission_record.v1.json",
            root / "spec" / "constitutional_support_admission_record.schema.json",
        ),
        CONSTITUTIONAL_COHERENCE_REPORT_SCHEMA: (
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_coherence_report.v1.json",
            root / "spec" / "constitutional_coherence_report.schema.json",
        ),
        CONSTITUTIONAL_UNRESOLVED_SEAM_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_unresolved_seam_register.v1.json",
            root / "spec" / "constitutional_unresolved_seam_register.schema.json",
        ),
        CONSTITUTIONAL_COHERENCE_LANE_DRIFT_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_coherence_lane_drift_record.v1.json",
            root / "spec" / "constitutional_coherence_lane_drift_record.schema.json",
        ),
        CONSTITUTIONAL_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_governance_calibration_register.v1.json",
            root / "spec" / "constitutional_governance_calibration_register.schema.json",
        ),
        CONSTITUTIONAL_MIGRATION_DECISION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_migration_decision_register.v1.json",
            root / "spec" / "constitutional_migration_decision_register.schema.json",
        ),
    }


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for authoritative, mirror in _schema_pairs().values():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    pairs = _schema_pairs()
    before = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    export_schema_main()
    after_first = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    export_schema_main()
    after_second = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    for expected_schema, (authoritative, _mirror) in _schema_pairs().items():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_schema


def test_exported_schema_has_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))
    for authoritative, mirror in _schema_pairs().values():
        _assert_no_absolute_path_material(
            json.loads(authoritative.read_text(encoding="utf-8")),
            repo_root_path=root,
        )
        _assert_no_absolute_path_material(
            json.loads(mirror.read_text(encoding="utf-8")),
            repo_root_path=root,
        )
