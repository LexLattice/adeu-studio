from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .models import (
    CONSTITUTIONAL_COHERENCE_LANE_DRIFT_RECORD_SCHEMA,
    CONSTITUTIONAL_COHERENCE_REPORT_SCHEMA,
    CONSTITUTIONAL_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA,
    CONSTITUTIONAL_MIGRATION_DECISION_REGISTER_SCHEMA,
    CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA,
    CONSTITUTIONAL_UNRESOLVED_SEAM_REGISTER_SCHEMA,
    ConstitutionalCoherenceLaneDriftRecord,
    ConstitutionalCoherenceReport,
    ConstitutionalGovernanceCalibrationRegister,
    ConstitutionalMigrationDecisionRegister,
    ConstitutionalSupportAdmissionRecord,
    ConstitutionalUnresolvedSeamRegister,
)

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _write_schema(path: Path, schema: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(schema, indent=2, sort_keys=True) + "\n"
    path.write_text(payload, encoding="utf-8")


def _assert_no_absolute_path_material(
    value: Any,
    *,
    repo_root_path: Path,
    node_path: str = "$",
) -> None:
    if isinstance(value, dict):
        for key in sorted(value):
            _assert_no_absolute_path_material(
                value[key],
                repo_root_path=repo_root_path,
                node_path=f"{node_path}.{key}",
            )
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _assert_no_absolute_path_material(
                item,
                repo_root_path=repo_root_path,
                node_path=f"{node_path}[{index}]",
            )
        return
    if not isinstance(value, str):
        return

    normalized = value.replace("\\", "/")
    root_text = repo_root_path.as_posix()
    if root_text in normalized:
        raise RuntimeError(
            f"schema export contains repository absolute path material at {node_path}: {value!r}"
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.search(value):
        raise RuntimeError(
            f"schema export contains Windows absolute path material at {node_path}: {value!r}"
        )
    if normalized.startswith("/home/") or normalized.startswith("/Users/"):
        raise RuntimeError(
            f"schema export contains user-home absolute path material at {node_path}: {value!r}"
        )


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema_outputs = [
        (
            ConstitutionalSupportAdmissionRecord,
            CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_support_admission_record.v1.json",
            root / "spec" / "constitutional_support_admission_record.schema.json",
        ),
        (
            ConstitutionalCoherenceReport,
            CONSTITUTIONAL_COHERENCE_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_coherence_report.v1.json",
            root / "spec" / "constitutional_coherence_report.schema.json",
        ),
        (
            ConstitutionalUnresolvedSeamRegister,
            CONSTITUTIONAL_UNRESOLVED_SEAM_REGISTER_SCHEMA,
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_unresolved_seam_register.v1.json",
            root / "spec" / "constitutional_unresolved_seam_register.schema.json",
        ),
        (
            ConstitutionalCoherenceLaneDriftRecord,
            CONSTITUTIONAL_COHERENCE_LANE_DRIFT_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_coherence_lane_drift_record.v1.json",
            root / "spec" / "constitutional_coherence_lane_drift_record.schema.json",
        ),
        (
            ConstitutionalGovernanceCalibrationRegister,
            CONSTITUTIONAL_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA,
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_governance_calibration_register.v1.json",
            root / "spec" / "constitutional_governance_calibration_register.schema.json",
        ),
        (
            ConstitutionalMigrationDecisionRegister,
            CONSTITUTIONAL_MIGRATION_DECISION_REGISTER_SCHEMA,
            root
            / "packages"
            / "adeu_constitutional_coherence"
            / "schema"
            / "constitutional_migration_decision_register.v1.json",
            root / "spec" / "constitutional_migration_decision_register.schema.json",
        ),
    ]

    for model, expected_schema, authoritative_path, mirror_path in schema_outputs:
        schema = model.model_json_schema(by_alias=True)
        if schema["properties"]["schema"]["const"] != expected_schema:
            raise RuntimeError(f"schema marker drift for {expected_schema}")
        _assert_no_absolute_path_material(schema, repo_root_path=root)
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
