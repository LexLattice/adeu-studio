from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .integrity_cycle_policy import AdeuIntegrityCyclePolicy
from .integrity_dangling_reference import AdeuIntegrityDanglingReference
from .lane_report import AdeuLaneReport
from .models import AdeuCoreIR
from .projection_alignment import AdeuProjectionAlignment


def _write_schema(path: Path, schema: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    core_ir_schema = AdeuCoreIR.model_json_schema(by_alias=True)
    lane_report_schema = AdeuLaneReport.model_json_schema(by_alias=True)
    integrity_cycle_policy_schema = AdeuIntegrityCyclePolicy.model_json_schema(by_alias=True)
    integrity_dangling_reference_schema = (
        AdeuIntegrityDanglingReference.model_json_schema(by_alias=True)
    )
    projection_alignment_schema = AdeuProjectionAlignment.model_json_schema(by_alias=True)

    authoritative_path = root / "packages" / "adeu_core_ir" / "schema" / "adeu_core_ir.v0_1.json"
    _write_schema(authoritative_path, core_ir_schema)

    lane_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_lane_report.v0_1.json"
    )
    _write_schema(lane_authoritative_path, lane_report_schema)

    integrity_cycle_policy_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_integrity_cycle_policy.v0_1.json"
    )
    _write_schema(
        integrity_cycle_policy_authoritative_path,
        integrity_cycle_policy_schema,
    )

    integrity_dangling_reference_authoritative_path = (
        root
        / "packages"
        / "adeu_core_ir"
        / "schema"
        / "adeu_integrity_dangling_reference.v0_1.json"
    )
    _write_schema(
        integrity_dangling_reference_authoritative_path,
        integrity_dangling_reference_schema,
    )

    projection_alignment_authoritative_path = (
        root / "packages" / "adeu_core_ir" / "schema" / "adeu_projection_alignment.v0_1.json"
    )
    _write_schema(projection_alignment_authoritative_path, projection_alignment_schema)

    mirror_path = root / "spec" / "adeu_core_ir.schema.json"
    _write_schema(mirror_path, core_ir_schema)

    lane_mirror_path = root / "spec" / "adeu_lane_report.schema.json"
    _write_schema(lane_mirror_path, lane_report_schema)

    integrity_cycle_policy_mirror_path = root / "spec" / "adeu_integrity_cycle_policy.schema.json"
    _write_schema(
        integrity_cycle_policy_mirror_path,
        integrity_cycle_policy_schema,
    )

    integrity_dangling_reference_mirror_path = (
        root / "spec" / "adeu_integrity_dangling_reference.schema.json"
    )
    _write_schema(
        integrity_dangling_reference_mirror_path,
        integrity_dangling_reference_schema,
    )

    projection_alignment_mirror_path = root / "spec" / "adeu_projection_alignment.schema.json"
    _write_schema(projection_alignment_mirror_path, projection_alignment_schema)


if __name__ == "__main__":
    main()
