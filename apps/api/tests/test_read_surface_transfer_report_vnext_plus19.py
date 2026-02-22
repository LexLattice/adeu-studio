from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest
from adeu_api.hashing import canonical_json
from adeu_api.read_surface_transfer_report_vnext_plus19 import (
    READ_SURFACE_TRANSFER_REPORT_VNEXT_PLUS19_SCHEMA,
    ReadSurfaceTransferReportVnextPlus19Error,
    build_read_surface_transfer_report_vnext_plus19_payload,
    read_surface_transfer_report_vnext_plus19_markdown,
)


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _extract_json_block(markdown: str) -> dict[str, object]:
    marker = "```json\n"
    start = markdown.find(marker)
    assert start != -1, "json fenced block start not found"
    start += len(marker)
    end = markdown.find("\n```", start)
    assert end != -1, "json fenced block end not found"
    return json.loads(markdown[start:end])


def test_build_read_surface_transfer_report_payload_is_deterministic() -> None:
    first = build_read_surface_transfer_report_vnext_plus19_payload(
        vnext_plus19_manifest_hash="a" * 64,
    )
    second = build_read_surface_transfer_report_vnext_plus19_payload(
        vnext_plus19_manifest_hash="a" * 64,
    )

    assert first["schema"] == READ_SURFACE_TRANSFER_REPORT_VNEXT_PLUS19_SCHEMA
    assert canonical_json(first) == canonical_json(second)
    assert first["vnext_plus19_manifest_hash"] == "a" * 64

    coverage_summary = first["coverage_summary"]
    assert coverage_summary["valid"] is True
    assert coverage_summary["surface_count"] == 3
    assert coverage_summary["covered_surface_count"] == 3
    assert coverage_summary["coverage_pct"] == 100.0

    assert first["core_ir_read_surface_summary"] == {
        "valid": True,
        "artifact_count": 1,
        "total_nodes": 7,
        "total_edges": 8,
    }
    assert first["lane_read_surface_summary"] == {
        "valid": True,
        "artifact_count": 1,
        "total_lane_projection_edges": 8,
        "lane_node_totals": {"O": 1, "E": 4, "D": 1, "U": 1},
        "lane_edge_totals": {"O": 0, "E": 7, "D": 1, "U": 0},
    }
    assert first["integrity_read_surface_summary"] == {
        "valid": True,
        "artifact_count": 1,
        "family_present_counts": {
            "dangling_reference": 1,
            "cycle_policy": 1,
            "deontic_conflict": 1,
            "reference_integrity_extended": 1,
            "cycle_policy_extended": 1,
            "deontic_conflict_extended": 1,
        },
        "family_missing_counts": {
            "dangling_reference": 0,
            "cycle_policy": 0,
            "deontic_conflict": 0,
            "reference_integrity_extended": 0,
            "cycle_policy_extended": 0,
            "deontic_conflict_extended": 0,
        },
        "family_issue_totals": {
            "dangling_reference": 2,
            "cycle_policy": 2,
            "deontic_conflict": 1,
            "reference_integrity_extended": 3,
            "cycle_policy_extended": 3,
            "deontic_conflict_extended": 2,
        },
    }
    assert first["replay_summary"] == {
        "valid": True,
        "replay_count": 1,
        "fixture_counts": {
            "core_ir_read_surface": 1,
            "lane_read_surface": 1,
            "integrity_read_surface": 1,
        },
        "replay_unit_counts": {
            "core_ir_read_surface": 1,
            "lane_read_surface": 1,
            "integrity_read_surface": 6,
        },
    }

    markdown = read_surface_transfer_report_vnext_plus19_markdown(first)
    parsed_json_block = _extract_json_block(markdown)
    assert canonical_json(parsed_json_block) == canonical_json(first)


def test_build_read_surface_transfer_report_script_writes_markdown(tmp_path: Path) -> None:
    repo_root = _repo_root()
    script = (
        repo_root
        / "apps"
        / "api"
        / "scripts"
        / "build_read_surface_transfer_report_vnext_plus19.py"
    )
    out_markdown = tmp_path / "READ_SURFACE_TRANSFER_REPORT_vNEXT_PLUS19.md"

    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            "--vnext-plus19-manifest-hash",
            "b" * 64,
            "--out",
            str(out_markdown),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, completed.stderr
    markdown = out_markdown.read_text(encoding="utf-8")
    payload = _extract_json_block(markdown)
    assert payload["schema"] == READ_SURFACE_TRANSFER_REPORT_VNEXT_PLUS19_SCHEMA
    assert payload["vnext_plus19_manifest_hash"] == "b" * 64


def test_build_read_surface_transfer_report_rejects_invalid_manifest_hash() -> None:
    with pytest.raises(
        ReadSurfaceTransferReportVnextPlus19Error,
        match="vnext_plus19_manifest_hash must be",
    ):
        build_read_surface_transfer_report_vnext_plus19_payload(
            vnext_plus19_manifest_hash="invalid-hash",
        )

