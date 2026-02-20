from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest
from adeu_api.core_ir_depth_transfer_report_vnext_plus15 import (
    CORE_IR_DEPTH_TRANSFER_REPORT_VNEXT_PLUS15_SCHEMA,
    CoreIrDepthTransferReportError,
    build_core_ir_depth_transfer_report_vnext_plus15_payload,
    core_ir_depth_transfer_report_vnext_plus15_markdown,
)
from urm_runtime.hashing import canonical_json, sha256_canonical_json


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _vnext_plus15_manifest_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus15_manifest.json"
    ).resolve()


def _extract_json_block(markdown: str) -> dict[str, object]:
    marker = "```json\n"
    start = markdown.find(marker)
    assert start != -1, "json fenced block start not found"
    start += len(marker)
    end = markdown.find("\n```", start)
    assert end != -1, "json fenced block end not found"
    return json.loads(markdown[start:end])


def _write_manifest_with_recomputed_hash(tmp_path: Path, payload: dict[str, object]) -> Path:
    normalized = dict(payload)
    normalized.pop("manifest_hash", None)
    normalized["manifest_hash"] = sha256_canonical_json(normalized)
    path = tmp_path / "vnext_plus15_manifest.json"
    path.write_text(canonical_json(normalized) + "\n", encoding="utf-8")
    return path


def _absolutize_run_refs(payload: dict[str, object]) -> None:
    manifest_dir = _vnext_plus15_manifest_path().parent
    fixture_keys = (
        "lane_report_replay_fixtures",
        "projection_alignment_fixtures",
        "depth_report_replay_fixtures",
    )
    for fixture_key in fixture_keys:
        fixtures = payload.get(fixture_key, [])
        if not isinstance(fixtures, list):
            continue
        for fixture in fixtures:
            if not isinstance(fixture, dict):
                continue
            runs = fixture.get("runs", [])
            if not isinstance(runs, list):
                continue
            for run in runs:
                if not isinstance(run, dict):
                    continue
                for key, value in list(run.items()):
                    if not isinstance(value, str) or not value:
                        continue
                    path = Path(value)
                    if path.is_absolute():
                        continue
                    run[key] = str((manifest_dir / path).resolve())


def test_build_core_ir_depth_transfer_report_payload_is_deterministic() -> None:
    first = build_core_ir_depth_transfer_report_vnext_plus15_payload(
        vnext_plus15_manifest_path=_vnext_plus15_manifest_path(),
    )
    second = build_core_ir_depth_transfer_report_vnext_plus15_payload(
        vnext_plus15_manifest_path=_vnext_plus15_manifest_path(),
    )

    assert first["schema"] == CORE_IR_DEPTH_TRANSFER_REPORT_VNEXT_PLUS15_SCHEMA
    assert canonical_json(first) == canonical_json(second)
    assert isinstance(first["vnext_plus15_manifest_hash"], str)
    assert len(first["vnext_plus15_manifest_hash"]) == 64

    coverage_summary = first["coverage_summary"]
    assert coverage_summary["valid"] is True
    assert coverage_summary["surface_count"] == 3
    assert coverage_summary["covered_surface_count"] == 3
    assert coverage_summary["coverage_pct"] == 100.0

    alignment_summary = first["alignment_summary"]
    assert alignment_summary["valid"] is True
    assert alignment_summary["fixture_count"] == 1
    assert alignment_summary["run_count"] == 3

    replay_summary = first["replay_summary"]
    assert replay_summary["valid"] is True
    assert replay_summary["replay_count"] == 3
    assert replay_summary["fixture_counts"] == {
        "lane_report_replay": 1,
        "projection_alignment": 1,
        "depth_report_replay": 1,
    }
    assert replay_summary["replay_unit_counts"] == {
        "lane_report_replay": 3,
        "projection_alignment": 3,
        "depth_report_replay": 3,
    }

    markdown = core_ir_depth_transfer_report_vnext_plus15_markdown(first)
    parsed_json_block = _extract_json_block(markdown)
    assert canonical_json(parsed_json_block) == canonical_json(first)


def test_build_core_ir_depth_transfer_report_script_writes_markdown(tmp_path: Path) -> None:
    repo_root = _repo_root()
    script = (
        repo_root
        / "apps"
        / "api"
        / "scripts"
        / "build_core_ir_depth_transfer_report_vnext_plus15.py"
    )
    out_markdown = tmp_path / "CORE_IR_DEPTH_TRANSFER_REPORT_vNEXT_PLUS15.md"

    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            "--vnext-plus15-manifest",
            str(_vnext_plus15_manifest_path()),
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
    assert payload["schema"] == CORE_IR_DEPTH_TRANSFER_REPORT_VNEXT_PLUS15_SCHEMA
    assert payload["coverage_summary"]["valid"] is True
    assert payload["alignment_summary"]["valid"] is True
    assert payload["replay_summary"]["valid"] is True


def test_build_core_ir_depth_transfer_report_rejects_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    bad_manifest_payload = json.loads(_vnext_plus15_manifest_path().read_text(encoding="utf-8"))
    bad_manifest_payload["manifest_hash"] = "0" * 64
    bad_manifest_path = tmp_path / "bad_vnext_plus15_manifest.json"
    bad_manifest_path.write_text(canonical_json(bad_manifest_payload) + "\n", encoding="utf-8")

    with pytest.raises(CoreIrDepthTransferReportError, match="manifest_hash mismatch"):
        build_core_ir_depth_transfer_report_vnext_plus15_payload(
            vnext_plus15_manifest_path=bad_manifest_path,
        )


def test_core_ir_depth_transfer_report_rejects_cross_surface_coverage_fixture_id(
    tmp_path: Path,
) -> None:
    manifest_payload = json.loads(_vnext_plus15_manifest_path().read_text(encoding="utf-8"))
    coverage_entries = manifest_payload["coverage"]
    for entry in coverage_entries:
        if entry["surface_id"] == "adeu.core_ir.lane_report":
            entry["fixture_ids"][0] = "projection_alignment.case_a"
            entry["fixture_ids"] = sorted(entry["fixture_ids"])
            break

    manifest_path = _write_manifest_with_recomputed_hash(tmp_path, manifest_payload)
    with pytest.raises(
        CoreIrDepthTransferReportError,
        match="references fixture_ids mapped to other surfaces",
    ):
        build_core_ir_depth_transfer_report_vnext_plus15_payload(
            vnext_plus15_manifest_path=manifest_path,
        )


def test_core_ir_depth_transfer_report_rejects_empty_lane_node_evidence(
    tmp_path: Path,
) -> None:
    manifest_payload = json.loads(_vnext_plus15_manifest_path().read_text(encoding="utf-8"))
    _absolutize_run_refs(manifest_payload)

    lane_report_payload = {
        "schema": "adeu_lane_report@0.1",
        "source_text_hash": "hash-empty",
        "lane_nodes": {"O": [], "E": [], "D": [], "U": []},
        "lane_edge_counts": {"O": 0, "E": 0, "D": 0, "U": 0},
    }
    lane_report_path = tmp_path / "empty_lane_report.json"
    lane_report_path.write_text(canonical_json(lane_report_payload) + "\n", encoding="utf-8")

    for fixture in manifest_payload["lane_report_replay_fixtures"]:
        for run in fixture["runs"]:
            run["lane_report_path"] = str(lane_report_path)

    manifest_path = _write_manifest_with_recomputed_hash(tmp_path, manifest_payload)
    with pytest.raises(
        CoreIrDepthTransferReportError,
        match="empty lane-node evidence",
    ):
        build_core_ir_depth_transfer_report_vnext_plus15_payload(
            vnext_plus15_manifest_path=manifest_path,
        )
