from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest
from adeu_api.integrity_transfer_report_vnext_plus17 import (
    INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS17_SCHEMA,
    IntegrityTransferReportError,
    build_integrity_transfer_report_vnext_plus17_payload,
    integrity_transfer_report_vnext_plus17_markdown,
)
from urm_runtime.hashing import canonical_json, sha256_canonical_json


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _vnext_plus17_manifest_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus17_manifest.json"
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
    path = tmp_path / "vnext_plus17_manifest.json"
    path.write_text(canonical_json(normalized) + "\n", encoding="utf-8")
    return path


def _absolutize_run_refs(payload: dict[str, object]) -> None:
    manifest_dir = _vnext_plus17_manifest_path().parent
    fixture_key_runs = (
        ("reference_integrity_extended_fixtures", "reference_integrity_extended_path"),
        ("cycle_policy_extended_fixtures", "cycle_policy_extended_path"),
        ("deontic_conflict_extended_fixtures", "deontic_conflict_extended_path"),
    )
    for fixture_key, run_key in fixture_key_runs:
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
                value = run.get(run_key)
                if not isinstance(value, str) or not value:
                    continue
                path = Path(value)
                if path.is_absolute():
                    continue
                run[run_key] = str((manifest_dir / path).resolve())


def test_build_integrity_transfer_report_payload_is_deterministic() -> None:
    first = build_integrity_transfer_report_vnext_plus17_payload(
        vnext_plus17_manifest_path=_vnext_plus17_manifest_path(),
    )
    second = build_integrity_transfer_report_vnext_plus17_payload(
        vnext_plus17_manifest_path=_vnext_plus17_manifest_path(),
    )

    assert first["schema"] == INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS17_SCHEMA
    assert canonical_json(first) == canonical_json(second)
    assert isinstance(first["vnext_plus17_manifest_hash"], str)
    assert len(first["vnext_plus17_manifest_hash"]) == 64

    coverage_summary = first["coverage_summary"]
    assert coverage_summary["valid"] is True
    assert coverage_summary["surface_count"] == 3
    assert coverage_summary["covered_surface_count"] == 3
    assert coverage_summary["coverage_pct"] == 100.0

    assert first["reference_integrity_extended_summary"]["valid"] is True
    assert first["cycle_policy_extended_summary"]["valid"] is True
    assert first["deontic_conflict_extended_summary"]["valid"] is True

    replay_summary = first["replay_summary"]
    assert replay_summary["valid"] is True
    assert replay_summary["replay_count"] == 3
    assert replay_summary["fixture_counts"] == {
        "reference_integrity_extended": 1,
        "cycle_policy_extended": 1,
        "deontic_conflict_extended": 1,
    }
    assert replay_summary["replay_unit_counts"] == {
        "reference_integrity_extended": 3,
        "cycle_policy_extended": 3,
        "deontic_conflict_extended": 3,
    }

    markdown = integrity_transfer_report_vnext_plus17_markdown(first)
    parsed_json_block = _extract_json_block(markdown)
    assert canonical_json(parsed_json_block) == canonical_json(first)


def test_build_integrity_transfer_report_script_writes_markdown(tmp_path: Path) -> None:
    repo_root = _repo_root()
    script = (
        repo_root
        / "apps"
        / "api"
        / "scripts"
        / "build_integrity_transfer_report_vnext_plus17.py"
    )
    out_markdown = tmp_path / "INTEGRITY_TRANSFER_REPORT_vNEXT_PLUS17.md"

    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            "--vnext-plus17-manifest",
            str(_vnext_plus17_manifest_path()),
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
    assert payload["schema"] == INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS17_SCHEMA
    assert payload["coverage_summary"]["valid"] is True
    assert payload["replay_summary"]["valid"] is True


def test_build_integrity_transfer_report_rejects_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    bad_manifest_payload = json.loads(_vnext_plus17_manifest_path().read_text(encoding="utf-8"))
    bad_manifest_payload["manifest_hash"] = "0" * 64
    bad_manifest_path = tmp_path / "bad_vnext_plus17_manifest.json"
    bad_manifest_path.write_text(canonical_json(bad_manifest_payload) + "\n", encoding="utf-8")

    with pytest.raises(IntegrityTransferReportError, match="manifest_hash mismatch"):
        build_integrity_transfer_report_vnext_plus17_payload(
            vnext_plus17_manifest_path=bad_manifest_path,
        )


def test_integrity_transfer_report_rejects_cross_surface_coverage_fixture_id(
    tmp_path: Path,
) -> None:
    manifest_payload = json.loads(_vnext_plus17_manifest_path().read_text(encoding="utf-8"))
    coverage_entries = manifest_payload["coverage"]
    for entry in coverage_entries:
        if entry["surface_id"] == "adeu.integrity.reference_integrity_extended":
            entry["fixture_ids"][0] = "integrity_cycle_policy_extended.case_a"
            entry["fixture_ids"] = sorted(entry["fixture_ids"])
            break

    manifest_path = _write_manifest_with_recomputed_hash(tmp_path, manifest_payload)
    with pytest.raises(
        IntegrityTransferReportError,
        match="mapped to a different surface",
    ):
        build_integrity_transfer_report_vnext_plus17_payload(
            vnext_plus17_manifest_path=manifest_path,
        )


def test_integrity_transfer_report_rejects_deontic_summary_mismatch(
    tmp_path: Path,
) -> None:
    manifest_payload = json.loads(_vnext_plus17_manifest_path().read_text(encoding="utf-8"))
    _absolutize_run_refs(manifest_payload)

    bad_deontic_payload = {
        "schema": "adeu_integrity_deontic_conflict_extended@0.1",
        "source_text_hash": "hash-e3-stop-gate-case-a",
        "summary": {
            "total_conflicts": 0,
            "deontic_conflict": 0,
            "deontic_tension": 0,
        },
        "conflicts": [
            {
                "kind": "deontic_conflict",
                "primary_id": "d_forbidden_1",
                "related_id": "d_obligatory_1",
            }
        ],
    }
    bad_deontic_path = tmp_path / "bad_deontic_conflict_extended.json"
    bad_deontic_path.write_text(canonical_json(bad_deontic_payload) + "\n", encoding="utf-8")

    fixtures = manifest_payload["deontic_conflict_extended_fixtures"]
    for fixture in fixtures:
        for run in fixture["runs"]:
            run["deontic_conflict_extended_path"] = str(bad_deontic_path)

    manifest_path = _write_manifest_with_recomputed_hash(tmp_path, manifest_payload)
    with pytest.raises(IntegrityTransferReportError, match="summary.total_conflicts mismatch"):
        build_integrity_transfer_report_vnext_plus17_payload(
            vnext_plus17_manifest_path=manifest_path,
        )
