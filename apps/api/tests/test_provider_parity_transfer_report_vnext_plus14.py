from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest
from adeu_api.provider_parity_transfer_report_vnext_plus14 import (
    PROVIDER_PARITY_TRANSFER_REPORT_VNEXT_PLUS14_SCHEMA,
    ProviderParityTransferReportError,
    build_provider_parity_transfer_report_vnext_plus14_payload,
    provider_parity_transfer_report_vnext_plus14_markdown,
)
from urm_runtime.hashing import canonical_json


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _vnext_plus14_manifest_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus14_manifest.json"
    ).resolve()


def _provider_matrix_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "provider_parity"
        / "vnext_plus14_provider_matrix.json"
    ).resolve()


def _extract_json_block(markdown: str) -> dict[str, object]:
    marker = "```json\n"
    start = markdown.find(marker)
    assert start != -1, "json fenced block start not found"
    start += len(marker)
    end = markdown.find("\n```", start)
    assert end != -1, "json fenced block end not found"
    return json.loads(markdown[start:end])


def test_build_provider_parity_transfer_report_payload_is_deterministic() -> None:
    first = build_provider_parity_transfer_report_vnext_plus14_payload(
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        provider_matrix_path=_provider_matrix_path(),
    )
    second = build_provider_parity_transfer_report_vnext_plus14_payload(
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        provider_matrix_path=_provider_matrix_path(),
    )

    assert first["schema"] == PROVIDER_PARITY_TRANSFER_REPORT_VNEXT_PLUS14_SCHEMA
    assert canonical_json(first) == canonical_json(second)
    assert isinstance(first["vnext_plus14_manifest_hash"], str)
    assert len(first["vnext_plus14_manifest_hash"]) == 64
    assert isinstance(first["provider_matrix_hash"], str)
    assert len(first["provider_matrix_hash"]) == 64

    parity_summary = first["parity_summary"]
    assert parity_summary["valid"] is True
    assert parity_summary["surface_count"] == 5
    assert parity_summary["matrix_surface_count"] == 5

    coverage_summary = first["coverage_summary"]
    assert coverage_summary["valid"] is True
    assert coverage_summary["surface_count"] == 5
    assert coverage_summary["covered_surface_count"] == 5
    assert coverage_summary["coverage_pct"] == 100.0

    markdown = provider_parity_transfer_report_vnext_plus14_markdown(first)
    parsed_json_block = _extract_json_block(markdown)
    assert canonical_json(parsed_json_block) == canonical_json(first)


def test_build_provider_parity_transfer_report_script_writes_markdown(tmp_path: Path) -> None:
    repo_root = _repo_root()
    script = (
        repo_root
        / "apps"
        / "api"
        / "scripts"
        / "build_provider_parity_transfer_report_vnext_plus14.py"
    )
    out_markdown = tmp_path / "PROVIDER_PARITY_TRANSFER_REPORT_vNEXT_PLUS14.md"

    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            "--vnext-plus14-manifest",
            str(_vnext_plus14_manifest_path()),
            "--provider-matrix",
            str(_provider_matrix_path()),
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
    assert payload["schema"] == PROVIDER_PARITY_TRANSFER_REPORT_VNEXT_PLUS14_SCHEMA
    assert payload["parity_summary"]["valid"] is True
    assert payload["coverage_summary"]["valid"] is True


def test_build_provider_parity_transfer_report_rejects_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    bad_manifest_payload = json.loads(_vnext_plus14_manifest_path().read_text(encoding="utf-8"))
    bad_manifest_payload["manifest_hash"] = "0" * 64
    bad_manifest_path = tmp_path / "bad_vnext_plus14_manifest.json"
    bad_manifest_path.write_text(canonical_json(bad_manifest_payload) + "\n", encoding="utf-8")

    with pytest.raises(ProviderParityTransferReportError, match="manifest_hash mismatch"):
        build_provider_parity_transfer_report_vnext_plus14_payload(
            vnext_plus14_manifest_path=bad_manifest_path,
            provider_matrix_path=_provider_matrix_path(),
        )
