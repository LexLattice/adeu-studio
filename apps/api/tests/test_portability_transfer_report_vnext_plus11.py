from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest
from adeu_api.portability_transfer_report_vnext_plus11 import (
    PORTABILITY_TRANSFER_REPORT_VNEXT_PLUS11_SCHEMA,
    PortabilityTransferReportError,
    build_portability_transfer_report_vnext_plus11_payload,
    portability_transfer_report_vnext_plus11_markdown,
)
from adeu_api.urm_domain_conformance import build_domain_conformance
from urm_runtime.hashing import canonical_json


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _runtime_root() -> Path:
    return (_repo_root() / "packages" / "urm_runtime" / "src" / "urm_runtime").resolve()


def _artifact_parity_fixtures_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus11_artifact_parity_fixtures.json"
    ).resolve()


def _vnext_plus11_manifest_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus11_manifest.json"
    ).resolve()


def _write_domain_conformance_fixture(tmp_path: Path) -> Path:
    payload = build_domain_conformance(
        events_dir=tmp_path / "domain_conformance_events",
        runtime_root=_runtime_root(),
        artifact_parity_fixtures_path=_artifact_parity_fixtures_path(),
        coverage_manifest_path=_vnext_plus11_manifest_path(),
    )
    output_path = tmp_path / "domain_conformance.json"
    output_path.write_text(canonical_json(payload) + "\n", encoding="utf-8")
    return output_path


def _extract_json_block(markdown: str) -> dict[str, object]:
    marker = "```json\n"
    start = markdown.find(marker)
    assert start != -1, "json fenced block start not found"
    start += len(marker)
    end = markdown.find("\n```", start)
    assert end != -1, "json fenced block end not found"
    return json.loads(markdown[start:end])


def test_build_portability_transfer_report_payload_is_deterministic(tmp_path: Path) -> None:
    domain_conformance_path = _write_domain_conformance_fixture(tmp_path)
    manifest_path = _vnext_plus11_manifest_path()

    first = build_portability_transfer_report_vnext_plus11_payload(
        vnext_plus11_manifest_path=manifest_path,
        domain_conformance_path=domain_conformance_path,
    )
    second = build_portability_transfer_report_vnext_plus11_payload(
        vnext_plus11_manifest_path=manifest_path,
        domain_conformance_path=domain_conformance_path,
    )

    assert first["schema"] == PORTABILITY_TRANSFER_REPORT_VNEXT_PLUS11_SCHEMA
    assert canonical_json(first) == canonical_json(second)
    assert isinstance(first["vnext_plus11_manifest_hash"], str)
    assert len(first["vnext_plus11_manifest_hash"]) == 64
    assert isinstance(first["domain_conformance_hash"], str)
    assert len(first["domain_conformance_hash"]) == 64
    coverage_summary = first["coverage_summary"]
    assert coverage_summary["valid"] is True
    assert coverage_summary["surface_count"] == 11
    assert coverage_summary["covered_surface_count"] == 11
    assert coverage_summary["coverage_pct"] == 100.0
    parity_summary = first["parity_summary"]
    assert parity_summary["valid"] is True
    assert parity_summary["fixture_count"] == 4
    assert parity_summary["evaluated_count"] == 4

    markdown = portability_transfer_report_vnext_plus11_markdown(first)
    parsed_json_block = _extract_json_block(markdown)
    assert canonical_json(parsed_json_block) == canonical_json(first)


def test_build_portability_transfer_report_script_writes_markdown(tmp_path: Path) -> None:
    repo_root = _repo_root()
    script = (
        repo_root
        / "apps"
        / "api"
        / "scripts"
        / "build_portability_transfer_report_vnext_plus11.py"
    )
    domain_conformance_path = _write_domain_conformance_fixture(tmp_path)
    out_markdown = tmp_path / "PORTABILITY_TRANSFER_REPORT_vNEXT_PLUS11.md"

    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            "--vnext-plus11-manifest",
            str(_vnext_plus11_manifest_path()),
            "--domain-conformance",
            str(domain_conformance_path),
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
    assert payload["schema"] == PORTABILITY_TRANSFER_REPORT_VNEXT_PLUS11_SCHEMA
    assert payload["coverage_summary"]["valid"] is True
    assert payload["parity_summary"]["valid"] is True


def test_build_portability_transfer_report_rejects_manifest_hash_mismatch(tmp_path: Path) -> None:
    domain_conformance_path = _write_domain_conformance_fixture(tmp_path)
    bad_manifest_payload = json.loads(_vnext_plus11_manifest_path().read_text(encoding="utf-8"))
    bad_manifest_payload["manifest_hash"] = "0" * 64
    bad_manifest_path = tmp_path / "bad_manifest.json"
    bad_manifest_path.write_text(canonical_json(bad_manifest_payload) + "\n", encoding="utf-8")

    with pytest.raises(PortabilityTransferReportError, match="manifest_hash mismatch"):
        build_portability_transfer_report_vnext_plus11_payload(
            vnext_plus11_manifest_path=bad_manifest_path,
            domain_conformance_path=domain_conformance_path,
        )
