from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from urm_runtime.extraction_fidelity_transfer_report_vnext_plus24 import (
    EXTRACTION_FIDELITY_TRANSFER_REPORT_VNEXT_PLUS24_SCHEMA,
    build_extraction_fidelity_transfer_report_vnext_plus24_payload,
)
from urm_runtime.hashing import canonical_json


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus24_manifest.json"


def _metrics_path() -> Path:
    return _repo_root() / "artifacts" / "stop_gate" / "metrics_v24_closeout.json"


def _doc_path() -> Path:
    return _repo_root() / "docs" / "EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md"


def _extract_json_block(markdown: str) -> dict[str, object]:
    marker = "```json\n"
    start = markdown.find(marker)
    assert start != -1, "json fenced block start not found"
    start += len(marker)
    end = markdown.find("\n```", start)
    assert end != -1, "json fenced block end not found"
    return json.loads(markdown[start:end])


def test_build_extraction_fidelity_transfer_report_payload_is_deterministic() -> None:
    first = build_extraction_fidelity_transfer_report_vnext_plus24_payload(
        vnext_plus24_manifest_path=_manifest_path(),
        stop_gate_metrics_path=_metrics_path(),
    )
    second = build_extraction_fidelity_transfer_report_vnext_plus24_payload(
        vnext_plus24_manifest_path=_manifest_path(),
        stop_gate_metrics_path=_metrics_path(),
    )

    assert first["schema"] == EXTRACTION_FIDELITY_TRANSFER_REPORT_VNEXT_PLUS24_SCHEMA
    assert canonical_json(first) == canonical_json(second)
    assert first["coverage_summary"]["valid"] is True
    assert first["replay_summary"]["valid"] is True


def test_build_extraction_fidelity_transfer_report_matches_locked_doc_json() -> None:
    payload = build_extraction_fidelity_transfer_report_vnext_plus24_payload(
        vnext_plus24_manifest_path=_manifest_path(),
        stop_gate_metrics_path=_metrics_path(),
    )
    doc_payload = _extract_json_block(_doc_path().read_text(encoding="utf-8"))
    assert canonical_json(payload) == canonical_json(doc_payload)


def test_build_extraction_fidelity_transfer_report_script_writes_markdown(tmp_path: Path) -> None:
    repo_root = _repo_root()
    script = (
        repo_root
        / "apps"
        / "api"
        / "scripts"
        / "build_extraction_fidelity_transfer_report_vnext_plus24.py"
    )
    out_markdown = tmp_path / "EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md"

    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            "--vnext-plus24-manifest",
            str(_manifest_path()),
            "--stop-gate-metrics",
            str(_metrics_path()),
            "--out",
            str(out_markdown),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stderr
    payload = _extract_json_block(out_markdown.read_text(encoding="utf-8"))
    assert payload["schema"] == EXTRACTION_FIDELITY_TRANSFER_REPORT_VNEXT_PLUS24_SCHEMA
    assert payload["replay_summary"]["all_passed"] is True
