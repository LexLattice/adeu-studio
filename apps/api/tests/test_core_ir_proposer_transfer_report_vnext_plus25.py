from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from urm_runtime.core_ir_proposer_transfer_report_vnext_plus25 import (
    CORE_IR_PROPOSER_TRANSFER_REPORT_VNEXT_PLUS25_SCHEMA,
    build_core_ir_proposer_transfer_report_vnext_plus25_payload,
)
from urm_runtime.hashing import canonical_json


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus25_manifest.json"


def _metrics_path() -> Path:
    return _repo_root() / "artifacts" / "stop_gate" / "metrics_v25_closeout.json"


def _provider_matrix_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "provider_parity"
        / "vnext_plus25_provider_matrix.json"
    )


def _doc_path() -> Path:
    return _repo_root() / "docs" / "CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md"


def _extract_json_block(markdown: str) -> dict[str, object]:
    marker = "```json\n"
    start = markdown.find(marker)
    assert start != -1, "json fenced block start not found"
    start += len(marker)
    end = markdown.find("\n```", start)
    assert end != -1, "json fenced block end not found"
    return json.loads(markdown[start:end])


def test_build_core_ir_proposer_transfer_report_payload_is_deterministic() -> None:
    first = build_core_ir_proposer_transfer_report_vnext_plus25_payload(
        vnext_plus25_manifest_path=_manifest_path(),
        provider_matrix_path=_provider_matrix_path(),
        stop_gate_metrics_path=_metrics_path(),
    )
    second = build_core_ir_proposer_transfer_report_vnext_plus25_payload(
        vnext_plus25_manifest_path=_manifest_path(),
        provider_matrix_path=_provider_matrix_path(),
        stop_gate_metrics_path=_metrics_path(),
    )

    assert first["schema"] == CORE_IR_PROPOSER_TRANSFER_REPORT_VNEXT_PLUS25_SCHEMA
    assert canonical_json(first) == canonical_json(second)
    assert first["coverage_summary"]["valid"] is True
    assert first["replay_summary"]["valid"] is True


def test_build_core_ir_proposer_transfer_report_matches_locked_doc_json() -> None:
    payload = build_core_ir_proposer_transfer_report_vnext_plus25_payload(
        vnext_plus25_manifest_path=_manifest_path(),
        provider_matrix_path=_provider_matrix_path(),
        stop_gate_metrics_path=_metrics_path(),
    )
    doc_payload = _extract_json_block(_doc_path().read_text(encoding="utf-8"))
    assert canonical_json(payload) == canonical_json(doc_payload)


def test_build_core_ir_proposer_transfer_report_script_writes_markdown(tmp_path: Path) -> None:
    repo_root = _repo_root()
    script = (
        repo_root
        / "apps"
        / "api"
        / "scripts"
        / "build_core_ir_proposer_transfer_report_vnext_plus25.py"
    )
    out_markdown = tmp_path / "CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md"

    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            "--vnext-plus25-manifest",
            str(_manifest_path()),
            "--provider-matrix",
            str(_provider_matrix_path()),
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
    assert payload["schema"] == CORE_IR_PROPOSER_TRANSFER_REPORT_VNEXT_PLUS25_SCHEMA
    assert payload["replay_summary"]["all_passed"] is True
