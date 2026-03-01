from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from urm_runtime.tooling_transfer_report_vnext_plus26 import (
    TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA,
    build_tooling_transfer_report_vnext_plus26_payload,
    canonical_payload_hash,
    extract_unique_schema_payload_from_markdown,
)


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _v26_closeout_metrics_path() -> Path:
    return _repo_root() / "artifacts" / "stop_gate" / "metrics_v26_closeout.json"


def _v25_closeout_metrics_path() -> Path:
    return _repo_root() / "artifacts" / "stop_gate" / "metrics_v25_closeout.json"


def _v26_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus26_manifest.json"


def _v26_transfer_report_path() -> Path:
    return _repo_root() / "docs" / "TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md"


def _locked_v26_transfer_payload() -> dict[str, Any]:
    return extract_unique_schema_payload_from_markdown(
        markdown_text=_v26_transfer_report_path().read_text(encoding="utf-8"),
        schema=TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA,
    )


def test_b4_historical_continuity_metrics_remain_frozen_in_v26_closeout_metrics() -> None:
    metrics_payload = _load_json(_v26_closeout_metrics_path())
    assert metrics_payload["schema"] == "stop_gate_metrics@1"

    metrics = metrics_payload["metrics"]
    assert metrics["artifact_stop_gate_input_model_parity_pct"] == 100.0
    assert metrics["artifact_transfer_report_builder_parity_pct"] == 100.0


def test_b4_transfer_report_regeneration_matches_locked_payload_hash() -> None:
    regenerated_payload = build_tooling_transfer_report_vnext_plus26_payload(
        vnext_plus26_manifest_path=_v26_manifest_path(),
        stop_gate_metrics_path=_v26_closeout_metrics_path(),
        s9_metrics_path=_v25_closeout_metrics_path(),
    )
    locked_payload = _locked_v26_transfer_payload()

    assert regenerated_payload["schema"] == TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA
    assert canonical_payload_hash(regenerated_payload) == canonical_payload_hash(locked_payload)


def test_b4_historical_continuity_metrics_remain_frozen_in_v26_transfer_payload() -> None:
    payload = build_tooling_transfer_report_vnext_plus26_payload(
        vnext_plus26_manifest_path=_v26_manifest_path(),
        stop_gate_metrics_path=_v26_closeout_metrics_path(),
        s9_metrics_path=_v25_closeout_metrics_path(),
    )

    stop_gate_input_model_parity = payload["stop_gate_input_model_parity_summary"]
    transfer_builder_parity = payload["transfer_report_builder_parity_summary"]
    replay_determinism = payload["replay_summary"]["determinism_pct"]

    assert stop_gate_input_model_parity["artifact_stop_gate_input_model_parity_pct"] == 100.0
    assert transfer_builder_parity["artifact_transfer_report_builder_parity_pct"] == 100.0
    assert replay_determinism["artifact_stop_gate_input_model_parity_pct"] == 100.0
    assert replay_determinism["artifact_transfer_report_builder_parity_pct"] == 100.0
