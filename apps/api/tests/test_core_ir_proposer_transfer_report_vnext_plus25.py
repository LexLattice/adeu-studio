from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import urm_runtime.core_ir_proposer_transfer_report_vnext_plus25 as proposer_report_module
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


def _fixture_run_paths(provider: str) -> dict[str, Path]:
    fixture_root = _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus25"
    return {
        "core_ir_proposer_request_path": (
            fixture_root / f"core_ir_proposer_request_case_a_{provider}.json"
        ),
        "core_ir_proposer_response_path": (
            fixture_root / f"core_ir_proposer_response_case_a_{provider}.json"
        ),
        "core_ir_proposal_packet_path": (
            fixture_root / f"core_ir_proposal_packet_case_a_{provider}.json"
        ),
    }


def _write_modified_fixture_run(
    *,
    tmp_path: Path,
    prefix: str,
    provider: str,
    summary_delta: int = 0,
) -> dict[str, str]:
    source_paths = _fixture_run_paths(provider)
    request_payload = json.loads(
        source_paths["core_ir_proposer_request_path"].read_text(encoding="utf-8")
    )
    response_payload = json.loads(
        source_paths["core_ir_proposer_response_path"].read_text(encoding="utf-8")
    )
    packet_payload = json.loads(
        source_paths["core_ir_proposal_packet_path"].read_text(encoding="utf-8")
    )

    if summary_delta:
        packet_summary = packet_payload["summary"]
        response_summary = response_payload["proposal_packet"]["summary"]
        packet_summary["assertion_node_count"] = (
            int(packet_summary["assertion_node_count"]) + summary_delta
        )
        packet_summary["relation_edge_count"] = (
            int(packet_summary["relation_edge_count"]) + summary_delta
        )
        response_summary["assertion_node_count"] = (
            int(response_summary["assertion_node_count"]) + summary_delta
        )
        response_summary["relation_edge_count"] = (
            int(response_summary["relation_edge_count"]) + summary_delta
        )

    request_name = f"{prefix}_request_{provider}.json"
    response_name = f"{prefix}_response_{provider}.json"
    packet_name = f"{prefix}_packet_{provider}.json"
    (tmp_path / request_name).write_text(canonical_json(request_payload) + "\n", encoding="utf-8")
    (tmp_path / response_name).write_text(canonical_json(response_payload) + "\n", encoding="utf-8")
    (tmp_path / packet_name).write_text(canonical_json(packet_payload) + "\n", encoding="utf-8")
    return {
        "provider": provider,
        "core_ir_proposer_request_path": request_name,
        "core_ir_proposer_response_path": response_name,
        "core_ir_proposal_packet_path": packet_name,
    }


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


def test_contract_summary_allows_different_summaries_across_fixtures(tmp_path: Path) -> None:
    fixture_a_runs = [
        _write_modified_fixture_run(tmp_path=tmp_path, prefix="fixture_a", provider=provider)
        for provider in ("codex", "mock", "openai")
    ]
    fixture_b_runs = [
        _write_modified_fixture_run(
            tmp_path=tmp_path,
            prefix="fixture_b",
            provider=provider,
            summary_delta=1,
        )
        for provider in ("codex", "mock", "openai")
    ]

    manifest = {
        "core_ir_proposer_contract_valid_fixtures": [
            {"fixture_id": "fixture_a", "runs": fixture_a_runs},
            {"fixture_id": "fixture_b", "runs": fixture_b_runs},
        ]
    }
    summary = proposer_report_module._contract_summary(
        manifest_path=tmp_path / "vnext_plus25_manifest.json",
        manifest=manifest,
        contract_pct=100.0,
    )
    assert summary["valid"] is True
    assert summary["core_ir_proposer_contract_fixture_count"] == 2
    assert summary["core_ir_proposer_contract_run_count"] == 6
    assert summary["summary_invariants"]["assertion_node_count"] == 11


def test_parity_summary_detects_drift_in_non_last_fixture(tmp_path: Path) -> None:
    fixture_a_runs = [
        _write_modified_fixture_run(
            tmp_path=tmp_path,
            prefix="parity_a",
            provider=provider,
            summary_delta=(1 if provider == "codex" else 0),
        )
        for provider in ("codex", "mock", "openai")
    ]
    fixture_b_runs = [
        _write_modified_fixture_run(tmp_path=tmp_path, prefix="parity_b", provider=provider)
        for provider in ("codex", "mock", "openai")
    ]

    manifest = {
        "core_ir_proposer_provider_parity_fixtures": [
            {"fixture_id": "parity_a", "runs": fixture_a_runs},
            {"fixture_id": "parity_b", "runs": fixture_b_runs},
        ]
    }
    summary = proposer_report_module._parity_summary(
        manifest_path=tmp_path / "vnext_plus25_manifest.json",
        manifest=manifest,
        parity_pct=100.0,
    )
    assert summary["valid"] is True
    assert summary["core_ir_proposer_parity_fixture_count"] == 2
    assert summary["core_ir_proposer_parity_run_count"] == 6
    assert summary["parity_fingerprint_hash_match"] is False
