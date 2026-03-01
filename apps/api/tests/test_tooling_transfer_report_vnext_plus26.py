from __future__ import annotations

import importlib.util
import json
from pathlib import Path
from types import ModuleType

import pytest
from urm_runtime.hashing import canonical_json
from urm_runtime.tooling_transfer_report_vnext_plus26 import (
    S9_REQUIRED_METRIC_KEYS,
    TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA,
    ToolingTransferReportVNextPlus26Error,
    build_tooling_transfer_report_vnext_plus26_payload,
    canonical_payload_hash,
    extract_unique_schema_payload_from_markdown,
    render_tooling_transfer_report_vnext_plus26_markdown,
)


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus26_manifest.json"


def _stop_gate_metrics_path() -> Path:
    return _repo_root() / "artifacts" / "stop_gate" / "metrics_v26_closeout.json"


def _s9_metrics_path() -> Path:
    return _repo_root() / "artifacts" / "stop_gate" / "metrics_v25_closeout.json"


def _doc_path() -> Path:
    return _repo_root() / "docs" / "TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md"


def _load_script_module() -> ModuleType:
    module_path = (
        _repo_root()
        / "apps"
        / "api"
        / "scripts"
        / "build_tooling_transfer_report_vnext_plus26.py"
    )
    spec = importlib.util.spec_from_file_location(
        "build_tooling_transfer_report_vnext_plus26_for_tests",
        module_path,
    )
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _locked_doc_payload() -> dict[str, object]:
    return extract_unique_schema_payload_from_markdown(
        markdown_text=_doc_path().read_text(encoding="utf-8"),
        schema=TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA,
    )


def test_build_tooling_transfer_report_payload_is_deterministic() -> None:
    first = build_tooling_transfer_report_vnext_plus26_payload(
        vnext_plus26_manifest_path=_manifest_path(),
        stop_gate_metrics_path=_stop_gate_metrics_path(),
        s9_metrics_path=_s9_metrics_path(),
    )
    second = build_tooling_transfer_report_vnext_plus26_payload(
        vnext_plus26_manifest_path=_manifest_path(),
        stop_gate_metrics_path=_stop_gate_metrics_path(),
        s9_metrics_path=_s9_metrics_path(),
    )

    assert first["schema"] == TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA
    assert canonical_json(first) == canonical_json(second)
    assert canonical_payload_hash(first) == canonical_payload_hash(second)

    expected_top_level_keys = (
        "schema",
        "vnext_plus26_manifest_hash",
        "coverage_summary",
        "stop_gate_input_model_parity_summary",
        "transfer_report_builder_parity_summary",
        "s9_trigger_check_summary",
        "replay_summary",
    )
    assert tuple(first.keys()) == expected_top_level_keys

    expected_runtime_observability_keys = (
        "elapsed_ms",
        "total_fixtures",
        "total_replays",
        "bytes_hashed_per_replay",
        "bytes_hashed_total",
    )
    runtime_observability = first["replay_summary"]["runtime_observability"]
    assert tuple(runtime_observability.keys()) == expected_runtime_observability_keys


def test_build_tooling_transfer_report_matches_locked_doc_json() -> None:
    payload = build_tooling_transfer_report_vnext_plus26_payload(
        vnext_plus26_manifest_path=_manifest_path(),
        stop_gate_metrics_path=_stop_gate_metrics_path(),
        s9_metrics_path=_s9_metrics_path(),
    )
    doc_payload = _locked_doc_payload()
    assert canonical_json(payload) == canonical_json(doc_payload)


@pytest.mark.parametrize(
    ("markdown_text", "expected_fragment"),
    [
        ("# report without fenced block\n", "must include at least one fenced JSON block"),
        (
            "```json\n"
            + json.dumps({"schema": "other.schema", "value": 1}, ensure_ascii=False)
            + "\n```\n",
            "does not contain required schema block",
        ),
        (
            "```json\n"
            + json.dumps(
                {"schema": TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA, "value": 1},
                ensure_ascii=False,
            )
            + "\n```\n"
            "```json\n"
            + json.dumps(
                {"schema": TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA, "value": 2},
                ensure_ascii=False,
            )
            + "\n```\n",
            "contains duplicate required schema blocks",
        ),
        ("```json\n{\n```\n", "contains invalid fenced JSON block"),
    ],
)
def test_extract_unique_schema_payload_from_markdown_fails_closed(
    markdown_text: str,
    expected_fragment: str,
) -> None:
    with pytest.raises(ToolingTransferReportVNextPlus26Error) as exc_info:
        extract_unique_schema_payload_from_markdown(
            markdown_text=markdown_text,
            schema=TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA,
        )
    assert expected_fragment in str(exc_info.value)


def test_script_check_only_passes_without_mutating_output(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    script_module = _load_script_module()
    baseline_text = _doc_path().read_text(encoding="utf-8")
    out_path = tmp_path / "TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md"
    out_path.write_text(baseline_text, encoding="utf-8")

    exit_code = script_module.main(
        [
            "--vnext-plus26-manifest",
            str(_manifest_path()),
            "--stop-gate-metrics",
            str(_stop_gate_metrics_path()),
            "--s9-metrics-path",
            str(_s9_metrics_path()),
            "--out",
            str(out_path),
        ]
    )

    assert exit_code == 0
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""
    assert out_path.read_text(encoding="utf-8") == baseline_text


def test_script_parity_uses_parsed_json_not_markdown_bytes(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    script_module = _load_script_module()
    payload = _locked_doc_payload()

    out_path = tmp_path / "TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md"
    out_path.write_text(
        "# Alternate Wrapper\n\n"
        "This wrapper is intentionally different while keeping the payload identical.\n\n"
        "```json\n"
        f"{json.dumps(payload, separators=(',', ':'), ensure_ascii=False)}\n"
        "```\n",
        encoding="utf-8",
    )

    check_exit_code = script_module.main(
        [
            "--vnext-plus26-manifest",
            str(_manifest_path()),
            "--stop-gate-metrics",
            str(_stop_gate_metrics_path()),
            "--s9-metrics-path",
            str(_s9_metrics_path()),
            "--out",
            str(out_path),
        ]
    )
    assert check_exit_code == 0

    write_exit_code = script_module.main(
        [
            "--vnext-plus26-manifest",
            str(_manifest_path()),
            "--stop-gate-metrics",
            str(_stop_gate_metrics_path()),
            "--s9-metrics-path",
            str(_s9_metrics_path()),
            "--out",
            str(out_path),
            "--write",
        ]
    )
    assert write_exit_code == 0
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""

    expected_markdown = render_tooling_transfer_report_vnext_plus26_markdown(
        build_tooling_transfer_report_vnext_plus26_payload(
            vnext_plus26_manifest_path=_manifest_path(),
            stop_gate_metrics_path=_stop_gate_metrics_path(),
            s9_metrics_path=_s9_metrics_path(),
        )
    )
    assert out_path.read_text(encoding="utf-8") == expected_markdown


def test_script_write_mode_fails_closed_without_clobber_on_parity_mismatch(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    script_module = _load_script_module()
    payload = _locked_doc_payload()
    payload["vnext_plus26_manifest_hash"] = "parity_drift"

    out_path = tmp_path / "TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md"
    mutated_text = render_tooling_transfer_report_vnext_plus26_markdown(payload)
    out_path.write_text(mutated_text, encoding="utf-8")

    exit_code = script_module.main(
        [
            "--vnext-plus26-manifest",
            str(_manifest_path()),
            "--stop-gate-metrics",
            str(_stop_gate_metrics_path()),
            "--s9-metrics-path",
            str(_s9_metrics_path()),
            "--out",
            str(out_path),
            "--write",
        ]
    )

    assert exit_code == 1
    captured = capsys.readouterr()
    assert captured.out == ""
    error_payload = json.loads(captured.err)
    assert error_payload["code"] == "TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_PARITY_MISMATCH"
    assert out_path.read_text(encoding="utf-8") == mutated_text


@pytest.mark.parametrize(
    "markdown_text",
    [
        "# No fenced block\n",
        (
            "```json\n"
            + json.dumps({"schema": "other.schema", "value": 1}, ensure_ascii=False)
            + "\n```\n"
        ),
        (
            "```json\n"
            + json.dumps(
                {"schema": TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA, "value": 1},
                ensure_ascii=False,
            )
            + "\n```\n"
            "```json\n"
            + json.dumps(
                {"schema": TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA, "value": 2},
                ensure_ascii=False,
            )
            + "\n```\n"
        ),
    ],
)
def test_script_fails_closed_when_baseline_schema_block_invalid(
    tmp_path: Path,
    markdown_text: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    script_module = _load_script_module()
    out_path = tmp_path / "TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md"
    out_path.write_text(markdown_text, encoding="utf-8")
    before_bytes = out_path.read_bytes()

    exit_code = script_module.main(
        [
            "--vnext-plus26-manifest",
            str(_manifest_path()),
            "--stop-gate-metrics",
            str(_stop_gate_metrics_path()),
            "--s9-metrics-path",
            str(_s9_metrics_path()),
            "--out",
            str(out_path),
        ]
    )

    assert exit_code == 1
    captured = capsys.readouterr()
    assert captured.out == ""
    error_payload = json.loads(captured.err)
    assert (
        error_payload["code"]
        == "TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_BASELINE_EXTRACTION_FAILED"
    )
    assert out_path.read_bytes() == before_bytes


def test_builder_fails_closed_when_s9_required_metric_is_missing(tmp_path: Path) -> None:
    s9_payload = json.loads(_s9_metrics_path().read_text(encoding="utf-8"))
    del s9_payload["metrics"][S9_REQUIRED_METRIC_KEYS[0]]
    s9_path = tmp_path / "metrics_v25_missing_required.json"
    s9_path.write_text(
        json.dumps(s9_payload, separators=(",", ":"), ensure_ascii=False),
        encoding="utf-8",
    )

    with pytest.raises(ToolingTransferReportVNextPlus26Error) as exc_info:
        build_tooling_transfer_report_vnext_plus26_payload(
            vnext_plus26_manifest_path=_manifest_path(),
            stop_gate_metrics_path=_stop_gate_metrics_path(),
            s9_metrics_path=s9_path,
        )

    assert "required metric is missing" in str(exc_info.value)
