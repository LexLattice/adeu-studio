from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json
from urm_runtime.stop_gate_registry import discover_repo_root
from urm_runtime.tooling_transfer_report_vnext_plus26 import (
    TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA,
    ToolingTransferReportVNextPlus26Error,
    build_tooling_transfer_report_vnext_plus26_payload,
    canonical_payload_hash,
    extract_unique_schema_payload_from_markdown,
    render_tooling_transfer_report_vnext_plus26_markdown,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic tooling transfer report for vNext+26.",
    )
    parser.add_argument(
        "--vnext-plus26-manifest",
        type=Path,
        default=None,
        help="Path to vNext+26 stop-gate manifest JSON.",
    )
    parser.add_argument(
        "--stop-gate-metrics",
        type=Path,
        default=None,
        help="Path to vNext+26 closeout stop-gate metrics JSON.",
    )
    parser.add_argument(
        "--s9-metrics-path",
        type=Path,
        default=None,
        help="Path to vNext+25 closeout stop-gate metrics JSON used by S9 summary.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Path to tooling transfer report markdown.",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="Write markdown output after parity check passes.",
    )
    return parser.parse_args(argv)


def _emit_error(*, code: str, message: str, context: dict[str, Any] | None = None) -> None:
    payload = {
        "code": code,
        "message": message,
        "context": dict(context or {}),
    }
    sys.stderr.write(canonical_json(payload) + "\n")


def _default_paths(*, repo_root: Path) -> dict[str, Path]:
    return {
        "vnext_plus26_manifest": repo_root
        / "apps"
        / "api"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus26_manifest.json",
        "stop_gate_metrics": repo_root / "artifacts" / "stop_gate" / "metrics_v26_closeout.json",
        "s9_metrics_path": repo_root / "artifacts" / "stop_gate" / "metrics_v25_closeout.json",
        "out": repo_root / "docs" / "TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md",
    }


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)

    repo_root = discover_repo_root(Path(__file__).resolve())
    if repo_root is None:
        _emit_error(
            code="TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_REPO_ROOT_NOT_FOUND",
            message="repository root not found from script path",
        )
        return 1

    defaults = _default_paths(repo_root=repo_root)
    manifest_path = args.vnext_plus26_manifest or defaults["vnext_plus26_manifest"]
    stop_gate_metrics_path = args.stop_gate_metrics or defaults["stop_gate_metrics"]
    s9_metrics_path = args.s9_metrics_path or defaults["s9_metrics_path"]
    out_path = args.out or defaults["out"]

    try:
        baseline_markdown = out_path.read_text(encoding="utf-8")
    except OSError as exc:
        _emit_error(
            code="TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_BASELINE_READ_FAILED",
            message="failed to read baseline markdown report",
            context={"path": str(out_path), "error": str(exc)},
        )
        return 1

    try:
        baseline_payload = extract_unique_schema_payload_from_markdown(
            markdown_text=baseline_markdown,
            schema=TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA,
        )
    except ToolingTransferReportVNextPlus26Error as exc:
        _emit_error(
            code="TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_BASELINE_EXTRACTION_FAILED",
            message="failed to extract baseline JSON payload",
            context={"path": str(out_path), "error": str(exc)},
        )
        return 1

    try:
        regenerated_payload = build_tooling_transfer_report_vnext_plus26_payload(
            vnext_plus26_manifest_path=manifest_path,
            stop_gate_metrics_path=stop_gate_metrics_path,
            s9_metrics_path=s9_metrics_path,
        )
    except ToolingTransferReportVNextPlus26Error as exc:
        _emit_error(
            code="TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_PAYLOAD_BUILD_FAILED",
            message="failed to build regenerated vnext+26 payload",
            context={
                "manifest_path": str(manifest_path),
                "stop_gate_metrics_path": str(stop_gate_metrics_path),
                "s9_metrics_path": str(s9_metrics_path),
                "error": str(exc),
            },
        )
        return 1

    baseline_hash = canonical_payload_hash(baseline_payload)
    regenerated_hash = canonical_payload_hash(regenerated_payload)
    if regenerated_hash != baseline_hash:
        _emit_error(
            code="TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_PARITY_MISMATCH",
            message="regenerated payload hash does not match baseline payload hash",
            context={
                "baseline_hash": baseline_hash,
                "regenerated_hash": regenerated_hash,
            },
        )
        return 1

    if not args.write:
        return 0

    markdown = render_tooling_transfer_report_vnext_plus26_markdown(regenerated_payload)
    try:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(markdown, encoding="utf-8")
    except OSError as exc:
        _emit_error(
            code="TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_WRITE_FAILED",
            message="failed to write markdown report",
            context={"path": str(out_path), "error": str(exc)},
        )
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
