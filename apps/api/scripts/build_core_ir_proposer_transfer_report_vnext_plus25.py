from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from urm_runtime.core_ir_proposer_transfer_report_vnext_plus25 import (
    build_core_ir_proposer_transfer_report_vnext_plus25_payload,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic core-ir proposer transfer report for vNext+25.",
    )
    parser.add_argument(
        "--vnext-plus25-manifest",
        type=Path,
        default=Path("apps/api/fixtures/stop_gate/vnext_plus25_manifest.json"),
        help="vNext+25 locked stop-gate manifest path.",
    )
    parser.add_argument(
        "--provider-matrix",
        type=Path,
        default=Path("apps/api/fixtures/provider_parity/vnext_plus25_provider_matrix.json"),
        help="vNext+25 provider matrix path.",
    )
    parser.add_argument(
        "--stop-gate-metrics",
        type=Path,
        default=Path("artifacts/stop_gate/metrics_v25_closeout.json"),
        help="vNext+25 closeout stop-gate metrics path.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md"),
        help="Output markdown path.",
    )
    return parser.parse_args(argv)


def _markdown(payload: dict[str, object]) -> str:
    body = json.dumps(payload, indent=2, ensure_ascii=False)
    return (
        "# Core-IR Proposer Transfer Report vNext+25\n\n"
        "Deterministic transfer summary generated from fixture-backed vNext+25 core-ir "
        "proposer request/response/packet artifacts.\n\n"
        "```json\n"
        f"{body}\n"
        "```\n"
    )


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    payload = build_core_ir_proposer_transfer_report_vnext_plus25_payload(
        vnext_plus25_manifest_path=args.vnext_plus25_manifest,
        provider_matrix_path=args.provider_matrix,
        stop_gate_metrics_path=args.stop_gate_metrics,
    )
    markdown = _markdown(payload)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(markdown, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
