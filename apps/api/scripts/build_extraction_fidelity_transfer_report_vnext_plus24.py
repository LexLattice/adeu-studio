from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from urm_runtime.extraction_fidelity_transfer_report_vnext_plus24 import (
    build_extraction_fidelity_transfer_report_vnext_plus24_payload,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic extraction-fidelity transfer report for vNext+24.",
    )
    parser.add_argument(
        "--vnext-plus24-manifest",
        type=Path,
        default=Path("apps/api/fixtures/stop_gate/vnext_plus24_manifest.json"),
        help="vNext+24 locked stop-gate manifest path.",
    )
    parser.add_argument(
        "--stop-gate-metrics",
        type=Path,
        default=Path("artifacts/stop_gate/metrics_v24_closeout.json"),
        help="vNext+24 closeout stop-gate metrics path.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md"),
        help="Output markdown path.",
    )
    return parser.parse_args(argv)


def _markdown(payload: dict[str, object]) -> str:
    body = json.dumps(payload, indent=2, ensure_ascii=False)
    return (
        "# Extraction-Fidelity Transfer Report vNext+24\n\n"
        "Deterministic transfer summary generated from fixture-backed vNext+24 "
        "extraction-fidelity packet/projection artifacts.\n\n"
        "```json\n"
        f"{body}\n"
        "```\n"
    )


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    payload = build_extraction_fidelity_transfer_report_vnext_plus24_payload(
        vnext_plus24_manifest_path=args.vnext_plus24_manifest,
        stop_gate_metrics_path=args.stop_gate_metrics,
    )
    markdown = _markdown(payload)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(markdown, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
