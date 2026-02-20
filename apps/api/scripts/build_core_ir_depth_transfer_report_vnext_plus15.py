from __future__ import annotations

import argparse
import sys
from pathlib import Path

from adeu_api.core_ir_depth_transfer_report_vnext_plus15 import (
    build_core_ir_depth_transfer_report_vnext_plus15_payload,
    core_ir_depth_transfer_report_vnext_plus15_markdown,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic core-ir depth transfer report for vNext+15.",
    )
    parser.add_argument(
        "--vnext-plus15-manifest",
        type=Path,
        default=Path("apps/api/fixtures/stop_gate/vnext_plus15_manifest.json"),
        help="vNext+15 locked stop-gate manifest path.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/CORE_IR_DEPTH_TRANSFER_REPORT_vNEXT_PLUS15.md"),
        help="Output markdown path.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    payload = build_core_ir_depth_transfer_report_vnext_plus15_payload(
        vnext_plus15_manifest_path=args.vnext_plus15_manifest,
    )
    markdown = core_ir_depth_transfer_report_vnext_plus15_markdown(payload)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(markdown, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
