from __future__ import annotations

import argparse
import sys
from pathlib import Path

from adeu_api.integrity_transfer_report_vnext_plus17 import (
    build_integrity_transfer_report_vnext_plus17_payload,
    integrity_transfer_report_vnext_plus17_markdown,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic integrity transfer report for vNext+17.",
    )
    parser.add_argument(
        "--vnext-plus17-manifest",
        type=Path,
        default=Path("apps/api/fixtures/stop_gate/vnext_plus17_manifest.json"),
        help="vNext+17 locked stop-gate manifest path.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/INTEGRITY_TRANSFER_REPORT_vNEXT_PLUS17.md"),
        help="Output markdown path.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    payload = build_integrity_transfer_report_vnext_plus17_payload(
        vnext_plus17_manifest_path=args.vnext_plus17_manifest,
    )
    markdown = integrity_transfer_report_vnext_plus17_markdown(payload)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(markdown, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
