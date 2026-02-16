from __future__ import annotations

import argparse
import sys
from pathlib import Path

from adeu_api.portability_transfer_report_vnext_plus11 import (
    build_portability_transfer_report_vnext_plus11_payload,
    portability_transfer_report_vnext_plus11_markdown,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic portability transfer report for vNext+11.",
    )
    parser.add_argument(
        "--vnext-plus11-manifest",
        type=Path,
        default=Path("apps/api/fixtures/stop_gate/vnext_plus11_manifest.json"),
        help="vNext+11 locked stop-gate manifest path.",
    )
    parser.add_argument(
        "--domain-conformance",
        type=Path,
        default=Path("artifacts/domain_conformance.json"),
        help="domain_conformance@1 JSON artifact path.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/PORTABILITY_TRANSFER_REPORT_vNEXT_PLUS11.md"),
        help="Output markdown path.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    payload = build_portability_transfer_report_vnext_plus11_payload(
        vnext_plus11_manifest_path=args.vnext_plus11_manifest,
        domain_conformance_path=args.domain_conformance,
    )
    markdown = portability_transfer_report_vnext_plus11_markdown(payload)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(markdown, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
