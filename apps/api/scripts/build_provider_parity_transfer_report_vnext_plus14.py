from __future__ import annotations

import argparse
import sys
from pathlib import Path

from adeu_api.provider_parity_transfer_report_vnext_plus14 import (
    build_provider_parity_transfer_report_vnext_plus14_payload,
    provider_parity_transfer_report_vnext_plus14_markdown,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic provider parity transfer report for vNext+14.",
    )
    parser.add_argument(
        "--vnext-plus14-manifest",
        type=Path,
        default=Path("apps/api/fixtures/stop_gate/vnext_plus14_manifest.json"),
        help="vNext+14 locked stop-gate manifest path.",
    )
    parser.add_argument(
        "--provider-matrix",
        type=Path,
        default=Path("apps/api/fixtures/provider_parity/vnext_plus14_provider_matrix.json"),
        help="vNext+14 provider parity matrix path.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/PROVIDER_PARITY_TRANSFER_REPORT_vNEXT_PLUS14.md"),
        help="Output markdown path.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    payload = build_provider_parity_transfer_report_vnext_plus14_payload(
        vnext_plus14_manifest_path=args.vnext_plus14_manifest,
        provider_matrix_path=args.provider_matrix,
    )
    markdown = provider_parity_transfer_report_vnext_plus14_markdown(payload)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(markdown, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
