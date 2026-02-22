from __future__ import annotations

import argparse
from pathlib import Path

from adeu_api.read_surface_transfer_report_vnext_plus19 import (
    build_read_surface_transfer_report_vnext_plus19_payload,
    read_surface_transfer_report_vnext_plus19_markdown,
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic vNext+19 read-surface transfer-report markdown.",
    )
    parser.add_argument(
        "--vnext-plus19-manifest-hash",
        required=True,
        help="vNext+19 manifest sha256 hash (64 lowercase hex chars)",
    )
    parser.add_argument(
        "--artifact-id",
        action="append",
        dest="artifact_ids",
        help=(
            "Optional core-ir artifact id to include. "
            "Repeat flag to include multiple entries. Defaults to full catalog."
        ),
    )
    parser.add_argument(
        "--catalog-path",
        type=Path,
        default=None,
        help="Optional read-surface catalog override path",
    )
    parser.add_argument(
        "--include-correlations",
        action="store_true",
        help=(
            "Include optional correlations block in generated payloads "
            "prior to summary aggregation"
        ),
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/READ_SURFACE_TRANSFER_REPORT_vNEXT_PLUS19.md"),
        help="Output markdown path",
    )
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    payload = build_read_surface_transfer_report_vnext_plus19_payload(
        vnext_plus19_manifest_hash=args.vnext_plus19_manifest_hash,
        artifact_ids=args.artifact_ids,
        include_correlations=args.include_correlations,
        catalog_path=args.catalog_path,
    )
    markdown = read_surface_transfer_report_vnext_plus19_markdown(payload)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(markdown, encoding="utf-8")


if __name__ == "__main__":
    main()
