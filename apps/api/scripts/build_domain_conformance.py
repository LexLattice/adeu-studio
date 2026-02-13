from __future__ import annotations

import argparse
import sys
from pathlib import Path

from adeu_api.urm_domain_conformance import build_domain_conformance
from urm_runtime.hashing import canonical_json


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build offline cross-domain conformance report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("artifacts/domain_conformance.json"),
        help="Output path for domain_conformance@1 JSON report.",
    )
    parser.add_argument(
        "--events-dir",
        type=Path,
        default=Path("artifacts/domain_conformance_events"),
        help="Directory used for deterministic per-domain event fixture generation.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    report = build_domain_conformance(events_dir=args.events_dir)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(canonical_json(report) + "\n", encoding="utf-8")
    return 0 if report.get("valid") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
