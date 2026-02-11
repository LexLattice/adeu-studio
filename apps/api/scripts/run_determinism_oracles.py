from __future__ import annotations

import argparse
from pathlib import Path

from adeu_api.determinism_oracles import write_determinism_oracle_report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run determinism oracles for bridge/questions/patch paths."
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("artifacts/determinism_oracles.json"),
        help="Output JSON path",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    report = write_determinism_oracle_report(args.out)
    summary = report["summary"]
    print(f"wrote {args.out}")
    print(
        f"total={summary['total']} "
        f"passed={summary['passed']} "
        f"failed={summary['failed']}"
    )


if __name__ == "__main__":
    main()
