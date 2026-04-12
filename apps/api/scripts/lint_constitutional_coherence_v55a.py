from __future__ import annotations

import argparse
import sys
from pathlib import Path

from adeu_constitutional_coherence import (
    DEFAULT_ADMISSIONS_PATH,
    render_report_payload,
    render_unresolved_register_payload,
    run_constitutional_coherence_v55a,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the warning-only V55-A constitutional coherence starter checker over "
            "the admitted seed set."
        )
    )
    parser.add_argument(
        "--admissions",
        default=DEFAULT_ADMISSIONS_PATH,
        help=(
            "Path to the constitutional_support_admission_record@1 list. "
            "Defaults to the committed V55-A starter fixture."
        ),
    )
    parser.add_argument(
        "--report-output",
        default=None,
        help="Optional path to write constitutional_coherence_report@1 JSON.",
    )
    parser.add_argument(
        "--unresolved-output",
        default=None,
        help="Optional path to write constitutional_unresolved_seam_register@1 JSON.",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Repository root path. Defaults to discovery from script location.",
    )
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    report, unresolved = run_constitutional_coherence_v55a(
        repo_root_path=args.repo_root,
        admissions_path=Path(args.admissions),
    )
    report_payload = render_report_payload(report)
    unresolved_payload = render_unresolved_register_payload(unresolved)
    if args.report_output:
        _write_text(Path(args.report_output), report_payload)
    else:
        sys.stdout.write(report_payload)
    if args.unresolved_output:
        _write_text(Path(args.unresolved_output), unresolved_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
