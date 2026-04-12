from __future__ import annotations

import argparse
import sys
import warnings
from pathlib import Path

warnings.filterwarnings(
    "ignore",
    message=(
        r'Field name "schema" in "Constitutional.*" shadows an attribute in parent '
        r'"BaseModel"'
    ),
    category=UserWarning,
)

from adeu_constitutional_coherence import (  # noqa: E402
    DEFAULT_V55B_ADMISSIONS_PATH,
    DEFAULT_V55B_DRIFT_RECORD_PATH,
    render_report_payload,
    render_unresolved_register_payload,
    run_constitutional_coherence_v55b,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the warning-only V55-B constitutional coherence descendant-trial "
            "hardening checker over the admitted seed set and explicit V55-A handoff."
        )
    )
    parser.add_argument(
        "--admissions",
        type=Path,
        default=DEFAULT_V55B_ADMISSIONS_PATH,
        help=(
            "Path to the constitutional_support_admission_record@1 list. "
            "Defaults to the committed V55-B fixture."
        ),
    )
    parser.add_argument(
        "--lane-drift",
        type=Path,
        default=DEFAULT_V55B_DRIFT_RECORD_PATH,
        help=(
            "Path to the constitutional_coherence_lane_drift_record@1 handoff. "
            "Defaults to the committed V55-B fixture."
        ),
    )
    parser.add_argument(
        "--report-output",
        type=Path,
        default=None,
        help="Optional path to write constitutional_coherence_report@1 JSON.",
    )
    parser.add_argument(
        "--unresolved-output",
        type=Path,
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
    try:
        report, unresolved = run_constitutional_coherence_v55b(
            repo_root_path=args.repo_root,
            admissions_path=args.admissions,
            lane_drift_path=args.lane_drift,
        )
    except (ValueError, FileNotFoundError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 1
    report_payload = render_report_payload(report)
    unresolved_payload = render_unresolved_register_payload(unresolved)
    if args.report_output:
        _write_text(args.report_output, report_payload)
    else:
        sys.stdout.write(report_payload)
    if args.unresolved_output:
        _write_text(args.unresolved_output, unresolved_payload)
    elif unresolved.entry_count > 0:
        sys.stderr.write(unresolved_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
