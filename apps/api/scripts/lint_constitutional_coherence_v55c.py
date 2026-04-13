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
    DEFAULT_V55C_ADMISSIONS_PATH,
    DEFAULT_V55C_DRIFT_RECORD_PATH,
    DEFAULT_V55C_V55A_REPORT_PATH,
    DEFAULT_V55C_V55A_UNRESOLVED_PATH,
    DEFAULT_V55C_V55B_DRIFT_PATH,
    DEFAULT_V55C_V55B_EVIDENCE_PATH,
    DEFAULT_V55C_V55B_REPORT_PATH,
    DEFAULT_V55C_V55B_UNRESOLVED_PATH,
    render_governance_calibration_register_payload,
    render_migration_decision_register_payload,
    run_constitutional_coherence_v55c,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the advisory-only V55-C constitutional coherence governance and "
            "migration decision checker over the shipped V55-A/V55-B evidence surfaces."
        )
    )
    parser.add_argument(
        "--admissions",
        type=Path,
        default=DEFAULT_V55C_ADMISSIONS_PATH,
        help=(
            "Path to the constitutional_support_admission_record@1 list. "
            "Defaults to the committed V55-C fixture."
        ),
    )
    parser.add_argument(
        "--lane-drift",
        type=Path,
        default=DEFAULT_V55C_DRIFT_RECORD_PATH,
        help=(
            "Path to the V55-C constitutional_coherence_lane_drift_record@1 handoff. "
            "Defaults to the committed V55-C fixture."
        ),
    )
    parser.add_argument(
        "--v55a-report",
        type=Path,
        default=DEFAULT_V55C_V55A_REPORT_PATH,
        help="Path to the shipped V55-A constitutional_coherence_report@1 fixture.",
    )
    parser.add_argument(
        "--v55a-unresolved",
        type=Path,
        default=DEFAULT_V55C_V55A_UNRESOLVED_PATH,
        help="Path to the shipped V55-A constitutional_unresolved_seam_register@1 fixture.",
    )
    parser.add_argument(
        "--v55b-report",
        type=Path,
        default=DEFAULT_V55C_V55B_REPORT_PATH,
        help="Path to the shipped V55-B constitutional_coherence_report@1 fixture.",
    )
    parser.add_argument(
        "--v55b-unresolved",
        type=Path,
        default=DEFAULT_V55C_V55B_UNRESOLVED_PATH,
        help="Path to the shipped V55-B constitutional_unresolved_seam_register@1 fixture.",
    )
    parser.add_argument(
        "--v55b-drift",
        type=Path,
        default=DEFAULT_V55C_V55B_DRIFT_PATH,
        help="Path to the shipped V55-B constitutional_coherence_lane_drift_record@1 fixture.",
    )
    parser.add_argument(
        "--v55b-evidence",
        type=Path,
        default=DEFAULT_V55C_V55B_EVIDENCE_PATH,
        help="Path to the shipped V55-B descendant-trial hardening evidence JSON.",
    )
    parser.add_argument(
        "--governance-output",
        type=Path,
        default=None,
        help="Optional path to write constitutional_governance_calibration_register@1 JSON.",
    )
    parser.add_argument(
        "--migration-output",
        type=Path,
        default=None,
        help="Optional path to write constitutional_migration_decision_register@1 JSON.",
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
        governance, migration = run_constitutional_coherence_v55c(
            repo_root_path=args.repo_root,
            admissions_path=args.admissions,
            lane_drift_path=args.lane_drift,
            v55a_report_path=args.v55a_report,
            v55a_unresolved_path=args.v55a_unresolved,
            v55b_report_path=args.v55b_report,
            v55b_unresolved_path=args.v55b_unresolved,
            v55b_drift_path=args.v55b_drift,
            v55b_evidence_path=args.v55b_evidence,
        )
    except (ValueError, FileNotFoundError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 1

    governance_payload = render_governance_calibration_register_payload(governance)
    migration_payload = render_migration_decision_register_payload(migration)
    if args.governance_output:
        _write_text(args.governance_output, governance_payload)
    else:
        sys.stdout.write(governance_payload)
    if args.migration_output:
        _write_text(args.migration_output, migration_payload)
    elif migration.entry_count > 0:
        sys.stderr.write(migration_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
