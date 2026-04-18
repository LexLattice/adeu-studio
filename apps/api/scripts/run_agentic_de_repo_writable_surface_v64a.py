from __future__ import annotations

import argparse
import sys
import warnings
from pathlib import Path

warnings.filterwarnings(
    "ignore",
    message=(
        r'Field name "schema" in "AgenticDe.*" shadows an attribute in parent '
        r'"BaseModel"'
    ),
    category=UserWarning,
)

from adeu_agentic_de import (  # noqa: E402
    DEFAULT_V59A_CONTINUITY_ADMISSION_PATH,
    DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH,
    DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    DEFAULT_V59C_EVIDENCE_PATH,
    DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    DEFAULT_V60C_EVIDENCE_PATH,
    DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    DEFAULT_V61C_EVIDENCE_PATH,
    DEFAULT_V64A_LANE_DRIFT_PATH,
    render_repo_writable_surface_descriptor_payload,
    render_repo_write_lease_payload,
    render_repo_write_surface_admission_payload,
    run_agentic_de_repo_writable_surface_v64a,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V64-A repo writable-surface starter over the shipped "
            "V59/V60/V61 lineage with one selected writable surface descriptor, one "
            "bounded lease, and one exact target admission."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument(
        "--v59a-continuity-region-declaration",
        type=Path,
        default=DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH,
    )
    parser.add_argument(
        "--v59a-continuity-admission",
        type=Path,
        default=DEFAULT_V59A_CONTINUITY_ADMISSION_PATH,
    )
    parser.add_argument(
        "--v59a-occupancy-report",
        type=Path,
        default=DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    )
    parser.add_argument(
        "--v59a-continuity-reintegration",
        type=Path,
        default=DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    )
    parser.add_argument(
        "--v60a-loop-state-ledger",
        type=Path,
        default=DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    )
    parser.add_argument(
        "--v60b-continuation-refresh-decision",
        type=Path,
        default=DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    )
    parser.add_argument(
        "--v61a-communication-ingress",
        type=Path,
        default=DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    )
    parser.add_argument(
        "--v61a-surface-authority-descriptor",
        type=Path,
        default=DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    )
    parser.add_argument(
        "--v61a-ingress-interpretation",
        type=Path,
        default=DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    )
    parser.add_argument(
        "--v61a-communication-egress",
        type=Path,
        default=DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    )
    parser.add_argument("--v64a-lane-drift", type=Path, default=DEFAULT_V64A_LANE_DRIFT_PATH)
    parser.add_argument("--v59c-evidence", type=Path, default=DEFAULT_V59C_EVIDENCE_PATH)
    parser.add_argument("--v60c-evidence", type=Path, default=DEFAULT_V60C_EVIDENCE_PATH)
    parser.add_argument("--v61c-evidence", type=Path, default=DEFAULT_V61C_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--repo-writable-surface-descriptor-output", type=Path, default=None)
    parser.add_argument("--repo-write-lease-output", type=Path, default=None)
    parser.add_argument("--repo-write-surface-admission-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        descriptor, lease, admission = run_agentic_de_repo_writable_surface_v64a(
            repo_root_path=args.repo_root,
            v59a_continuity_region_declaration_path=args.v59a_continuity_region_declaration,
            v59a_continuity_admission_path=args.v59a_continuity_admission,
            v59a_occupancy_report_path=args.v59a_occupancy_report,
            v59a_continuity_reintegration_path=args.v59a_continuity_reintegration,
            v60a_loop_state_ledger_path=args.v60a_loop_state_ledger,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_ingress_path=args.v61a_communication_ingress,
            v61a_surface_authority_descriptor_path=args.v61a_surface_authority_descriptor,
            v61a_ingress_interpretation_path=args.v61a_ingress_interpretation,
            v61a_communication_egress_path=args.v61a_communication_egress,
            lane_drift_path=args.v64a_lane_drift,
            v59c_evidence_path=args.v59c_evidence,
            v60c_evidence_path=args.v60c_evidence,
            v61c_evidence_path=args.v61c_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    descriptor_payload = render_repo_writable_surface_descriptor_payload(descriptor)
    lease_payload = render_repo_write_lease_payload(lease)
    admission_payload = render_repo_write_surface_admission_payload(admission)

    if args.repo_writable_surface_descriptor_output is not None:
        _write_text(args.repo_writable_surface_descriptor_output, descriptor_payload)
    if args.repo_write_lease_output is not None:
        _write_text(args.repo_write_lease_output, lease_payload)
    if args.repo_write_surface_admission_output is not None:
        _write_text(args.repo_write_surface_admission_output, admission_payload)

    if args.repo_write_surface_admission_output is None:
        sys.stdout.write(admission_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
