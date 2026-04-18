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
    DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    DEFAULT_V61C_EVIDENCE_PATH,
    DEFAULT_V62C_EVIDENCE_PATH,
    DEFAULT_V63A_LANE_DRIFT_PATH,
    render_remote_operator_response_payload,
    render_remote_operator_session_payload,
    render_remote_operator_view_payload,
    run_agentic_de_remote_operator_starter_v63a,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V63-A remote-operator starter over the shipped V60/V61 "
            "lineage with one explicit remote_operator session, one read-mostly view, "
            "and one bounded response record."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
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
    parser.add_argument("--v63a-lane-drift", type=Path, default=DEFAULT_V63A_LANE_DRIFT_PATH)
    parser.add_argument("--v61c-evidence", type=Path, default=DEFAULT_V61C_EVIDENCE_PATH)
    parser.add_argument("--v62c-evidence", type=Path, default=DEFAULT_V62C_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument(
        "--selected-response-kind",
        choices=("acknowledge", "approve", "continue", "pause", "escalate"),
        default="acknowledge",
    )
    parser.add_argument("--remote-operator-session-output", type=Path, default=None)
    parser.add_argument("--remote-operator-view-output", type=Path, default=None)
    parser.add_argument("--remote-operator-response-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        session_record, view_packet, response_record = run_agentic_de_remote_operator_starter_v63a(
            repo_root_path=args.repo_root,
            v60a_loop_state_ledger_path=args.v60a_loop_state_ledger,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_ingress_path=args.v61a_communication_ingress,
            v61a_surface_authority_descriptor_path=args.v61a_surface_authority_descriptor,
            v61a_ingress_interpretation_path=args.v61a_ingress_interpretation,
            v61a_communication_egress_path=args.v61a_communication_egress,
            lane_drift_path=args.v63a_lane_drift,
            v61c_evidence_path=args.v61c_evidence,
            v62c_evidence_path=args.v62c_evidence,
            target_relative_path=args.target_relative_path,
            selected_response_kind=args.selected_response_kind,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    session_payload = render_remote_operator_session_payload(session_record)
    view_payload = render_remote_operator_view_payload(view_packet)
    response_payload = render_remote_operator_response_payload(response_record)

    if args.remote_operator_session_output is not None:
        _write_text(args.remote_operator_session_output, session_payload)
    if args.remote_operator_view_output is not None:
        _write_text(args.remote_operator_view_output, view_payload)
    if args.remote_operator_response_output is not None:
        _write_text(args.remote_operator_response_output, response_payload)

    if args.remote_operator_response_output is None:
        sys.stdout.write(response_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
