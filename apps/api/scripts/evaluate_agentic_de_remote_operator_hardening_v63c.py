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
    DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    DEFAULT_V63A_EVIDENCE_PATH,
    DEFAULT_V63A_REMOTE_OPERATOR_RESPONSE_PATH,
    DEFAULT_V63A_REMOTE_OPERATOR_SESSION_PATH,
    DEFAULT_V63A_REMOTE_OPERATOR_VIEW_PATH,
    DEFAULT_V63B_EVIDENCE_PATH,
    DEFAULT_V63B_REMOTE_OPERATOR_CONTROL_BRIDGE_PATH,
    DEFAULT_V63C_LANE_DRIFT_PATH,
    render_remote_operator_hardening_payload,
    run_agentic_de_remote_operator_hardening_v63c,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Evaluate the bounded V63-C advisory remote-operator hardening seam over "
            "the shipped V63-A/V63-B remote lineage and shipped V60/V61 posture."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
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
    parser.add_argument(
        "--v63a-remote-operator-session",
        type=Path,
        default=DEFAULT_V63A_REMOTE_OPERATOR_SESSION_PATH,
    )
    parser.add_argument(
        "--v63a-remote-operator-view",
        type=Path,
        default=DEFAULT_V63A_REMOTE_OPERATOR_VIEW_PATH,
    )
    parser.add_argument(
        "--v63a-remote-operator-response",
        type=Path,
        default=DEFAULT_V63A_REMOTE_OPERATOR_RESPONSE_PATH,
    )
    parser.add_argument(
        "--v63b-remote-operator-control-bridge",
        type=Path,
        default=DEFAULT_V63B_REMOTE_OPERATOR_CONTROL_BRIDGE_PATH,
    )
    parser.add_argument("--v63c-lane-drift", type=Path, default=DEFAULT_V63C_LANE_DRIFT_PATH)
    parser.add_argument("--v63a-evidence", type=Path, default=DEFAULT_V63A_EVIDENCE_PATH)
    parser.add_argument("--v63b-evidence", type=Path, default=DEFAULT_V63B_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--hardening-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        register = run_agentic_de_remote_operator_hardening_v63c(
            repo_root_path=args.repo_root,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_ingress_path=args.v61a_communication_ingress,
            v61a_surface_authority_descriptor_path=args.v61a_surface_authority_descriptor,
            v61a_ingress_interpretation_path=args.v61a_ingress_interpretation,
            v61a_communication_egress_path=args.v61a_communication_egress,
            v63a_remote_operator_session_path=args.v63a_remote_operator_session,
            v63a_remote_operator_view_path=args.v63a_remote_operator_view,
            v63a_remote_operator_response_path=args.v63a_remote_operator_response,
            v63b_remote_operator_control_bridge_path=args.v63b_remote_operator_control_bridge,
            lane_drift_path=args.v63c_lane_drift,
            v63a_evidence_path=args.v63a_evidence,
            v63b_evidence_path=args.v63b_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    payload = render_remote_operator_hardening_payload(register)
    if args.hardening_output is not None:
        _write_text(args.hardening_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
