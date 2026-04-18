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
    DEFAULT_V63A_REMOTE_OPERATOR_SESSION_PATH,
    DEFAULT_V63A_REMOTE_OPERATOR_VIEW_PATH,
    DEFAULT_V63B_LANE_DRIFT_PATH,
    render_remote_operator_control_bridge_payload,
    run_agentic_de_remote_operator_control_bridge_v63b,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V63-B remote-operator control bridge over the shipped "
            "V63-A session/view basis and shipped V60/V61 lineage with one richer "
            "typed intervention packet."
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
    parser.add_argument("--v63b-lane-drift", type=Path, default=DEFAULT_V63B_LANE_DRIFT_PATH)
    parser.add_argument("--v63a-evidence", type=Path, default=DEFAULT_V63A_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument(
        "--selected-intervention-kind",
        choices=("structured_answer", "clarification", "inspect_rich"),
        default="structured_answer",
    )
    parser.add_argument("--remote-operator-control-bridge-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        bridge_packet = run_agentic_de_remote_operator_control_bridge_v63b(
            repo_root_path=args.repo_root,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_ingress_path=args.v61a_communication_ingress,
            v61a_surface_authority_descriptor_path=args.v61a_surface_authority_descriptor,
            v61a_ingress_interpretation_path=args.v61a_ingress_interpretation,
            v61a_communication_egress_path=args.v61a_communication_egress,
            v63a_remote_operator_session_path=args.v63a_remote_operator_session,
            v63a_remote_operator_view_path=args.v63a_remote_operator_view,
            lane_drift_path=args.v63b_lane_drift,
            v63a_evidence_path=args.v63a_evidence,
            target_relative_path=args.target_relative_path,
            selected_intervention_kind=args.selected_intervention_kind,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    payload = render_remote_operator_control_bridge_payload(bridge_packet)
    if args.remote_operator_control_bridge_output is not None:
        _write_text(args.remote_operator_control_bridge_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
