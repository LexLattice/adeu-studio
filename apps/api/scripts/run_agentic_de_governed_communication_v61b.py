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
    DEFAULT_V60A_TASK_CHARTER_PATH,
    DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    DEFAULT_V61A_EVIDENCE_PATH,
    DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    DEFAULT_V61B_LANE_DRIFT_PATH,
    render_bridge_office_binding_payload,
    render_message_rewitness_gate_payload,
    run_agentic_de_governed_communication_v61b,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V61-B bridge-office binding and rewitness follow-on over the "
            "exact resident /urm/copilot/send seam and shipped V60/V61-A lineage."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument("--v60a-task-charter", type=Path, default=DEFAULT_V60A_TASK_CHARTER_PATH)
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
    parser.add_argument("--v61b-lane-drift", type=Path, default=DEFAULT_V61B_LANE_DRIFT_PATH)
    parser.add_argument("--v61a-evidence", type=Path, default=DEFAULT_V61A_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument(
        "--bridge-office-binding-output",
        type=Path,
        default=None,
    )
    parser.add_argument("--message-rewitness-gate-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        bridge_binding, rewitness_gate = run_agentic_de_governed_communication_v61b(
            repo_root_path=args.repo_root,
            v60a_task_charter_path=args.v60a_task_charter,
            v60a_loop_state_ledger_path=args.v60a_loop_state_ledger,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_ingress_path=args.v61a_communication_ingress,
            v61a_surface_authority_descriptor_path=args.v61a_surface_authority_descriptor,
            v61a_ingress_interpretation_path=args.v61a_ingress_interpretation,
            v61a_communication_egress_path=args.v61a_communication_egress,
            lane_drift_path=args.v61b_lane_drift,
            v61a_evidence_path=args.v61a_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    bridge_payload = render_bridge_office_binding_payload(bridge_binding)
    rewitness_payload = render_message_rewitness_gate_payload(rewitness_gate)

    if args.bridge_office_binding_output is not None:
        _write_text(args.bridge_office_binding_output, bridge_payload)
    if args.message_rewitness_gate_output is not None:
        _write_text(args.message_rewitness_gate_output, rewitness_payload)

    if args.message_rewitness_gate_output is None:
        sys.stdout.write(rewitness_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
