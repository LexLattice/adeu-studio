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
    DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH,
    DEFAULT_V60A_CONTINUATION_DECISION_PATH,
    DEFAULT_V60A_EVIDENCE_PATH,
    DEFAULT_V60A_LANE_DRIFT_PATH,
    DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    DEFAULT_V60A_SEED_INTENT_PATH,
    DEFAULT_V60A_TASK_CHARTER_PATH,
    DEFAULT_V60A_TASK_RESIDUAL_PATH,
    DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    DEFAULT_V60B_EVIDENCE_PATH,
    DEFAULT_V60B_LANE_DRIFT_PATH,
    DEFAULT_V60B_TASK_RESIDUAL_REFRESH_PATH,
    DEFAULT_V60C_HARDENING_PATH,
    DEFAULT_V60C_LANE_DRIFT_PATH,
    DEFAULT_V61A_LANE_DRIFT_PATH,
    DEFAULT_V61A_SEND_REQUEST_PATH,
    render_communication_egress_payload,
    render_communication_ingress_payload,
    render_ingress_interpretation_payload,
    render_surface_authority_descriptor_payload,
    run_agentic_de_governed_communication_v61a,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V61-A governed communication starter over the exact "
            "resident /urm/copilot/send seam and the shipped V60 continuation lineage."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument(
        "--v59a-live-turn-reintegration",
        type=Path,
        default=DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    )
    parser.add_argument(
        "--v59a-continuity-reintegration",
        type=Path,
        default=DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    )
    parser.add_argument(
        "--v59b-continuity-restoration-reintegration",
        type=Path,
        default=DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH,
    )
    parser.add_argument("--v60a-lane-drift", type=Path, default=DEFAULT_V60A_LANE_DRIFT_PATH)
    parser.add_argument("--v60a-seed-intent", type=Path, default=DEFAULT_V60A_SEED_INTENT_PATH)
    parser.add_argument("--v60a-task-charter", type=Path, default=DEFAULT_V60A_TASK_CHARTER_PATH)
    parser.add_argument("--v60a-task-residual", type=Path, default=DEFAULT_V60A_TASK_RESIDUAL_PATH)
    parser.add_argument(
        "--v60a-loop-state-ledger",
        type=Path,
        default=DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    )
    parser.add_argument(
        "--v60a-continuation-decision",
        type=Path,
        default=DEFAULT_V60A_CONTINUATION_DECISION_PATH,
    )
    parser.add_argument("--v60b-lane-drift", type=Path, default=DEFAULT_V60B_LANE_DRIFT_PATH)
    parser.add_argument(
        "--v60b-task-residual-refresh",
        type=Path,
        default=DEFAULT_V60B_TASK_RESIDUAL_REFRESH_PATH,
    )
    parser.add_argument(
        "--v60b-continuation-refresh-decision",
        type=Path,
        default=DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    )
    parser.add_argument("--v60c-lane-drift", type=Path, default=DEFAULT_V60C_LANE_DRIFT_PATH)
    parser.add_argument("--v60c-hardening", type=Path, default=DEFAULT_V60C_HARDENING_PATH)
    parser.add_argument("--v61a-lane-drift", type=Path, default=DEFAULT_V61A_LANE_DRIFT_PATH)
    parser.add_argument("--send-request", type=Path, default=DEFAULT_V61A_SEND_REQUEST_PATH)
    parser.add_argument("--v60a-evidence", type=Path, default=DEFAULT_V60A_EVIDENCE_PATH)
    parser.add_argument("--v60b-evidence", type=Path, default=DEFAULT_V60B_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--communication-ingress-output", type=Path, default=None)
    parser.add_argument("--surface-authority-descriptor-output", type=Path, default=None)
    parser.add_argument("--ingress-interpretation-output", type=Path, default=None)
    parser.add_argument("--communication-egress-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        ingress, descriptor, interpretation, egress = run_agentic_de_governed_communication_v61a(
            repo_root_path=args.repo_root,
            v59a_live_turn_reintegration_path=args.v59a_live_turn_reintegration,
            v59a_continuity_reintegration_path=args.v59a_continuity_reintegration,
            v59b_continuity_restoration_reintegration_path=(
                args.v59b_continuity_restoration_reintegration
            ),
            v60a_lane_drift_path=args.v60a_lane_drift,
            v60a_seed_intent_path=args.v60a_seed_intent,
            v60a_task_charter_path=args.v60a_task_charter,
            v60a_task_residual_path=args.v60a_task_residual,
            v60a_loop_state_ledger_path=args.v60a_loop_state_ledger,
            v60a_continuation_decision_path=args.v60a_continuation_decision,
            v60b_lane_drift_path=args.v60b_lane_drift,
            v60b_task_residual_refresh_path=args.v60b_task_residual_refresh,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v60c_lane_drift_path=args.v60c_lane_drift,
            v60c_hardening_path=args.v60c_hardening,
            lane_drift_path=args.v61a_lane_drift,
            send_request_path=args.send_request,
            v60a_evidence_path=args.v60a_evidence,
            v60b_evidence_path=args.v60b_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    ingress_payload = render_communication_ingress_payload(ingress)
    descriptor_payload = render_surface_authority_descriptor_payload(descriptor)
    interpretation_payload = render_ingress_interpretation_payload(interpretation)
    egress_payload = render_communication_egress_payload(egress)

    if args.communication_ingress_output is not None:
        _write_text(args.communication_ingress_output, ingress_payload)
    if args.surface_authority_descriptor_output is not None:
        _write_text(args.surface_authority_descriptor_output, descriptor_payload)
    if args.ingress_interpretation_output is not None:
        _write_text(args.ingress_interpretation_output, interpretation_payload)
    if args.communication_egress_output is not None:
        _write_text(args.communication_egress_output, egress_payload)

    if args.communication_egress_output is None:
        sys.stdout.write(egress_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
