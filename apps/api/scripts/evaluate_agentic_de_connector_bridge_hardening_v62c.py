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
    DEFAULT_V61B_BRIDGE_OFFICE_BINDING_PATH,
    DEFAULT_V61B_MESSAGE_REWITNESS_GATE_PATH,
    DEFAULT_V61C_HARDENING_PATH,
    DEFAULT_V62A_CONNECTOR_ADMISSION_PATH,
    DEFAULT_V62A_EVIDENCE_PATH,
    DEFAULT_V62A_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PATH,
    DEFAULT_V62B_EVIDENCE_PATH,
    DEFAULT_V62B_EXTERNAL_ASSISTANT_EGRESS_BRIDGE_PATH,
    DEFAULT_V62C_LANE_DRIFT_PATH,
    render_connector_bridge_hardening_payload,
    run_agentic_de_connector_bridge_hardening_v62c,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Evaluate the bounded V62-C advisory connector hardening seam over the "
            "shipped V62-A/V62-B connector lineage and shipped V61 posture."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument(
        "--v60b-continuation-refresh-decision",
        type=Path,
        default=DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    )
    parser.add_argument(
        "--v61a-communication-egress",
        type=Path,
        default=DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    )
    parser.add_argument(
        "--v61b-bridge-office-binding",
        type=Path,
        default=DEFAULT_V61B_BRIDGE_OFFICE_BINDING_PATH,
    )
    parser.add_argument(
        "--v61b-message-rewitness-gate",
        type=Path,
        default=DEFAULT_V61B_MESSAGE_REWITNESS_GATE_PATH,
    )
    parser.add_argument(
        "--v61c-governed-communication-hardening",
        type=Path,
        default=DEFAULT_V61C_HARDENING_PATH,
    )
    parser.add_argument(
        "--v62a-connector-admission",
        type=Path,
        default=DEFAULT_V62A_CONNECTOR_ADMISSION_PATH,
    )
    parser.add_argument(
        "--v62a-external-assistant-ingress-bridge",
        type=Path,
        default=DEFAULT_V62A_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PATH,
    )
    parser.add_argument(
        "--v62b-external-assistant-egress-bridge",
        type=Path,
        default=DEFAULT_V62B_EXTERNAL_ASSISTANT_EGRESS_BRIDGE_PATH,
    )
    parser.add_argument("--v62c-lane-drift", type=Path, default=DEFAULT_V62C_LANE_DRIFT_PATH)
    parser.add_argument("--v62a-evidence", type=Path, default=DEFAULT_V62A_EVIDENCE_PATH)
    parser.add_argument("--v62b-evidence", type=Path, default=DEFAULT_V62B_EVIDENCE_PATH)
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
        register = run_agentic_de_connector_bridge_hardening_v62c(
            repo_root_path=args.repo_root,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_egress_path=args.v61a_communication_egress,
            v61b_bridge_office_binding_path=args.v61b_bridge_office_binding,
            v61b_message_rewitness_gate_path=args.v61b_message_rewitness_gate,
            v61c_governed_communication_hardening_path=(args.v61c_governed_communication_hardening),
            v62a_connector_admission_path=args.v62a_connector_admission,
            v62a_external_assistant_ingress_bridge_path=(
                args.v62a_external_assistant_ingress_bridge
            ),
            v62b_external_assistant_egress_bridge_path=(args.v62b_external_assistant_egress_bridge),
            lane_drift_path=args.v62c_lane_drift,
            v62a_evidence_path=args.v62a_evidence,
            v62b_evidence_path=args.v62b_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    payload = render_connector_bridge_hardening_payload(register)
    if args.hardening_output is not None:
        _write_text(args.hardening_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
