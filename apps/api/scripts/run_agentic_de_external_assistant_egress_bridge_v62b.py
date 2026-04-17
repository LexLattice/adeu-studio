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
    DEFAULT_V62A_CONNECTOR_ADMISSION_PATH,
    DEFAULT_V62A_EVIDENCE_PATH,
    DEFAULT_V62A_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PATH,
    DEFAULT_V62B_LANE_DRIFT_PATH,
    render_external_assistant_egress_bridge_payload,
    run_agentic_de_external_assistant_egress_bridge_v62b,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V62-B external-assistant egress bridge follow-on over "
            "the shipped V62-A admitted connector path and shipped V61-A/V61-B lineage."
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
        "--v62a-connector-admission",
        type=Path,
        default=DEFAULT_V62A_CONNECTOR_ADMISSION_PATH,
    )
    parser.add_argument(
        "--v62a-external-assistant-ingress-bridge",
        type=Path,
        default=DEFAULT_V62A_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PATH,
    )
    parser.add_argument("--v62b-lane-drift", type=Path, default=DEFAULT_V62B_LANE_DRIFT_PATH)
    parser.add_argument("--v62a-evidence", type=Path, default=DEFAULT_V62A_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--external-assistant-egress-bridge-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        egress_bridge = run_agentic_de_external_assistant_egress_bridge_v62b(
            repo_root_path=args.repo_root,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_egress_path=args.v61a_communication_egress,
            v61b_bridge_office_binding_path=args.v61b_bridge_office_binding,
            v61b_message_rewitness_gate_path=args.v61b_message_rewitness_gate,
            v62a_connector_admission_path=args.v62a_connector_admission,
            v62a_external_assistant_ingress_bridge_path=(
                args.v62a_external_assistant_ingress_bridge
            ),
            lane_drift_path=args.v62b_lane_drift,
            v62a_evidence_path=args.v62a_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    payload = render_external_assistant_egress_bridge_payload(egress_bridge)
    if args.external_assistant_egress_bridge_output is not None:
        _write_text(args.external_assistant_egress_bridge_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
