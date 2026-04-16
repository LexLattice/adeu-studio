from __future__ import annotations

import argparse
import sys
import warnings
from datetime import datetime
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
    DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    DEFAULT_V61A_EVIDENCE_PATH,
    DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    DEFAULT_V61B_EVIDENCE_PATH,
    DEFAULT_V61C_EVIDENCE_PATH,
    DEFAULT_V62A_CONNECTOR_SNAPSHOT_PATH,
    DEFAULT_V62A_LANE_DRIFT_PATH,
    render_connector_admission_payload,
    render_external_assistant_ingress_bridge_payload,
    run_agentic_de_connector_admission_v62a,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_datetime(value: str) -> datetime:
    try:
        return datetime.fromisoformat(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"invalid ISO datetime: {value}") from exc


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V62-A connector-admission starter over the exact "
            "connector snapshot create/get seam and the shipped V61-A communication lineage."
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
        "--connector-snapshot",
        type=Path,
        default=DEFAULT_V62A_CONNECTOR_SNAPSHOT_PATH,
    )
    parser.add_argument("--v62a-lane-drift", type=Path, default=DEFAULT_V62A_LANE_DRIFT_PATH)
    parser.add_argument("--v61a-evidence", type=Path, default=DEFAULT_V61A_EVIDENCE_PATH)
    parser.add_argument("--v61b-evidence", type=Path, default=DEFAULT_V61B_EVIDENCE_PATH)
    parser.add_argument("--v61c-evidence", type=Path, default=DEFAULT_V61C_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--min-acceptable-ts", type=_parse_datetime, default=None)
    parser.add_argument("--connector-admission-output", type=Path, default=None)
    parser.add_argument("--external-assistant-ingress-bridge-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        connector_admission, ingress_bridge = run_agentic_de_connector_admission_v62a(
            repo_root_path=args.repo_root,
            v60a_task_charter_path=args.v60a_task_charter,
            v60a_loop_state_ledger_path=args.v60a_loop_state_ledger,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_ingress_path=args.v61a_communication_ingress,
            v61a_surface_authority_descriptor_path=args.v61a_surface_authority_descriptor,
            v61a_ingress_interpretation_path=args.v61a_ingress_interpretation,
            connector_snapshot_path=args.connector_snapshot,
            lane_drift_path=args.v62a_lane_drift,
            v61a_evidence_path=args.v61a_evidence,
            v61b_evidence_path=args.v61b_evidence,
            v61c_evidence_path=args.v61c_evidence,
            target_relative_path=args.target_relative_path,
            min_acceptable_ts=args.min_acceptable_ts,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    connector_admission_payload = render_connector_admission_payload(connector_admission)
    ingress_bridge_payload = render_external_assistant_ingress_bridge_payload(ingress_bridge)

    if args.connector_admission_output is not None:
        _write_text(args.connector_admission_output, connector_admission_payload)
    if args.external_assistant_ingress_bridge_output is not None:
        _write_text(args.external_assistant_ingress_bridge_output, ingress_bridge_payload)

    if args.external_assistant_ingress_bridge_output is None:
        sys.stdout.write(ingress_bridge_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
