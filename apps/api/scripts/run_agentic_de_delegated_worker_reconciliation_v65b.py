from __future__ import annotations

import argparse
import sys
import warnings
from pathlib import Path

warnings.filterwarnings(
    "ignore",
    message=r'Field name "schema" in ".*" shadows an attribute in parent "BaseModel"',
    category=UserWarning,
)

from adeu_agentic_de import (  # noqa: E402
    DEFAULT_V48D_EVIDENCE_PATH,
    DEFAULT_V48E_EVIDENCE_PATH,
    DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH,
    DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    DEFAULT_V65A_DELEGATED_WORKER_EXPORT_PATH,
    DEFAULT_V65A_EVIDENCE_PATH,
    DEFAULT_V65B_LANE_DRIFT_PATH,
    DEFAULT_V65B_WORKER_BOUNDARY_CONFORMANCE_PATH,
    render_delegated_worker_reconciliation_payload,
    run_agentic_de_delegated_worker_reconciliation_v65b,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V65-B delegated worker reconciliation seam over the shipped "
            "V65-A export lineage and one released worker boundary-conformance lineage."
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
        "--v65a-delegated-worker-export",
        type=Path,
        default=DEFAULT_V65A_DELEGATED_WORKER_EXPORT_PATH,
    )
    parser.add_argument(
        "--worker-boundary-conformance",
        type=Path,
        default=DEFAULT_V65B_WORKER_BOUNDARY_CONFORMANCE_PATH,
    )
    parser.add_argument(
        "--v48e-worker-delegation-topology",
        type=Path,
        default=DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH,
    )
    parser.add_argument("--v65b-lane-drift", type=Path, default=DEFAULT_V65B_LANE_DRIFT_PATH)
    parser.add_argument("--v65a-evidence", type=Path, default=DEFAULT_V65A_EVIDENCE_PATH)
    parser.add_argument("--v48d-evidence", type=Path, default=DEFAULT_V48D_EVIDENCE_PATH)
    parser.add_argument("--v48e-evidence", type=Path, default=DEFAULT_V48E_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--delegated-worker-reconciliation-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report = run_agentic_de_delegated_worker_reconciliation_v65b(
            repo_root_path=args.repo_root,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_egress_path=args.v61a_communication_egress,
            v65a_delegated_worker_export_path=args.v65a_delegated_worker_export,
            worker_boundary_conformance_path=args.worker_boundary_conformance,
            v48e_worker_delegation_topology_path=args.v48e_worker_delegation_topology,
            lane_drift_path=args.v65b_lane_drift,
            v65a_evidence_path=args.v65a_evidence,
            v48d_evidence_path=args.v48d_evidence,
            v48e_evidence_path=args.v48e_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    payload = render_delegated_worker_reconciliation_payload(report)
    if args.delegated_worker_reconciliation_output is not None:
        _write_text(args.delegated_worker_reconciliation_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
