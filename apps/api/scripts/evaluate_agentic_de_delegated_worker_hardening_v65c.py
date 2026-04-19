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
    DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    DEFAULT_V65A_DELEGATED_WORKER_EXPORT_PATH,
    DEFAULT_V65A_EVIDENCE_PATH,
    DEFAULT_V65B_DELEGATED_WORKER_RECONCILIATION_PATH,
    DEFAULT_V65C_LANE_DRIFT_PATH,
    render_delegated_worker_hardening_payload,
    run_agentic_de_delegated_worker_hardening_v65c,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _default_v65b_evidence_path() -> Path:
    return (
        Path(__file__).resolve().parents[3]
        / "artifacts"
        / "agent_harness"
        / "v180"
        / "evidence_inputs"
        / "v65b_delegated_worker_reconciliation_evidence_v180.json"
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Evaluate the bounded V65-C advisory delegated-worker hardening seam over the "
            "shipped V65-A export lineage and optional shipped V65-B reconciliation lineage."
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
        "--v65b-delegated-worker-reconciliation",
        type=Path,
        default=DEFAULT_V65B_DELEGATED_WORKER_RECONCILIATION_PATH,
    )
    parser.add_argument("--v65c-lane-drift", type=Path, default=DEFAULT_V65C_LANE_DRIFT_PATH)
    parser.add_argument("--v65a-evidence", type=Path, default=DEFAULT_V65A_EVIDENCE_PATH)
    parser.add_argument("--v65b-evidence", type=Path, default=_default_v65b_evidence_path())
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
        register = run_agentic_de_delegated_worker_hardening_v65c(
            repo_root_path=args.repo_root,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_egress_path=args.v61a_communication_egress,
            v65a_delegated_worker_export_path=args.v65a_delegated_worker_export,
            v65b_delegated_worker_reconciliation_path=args.v65b_delegated_worker_reconciliation,
            lane_drift_path=args.v65c_lane_drift,
            v65a_evidence_path=args.v65a_evidence,
            v65b_evidence_path=args.v65b_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    payload = render_delegated_worker_hardening_payload(register)
    if args.hardening_output is not None:
        _write_text(args.hardening_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
