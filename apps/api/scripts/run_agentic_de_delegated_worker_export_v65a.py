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
    DEFAULT_V48E_EVIDENCE_PATH,
    DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH,
    DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    DEFAULT_V64A_REPO_WRITABLE_SURFACE_DESCRIPTOR_PATH,
    DEFAULT_V64A_REPO_WRITE_LEASE_PATH,
    DEFAULT_V64A_REPO_WRITE_SURFACE_ADMISSION_PATH,
    DEFAULT_V64C_EVIDENCE_PATH,
    DEFAULT_V64C_REPO_WRITABLE_SURFACE_HARDENING_PATH,
    DEFAULT_V65A_LANE_DRIFT_PATH,
    render_delegated_worker_export_payload,
    run_agentic_de_delegated_worker_export_v65a,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V65-A delegated worker export starter over the shipped V64 "
            "local writable lineage, shipped V64-C shaping context, and released V48-E "
            "worker topology."
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
        "--v64a-repo-writable-surface-descriptor",
        type=Path,
        default=DEFAULT_V64A_REPO_WRITABLE_SURFACE_DESCRIPTOR_PATH,
    )
    parser.add_argument(
        "--v64a-repo-write-lease",
        type=Path,
        default=DEFAULT_V64A_REPO_WRITE_LEASE_PATH,
    )
    parser.add_argument(
        "--v64a-repo-write-surface-admission",
        type=Path,
        default=DEFAULT_V64A_REPO_WRITE_SURFACE_ADMISSION_PATH,
    )
    parser.add_argument(
        "--v64c-repo-writable-surface-hardening",
        type=Path,
        default=DEFAULT_V64C_REPO_WRITABLE_SURFACE_HARDENING_PATH,
    )
    parser.add_argument(
        "--v48e-worker-delegation-topology",
        type=Path,
        default=DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH,
    )
    parser.add_argument("--v65a-lane-drift", type=Path, default=DEFAULT_V65A_LANE_DRIFT_PATH)
    parser.add_argument("--v64c-evidence", type=Path, default=DEFAULT_V64C_EVIDENCE_PATH)
    parser.add_argument("--v48e-evidence", type=Path, default=DEFAULT_V48E_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--delegated-worker-export-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        packet = run_agentic_de_delegated_worker_export_v65a(
            repo_root_path=args.repo_root,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_ingress_path=args.v61a_communication_ingress,
            v61a_surface_authority_descriptor_path=args.v61a_surface_authority_descriptor,
            v61a_ingress_interpretation_path=args.v61a_ingress_interpretation,
            v61a_communication_egress_path=args.v61a_communication_egress,
            v64a_repo_writable_surface_descriptor_path=args.v64a_repo_writable_surface_descriptor,
            v64a_repo_write_lease_path=args.v64a_repo_write_lease,
            v64a_repo_write_surface_admission_path=args.v64a_repo_write_surface_admission,
            v64c_repo_writable_surface_hardening_path=args.v64c_repo_writable_surface_hardening,
            v48e_worker_delegation_topology_path=args.v48e_worker_delegation_topology,
            lane_drift_path=args.v65a_lane_drift,
            v64c_evidence_path=args.v64c_evidence,
            v48e_evidence_path=args.v48e_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    payload = render_delegated_worker_export_payload(packet)
    if args.delegated_worker_export_output is not None:
        _write_text(args.delegated_worker_export_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
