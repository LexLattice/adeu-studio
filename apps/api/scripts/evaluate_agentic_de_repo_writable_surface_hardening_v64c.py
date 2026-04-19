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
    DEFAULT_V64A_EVIDENCE_PATH,
    DEFAULT_V64A_REPO_WRITABLE_SURFACE_DESCRIPTOR_PATH,
    DEFAULT_V64A_REPO_WRITE_LEASE_PATH,
    DEFAULT_V64A_REPO_WRITE_SURFACE_ADMISSION_PATH,
    DEFAULT_V64B_EVIDENCE_PATH,
    DEFAULT_V64B_REPO_WRITE_REINTEGRATION_PATH,
    DEFAULT_V64B_REPO_WRITE_RESTORATION_PATH,
    DEFAULT_V64C_LANE_DRIFT_PATH,
    render_repo_writable_surface_hardening_payload,
    run_agentic_de_repo_writable_surface_hardening_v64c,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Evaluate the bounded V64-C advisory writable-surface hardening seam over the "
            "shipped V64-A writable-surface lineage and optional shipped V64-B restoration/"
            "reintegration lineage."
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
        "--v64b-repo-write-restoration",
        type=Path,
        default=DEFAULT_V64B_REPO_WRITE_RESTORATION_PATH,
    )
    parser.add_argument(
        "--v64b-repo-write-reintegration",
        type=Path,
        default=DEFAULT_V64B_REPO_WRITE_REINTEGRATION_PATH,
    )
    parser.add_argument("--v64c-lane-drift", type=Path, default=DEFAULT_V64C_LANE_DRIFT_PATH)
    parser.add_argument("--v64a-evidence", type=Path, default=DEFAULT_V64A_EVIDENCE_PATH)
    parser.add_argument("--v64b-evidence", type=Path, default=DEFAULT_V64B_EVIDENCE_PATH)
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
        register = run_agentic_de_repo_writable_surface_hardening_v64c(
            repo_root_path=args.repo_root,
            v60b_continuation_refresh_decision_path=args.v60b_continuation_refresh_decision,
            v61a_communication_ingress_path=args.v61a_communication_ingress,
            v61a_surface_authority_descriptor_path=args.v61a_surface_authority_descriptor,
            v61a_ingress_interpretation_path=args.v61a_ingress_interpretation,
            v61a_communication_egress_path=args.v61a_communication_egress,
            v64a_repo_writable_surface_descriptor_path=args.v64a_repo_writable_surface_descriptor,
            v64a_repo_write_lease_path=args.v64a_repo_write_lease,
            v64a_repo_write_surface_admission_path=args.v64a_repo_write_surface_admission,
            v64b_repo_write_restoration_path=args.v64b_repo_write_restoration,
            v64b_repo_write_reintegration_path=args.v64b_repo_write_reintegration,
            lane_drift_path=args.v64c_lane_drift,
            v64a_evidence_path=args.v64a_evidence,
            v64b_evidence_path=args.v64b_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    payload = render_repo_writable_surface_hardening_payload(register)
    if args.hardening_output is not None:
        _write_text(args.hardening_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
