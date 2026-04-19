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
    DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    DEFAULT_V59A_OBSERVATION_PATH,
    DEFAULT_V64A_EVIDENCE_PATH,
    DEFAULT_V64A_REPO_WRITABLE_SURFACE_DESCRIPTOR_PATH,
    DEFAULT_V64A_REPO_WRITE_LEASE_PATH,
    DEFAULT_V64A_REPO_WRITE_SURFACE_ADMISSION_PATH,
    DEFAULT_V64B_LANE_DRIFT_PATH,
    render_repo_write_reintegration_payload,
    render_repo_write_restoration_payload,
    run_agentic_de_repo_write_restoration_v64b,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V64-B repo-write restoration seam over the shipped V64-A "
            "writable-surface descriptor, lease, and exact target admission plus the "
            "shipped V59-A concrete write-effect lineage."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument("--v59a-observation", type=Path, default=DEFAULT_V59A_OBSERVATION_PATH)
    parser.add_argument(
        "--v59a-local-effect-conformance",
        type=Path,
        default=DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
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
    parser.add_argument("--v64b-lane-drift", type=Path, default=DEFAULT_V64B_LANE_DRIFT_PATH)
    parser.add_argument("--v64a-evidence", type=Path, default=DEFAULT_V64A_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--repo-write-restoration-output", type=Path, default=None)
    parser.add_argument("--repo-write-reintegration-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        restoration, reintegration = run_agentic_de_repo_write_restoration_v64b(
            repo_root_path=args.repo_root,
            v59a_observation_path=args.v59a_observation,
            v59a_local_effect_conformance_path=args.v59a_local_effect_conformance,
            v64a_repo_writable_surface_descriptor_path=args.v64a_repo_writable_surface_descriptor,
            v64a_repo_write_lease_path=args.v64a_repo_write_lease,
            v64a_repo_write_surface_admission_path=args.v64a_repo_write_surface_admission,
            lane_drift_path=args.v64b_lane_drift,
            v64a_evidence_path=args.v64a_evidence,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    restoration_payload = render_repo_write_restoration_payload(restoration)
    reintegration_payload = render_repo_write_reintegration_payload(reintegration)

    if args.repo_write_restoration_output is not None:
        _write_text(args.repo_write_restoration_output, restoration_payload)
    if args.repo_write_reintegration_output is not None:
        _write_text(args.repo_write_reintegration_output, reintegration_payload)
    else:
        sys.stdout.write(reintegration_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
