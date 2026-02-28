from __future__ import annotations

import argparse
import sys
from pathlib import Path

from urm_runtime.deterministic_env import (
    DeterministicToolingEnvError,
    ensure_deterministic_tooling_env,
)
from urm_runtime.hashing import canonical_json
from urm_runtime.stop_gate_registry import (
    ACTIVE_STOP_GATE_MANIFEST_VERSIONS,
    default_stop_gate_manifest_path,
    find_inactive_stop_gate_manifest_flags,
)
from urm_runtime.stop_gate_tools import (
    StopGateMetricsInput,
    build_stop_gate_metrics_from_input,
    stop_gate_markdown,
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build stop-gate metrics from persisted evidence artifacts.",
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path("artifacts/stop_gate/metrics.json"),
        help="Output JSON path",
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=Path("artifacts/stop_gate/report.md"),
        help="Output markdown path",
    )
    parser.add_argument(
        "--quality-current",
        type=Path,
        default=Path("artifacts/quality_dashboard.json"),
        help="Current quality dashboard JSON path",
    )
    parser.add_argument(
        "--quality-baseline",
        type=Path,
        default=None,
        help="Optional baseline quality dashboard JSON path",
    )
    parser.add_argument(
        "--incident-packet",
        dest="incident_packet_paths",
        action="append",
        type=Path,
        default=[
            Path("examples/eval/stop_gate/incident_packet_case_a_1.json"),
            Path("examples/eval/stop_gate/incident_packet_case_a_2.json"),
        ],
        help="Incident packet artifact path (repeatable)",
    )
    parser.add_argument(
        "--event-stream",
        dest="event_stream_paths",
        action="append",
        type=Path,
        default=[
            Path("apps/api/tests/fixtures/urm_events/sample_valid.ndjson"),
        ],
        help="URM event stream NDJSON path (repeatable)",
    )
    parser.add_argument(
        "--connector-snapshot",
        dest="connector_snapshot_paths",
        action="append",
        type=Path,
        default=[
            Path("examples/eval/stop_gate/connector_snapshot_case_a_1.json"),
            Path("examples/eval/stop_gate/connector_snapshot_case_a_2.json"),
        ],
        help="Connector snapshot artifact path (repeatable)",
    )
    parser.add_argument(
        "--validator-evidence-packet",
        dest="validator_evidence_packet_paths",
        action="append",
        type=Path,
        default=[
            Path("examples/eval/stop_gate/validator_evidence_packet_case_a_1.json"),
            Path("examples/eval/stop_gate/validator_evidence_packet_case_a_2.json"),
            Path("examples/eval/stop_gate/validator_evidence_packet_case_a_3.json"),
        ],
        help="Validator evidence packet artifact path (repeatable)",
    )
    parser.add_argument(
        "--semantics-diagnostics",
        dest="semantics_diagnostics_paths",
        action="append",
        type=Path,
        default=[
            Path("examples/eval/stop_gate/semantics_diagnostics_case_a_1.json"),
            Path("examples/eval/stop_gate/semantics_diagnostics_case_a_2.json"),
            Path("examples/eval/stop_gate/semantics_diagnostics_case_a_3.json"),
        ],
        help="Semantics diagnostics artifact path (repeatable)",
    )
    for version in ACTIVE_STOP_GATE_MANIFEST_VERSIONS:
        parser.add_argument(
            f"--vnext-plus{version}-manifest",
            dest=f"vnext_plus{version}_manifest",
            type=Path,
            default=default_stop_gate_manifest_path(version),
            help=f"vNext+{version} frozen stop-gate fixture manifest path",
        )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    raw_argv = list(sys.argv[1:] if argv is None else argv)
    inactive_flags = find_inactive_stop_gate_manifest_flags(raw_argv)
    if inactive_flags:
        active_versions = ",".join(str(version) for version in ACTIVE_STOP_GATE_MANIFEST_VERSIONS)
        rendered_flags = ", ".join(inactive_flags)
        sys.stderr.write(
            "inactive stop-gate manifest flags are unsupported: "
            f"{rendered_flags} (active versions: {active_versions})\n"
        )
        return 1

    try:
        ensure_deterministic_tooling_env()
    except DeterministicToolingEnvError as exc:
        sys.stderr.write(f"{exc}\n")
        return 1

    args = parse_args(raw_argv)
    manifest_kwargs = {
        f"vnext_plus{version}_manifest_path": getattr(args, f"vnext_plus{version}_manifest")
        for version in ACTIVE_STOP_GATE_MANIFEST_VERSIONS
    }
    stop_gate_input = StopGateMetricsInput.from_legacy_kwargs(
        incident_packet_paths=list(args.incident_packet_paths),
        event_stream_paths=list(args.event_stream_paths),
        connector_snapshot_paths=list(args.connector_snapshot_paths),
        validator_evidence_packet_paths=list(args.validator_evidence_packet_paths),
        semantics_diagnostics_paths=list(args.semantics_diagnostics_paths),
        quality_current_path=args.quality_current,
        quality_baseline_path=args.quality_baseline,
        **manifest_kwargs,
    )
    report = build_stop_gate_metrics_from_input(stop_gate_input)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(canonical_json(report) + "\n", encoding="utf-8")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(stop_gate_markdown(report), encoding="utf-8")
    print(f"wrote {args.out_json}")
    print(f"wrote {args.out_md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
