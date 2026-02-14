from __future__ import annotations

import argparse
from pathlib import Path

from urm_runtime.hashing import canonical_json
from urm_runtime.stop_gate_tools import build_stop_gate_metrics, stop_gate_markdown


def parse_args() -> argparse.Namespace:
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
    parser.add_argument(
        "--vnext-plus7-manifest",
        type=Path,
        default=Path("apps/api/fixtures/stop_gate/vnext_plus7_manifest.json"),
        help="vNext+7 frozen stop-gate fixture manifest path",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    report = build_stop_gate_metrics(
        incident_packet_paths=list(args.incident_packet_paths),
        event_stream_paths=list(args.event_stream_paths),
        connector_snapshot_paths=list(args.connector_snapshot_paths),
        validator_evidence_packet_paths=list(args.validator_evidence_packet_paths),
        semantics_diagnostics_paths=list(args.semantics_diagnostics_paths),
        quality_current_path=args.quality_current,
        quality_baseline_path=args.quality_baseline,
        vnext_plus7_manifest_path=args.vnext_plus7_manifest,
    )
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(canonical_json(report) + "\n", encoding="utf-8")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(stop_gate_markdown(report), encoding="utf-8")
    print(f"wrote {args.out_json}")
    print(f"wrote {args.out_md}")


if __name__ == "__main__":
    main()
