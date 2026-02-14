from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from adeu_explain import ConceptAnalysisDelta, DiffReport, ExplainDiffError, FlipExplanation

from .explain_builder import build_explain_packet_payload


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"expected JSON object at {path}")
    return payload


def _write_json(path: Path | None, payload: dict[str, Any], *, pretty: bool) -> None:
    if pretty:
        text = json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    else:
        text = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"
    if path is None:
        sys.stdout.write(text)
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _build_packet_from_payload(payload: dict[str, Any]) -> dict[str, Any]:
    explain_kind = payload.get("explain_kind")
    input_artifact_refs = payload.get("input_artifact_refs")
    diff_report_raw = payload.get("diff_report")
    if not isinstance(explain_kind, str):
        raise ValueError("input must include explain_kind")
    if not isinstance(input_artifact_refs, list):
        raise ValueError("input must include input_artifact_refs list")
    if not isinstance(diff_report_raw, dict):
        raise ValueError("input must include diff_report object")

    diff_report = DiffReport.model_validate(diff_report_raw)
    flip_explanation_raw = payload.get("flip_explanation")
    analysis_delta_raw = payload.get("analysis_delta")
    flip_explanation = (
        FlipExplanation.model_validate(flip_explanation_raw)
        if flip_explanation_raw is not None
        else None
    )
    analysis_delta = (
        ConceptAnalysisDelta.model_validate(analysis_delta_raw)
        if analysis_delta_raw is not None
        else None
    )

    return build_explain_packet_payload(
        explain_kind=explain_kind,
        diff_report=diff_report,
        input_artifact_refs=[str(item) for item in input_artifact_refs],
        flip_explanation=flip_explanation,
        analysis_delta=analysis_delta,
        run_ir_mismatch=payload.get("run_ir_mismatch"),
        left_mismatch=payload.get("left_mismatch"),
        right_mismatch=payload.get("right_mismatch"),
    )


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build deterministic explain_diff@1 packets from normalized input payloads."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    build = subparsers.add_parser("build", help="Build explain_diff@1 packet")
    build.add_argument("--in", dest="in_path", required=True, help="Path to input JSON payload")
    build.add_argument("--out", dest="out_path", help="Path to write output packet JSON")
    build.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print output JSON (still key-sorted).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    if args.command != "build":
        raise RuntimeError("unsupported explain-tools command")

    try:
        payload = _load_json(Path(args.in_path))
        packet = _build_packet_from_payload(payload)
        out_path = Path(args.out_path) if args.out_path else None
        _write_json(out_path, packet, pretty=bool(args.pretty))
    except (json.JSONDecodeError, OSError, ValueError, ExplainDiffError) as exc:
        print(f"explain-tools: {exc}", file=sys.stderr)
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
