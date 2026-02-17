from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path
from typing import Any

from adeu_api.paper_pipeline import (
    build_flow_gate_diagnostics,
    classify_flow_divergence,
    derive_cleaned_source_text,
    select_best_flow,
)
from adeu_api.urm_routes import _reset_manager_for_tests, urm_tool_call_endpoint
from urm_runtime.hashing import canonical_json
from urm_runtime.models import ToolCallRequest


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run deterministic paper abstract pipeline over a local PDF.",
    )
    parser.add_argument(
        "--pdf",
        type=Path,
        required=True,
        help="Path to input PDF.",
    )
    parser.add_argument(
        "--title",
        type=str,
        default=None,
        help="Optional paper title override.",
    )
    parser.add_argument(
        "--min-words",
        type=int,
        default=20,
        help="Minimum abstract word count constraint.",
    )
    parser.add_argument(
        "--max-words",
        type=int,
        default=220,
        help="Maximum abstract word count constraint.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("artifacts/manual_runs/paper_pipeline_summary.json"),
        help="Output JSON path for paper pipeline summary.",
    )
    return parser.parse_args(argv)


def _extract_pdf_text(pdf_path: Path) -> str:
    if not pdf_path.is_file():
        raise FileNotFoundError(f"pdf not found: {pdf_path}")
    try:
        completed = subprocess.run(
            ["pdftotext", str(pdf_path), "-"],
            check=True,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as exc:
        raise RuntimeError("pdftotext is required to run this pipeline script") from exc
    return completed.stdout


def _tool_call(tool_name: str, arguments: dict[str, Any]) -> dict[str, Any]:
    response = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name=tool_name,
            arguments=arguments,
        )
    )
    return response.model_dump(mode="json")


def _run_flow(
    *,
    label: str,
    source_text: str,
    title: str,
    min_words: int,
    max_words: int,
) -> dict[str, Any]:
    ingest = _tool_call(
        "paper.ingest_text",
        {
            "title": title,
            "source_text": source_text,
        },
    )
    extract = _tool_call(
        "paper.extract_abstract_candidate",
        {
            "source_text": source_text,
        },
    )
    abstract_text = str(extract["result"]["abstract_text"])
    check = _tool_call(
        "paper.check_constraints",
        {
            "abstract_text": abstract_text,
            "min_words": min_words,
            "max_words": max_words,
        },
    )
    emit = _tool_call(
        "paper.emit_artifact",
        {
            "title": title,
            "abstract_text": abstract_text,
            "checks": check["result"]["checks"],
        },
    )
    diagnostics = build_flow_gate_diagnostics(
        extract_result=extract["result"],
        check_result=check["result"],
    )
    return {
        "label": label,
        "input_chars": len(source_text),
        "ingest": ingest,
        "extract": extract,
        "check": check,
        "emit": emit,
        "constraint_passes": bool(check["result"]["passes"]),
        "structural_passes": diagnostics["structural_passes"],
        "gate_results": diagnostics["gate_results"],
        "fail_codes": diagnostics["fail_codes"],
    }


def _flow_by_label(flows: list[dict[str, Any]], *, label: str) -> dict[str, Any] | None:
    for flow in flows:
        if flow.get("label") == label:
            return flow
    return None


def _build_summary(
    *,
    pdf_path: Path,
    title: str,
    raw_text: str,
    cleaned_text: str,
    min_words: int,
    max_words: int,
) -> dict[str, Any]:
    flows = [
        _run_flow(
            label="raw_pdf_text",
            source_text=raw_text,
            title=title,
            min_words=min_words,
            max_words=max_words,
        ),
        _run_flow(
            label="cleaned_text",
            source_text=cleaned_text,
            title=title,
            min_words=min_words,
            max_words=max_words,
        ),
    ]
    selected_flow, selection_reason = select_best_flow(flows)
    selected_label = str(selected_flow["label"])
    selected_extract = selected_flow["extract"]["result"]
    flows_diverged, divergence_class = classify_flow_divergence(flows)
    raw_flow = _flow_by_label(flows, label="raw_pdf_text")
    raw_parse_degraded = True
    if raw_flow is not None:
        raw_parse_degraded = not bool(raw_flow.get("structural_passes"))
    selected_structural_passes = bool(selected_flow.get("structural_passes"))
    selected_fail_codes = selected_flow.get("fail_codes")
    if not isinstance(selected_fail_codes, list):
        selected_fail_codes = []
    final_parse_quality = (
        "ok"
        if selected_structural_passes and divergence_class != "major"
        else "degraded"
    )

    return {
        "schema": "paper_pipeline_summary@1",
        "pdf_path": str(pdf_path),
        "title": title,
        "flows": flows,
        "selected_flow": selected_label,
        "selected_candidate_hash": selected_extract.get("candidate_hash"),
        "selected_artifact_id": selected_flow["emit"]["result"].get("artifact_id"),
        "selection_reason": selection_reason,
        "selected_fail_codes": selected_fail_codes,
        "fallback_used": selected_label != "raw_pdf_text",
        "parse_degraded_raw": raw_parse_degraded,
        "final_parse_quality": final_parse_quality,
        "selected_word_count": selected_extract.get("word_count"),
        "flows_diverged": flows_diverged,
        "divergence_class": divergence_class,
        "divergence_reason_codes": (
            ["ARTIFACT_ID_MISMATCH", f"CLASS_{divergence_class.upper()}"]
            if flows_diverged
            else ["ARTIFACT_ID_MATCH"]
        ),
        "selected_gate_results": selected_flow.get("gate_results"),
    }


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    raw_text = _extract_pdf_text(args.pdf)
    cleaned_text = derive_cleaned_source_text(raw_text)
    title = args.title or args.pdf.stem

    _reset_manager_for_tests()
    try:
        summary = _build_summary(
            pdf_path=args.pdf,
            title=title,
            raw_text=raw_text,
            cleaned_text=cleaned_text,
            min_words=args.min_words,
            max_words=args.max_words,
        )
    finally:
        _reset_manager_for_tests()

    args.out.parent.mkdir(parents=True, exist_ok=True)
    raw_path = args.out.parent / "paper_raw_text.txt"
    cleaned_path = args.out.parent / "paper_cleaned_text.txt"
    raw_path.write_text(raw_text, encoding="utf-8")
    cleaned_path.write_text(cleaned_text, encoding="utf-8")
    summary["raw_text_path"] = str(raw_path)
    summary["cleaned_text_path"] = str(cleaned_path)
    args.out.write_text(canonical_json(summary) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
