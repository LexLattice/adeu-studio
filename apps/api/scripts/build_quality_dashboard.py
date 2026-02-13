from __future__ import annotations

import argparse
from pathlib import Path

from adeu_api.quality_dashboard import (
    DEFAULT_QUESTION_REPEATS,
    DEFAULT_SESSION_STEPS,
    DETERMINISTIC_EVALUATION_TS,
    write_quality_dashboard,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build CI quality dashboard metrics from eval fixtures."
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("artifacts/quality_dashboard.json"),
        help="Output JSON path",
    )
    parser.add_argument(
        "--question-repeats",
        type=int,
        default=DEFAULT_QUESTION_REPEATS,
        help="Number of repeated /concepts/questions runs per fixture",
    )
    parser.add_argument(
        "--session-steps",
        type=int,
        default=DEFAULT_SESSION_STEPS,
        help="Maximum apply/recheck steps for resolved-session simulation",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        default=None,
        help="Optional baseline quality dashboard for deterministic delta computation",
    )
    parser.add_argument(
        "--evaluation-ts",
        type=str,
        default=DETERMINISTIC_EVALUATION_TS,
        help="Deterministic evaluation timestamp to embed in generated output",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.question_repeats < 1:
        raise ValueError("--question-repeats must be >= 1")
    if args.session_steps < 1:
        raise ValueError("--session-steps must be >= 1")

    dashboard = write_quality_dashboard(
        args.out,
        question_repeats=args.question_repeats,
        session_steps=args.session_steps,
        baseline_path=args.baseline,
        evaluation_ts=args.evaluation_ts,
    )

    metrics = dashboard["metrics"]
    delta_report = dashboard["delta_report"]
    print(f"wrote {args.out}")
    print(
        "redundancy_rate=",
        metrics["redundancy_rate"],
        "top_k_stability@10=",
        metrics["top_k_stability@10"],
        "evidence_coverage_rate=",
        metrics["evidence_coverage_rate"],
        "bridge_loss_utilization_rate=",
        metrics["bridge_loss_utilization_rate"],
        "coherence_alert_count=",
        metrics["coherence_alert_count"],
        "non_negative_quality=",
        delta_report["non_negative_quality"],
    )


if __name__ == "__main__":
    main()
