from __future__ import annotations

import argparse
from pathlib import Path

from adeu_api.quality_dashboard import (
    DEFAULT_QUESTION_REPEATS,
    DEFAULT_SESSION_STEPS,
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
    )

    metrics = dashboard["metrics"]
    print(f"wrote {args.out}")
    print(
        "question_stability_pct=",
        metrics["question_stability_pct"],
        "avg_questions_per_ir=",
        metrics["avg_questions_per_ir"],
        "avg_resolved_per_session=",
        metrics["avg_resolved_per_session"],
        "avg_solver_calls_per_action=",
        metrics["avg_solver_calls_per_action"],
    )


if __name__ == "__main__":
    main()
