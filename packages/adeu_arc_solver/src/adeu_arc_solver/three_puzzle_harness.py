from __future__ import annotations

from typing import Any, Literal

from adeu_arc_agi import derive_v42g3_arc_three_puzzle_harness_record


def derive_v42g3_three_puzzle_harness_record(
    *,
    puzzle_input_bundle: dict[str, Any],
    harness_run_id: str,
    harness_execution_status: Literal[
        "in_progress",
        "completed",
        "completed_with_failures",
        "invalid",
    ],
    harness_sequence_register: str,
    config_consistency_posture: Literal[
        "uniform_across_all_puzzles",
        "explicit_divergence_declared",
    ],
    puzzle_run_inputs: list[dict[str, Any]],
    run_summary: str,
    evidence_refs: list[str],
    aggregated_local_eval_ref: str | None = None,
    aggregated_scorecard_posture_ref: str | None = None,
    aggregated_submission_posture_ref: str | None = None,
) -> dict[str, Any]:
    return derive_v42g3_arc_three_puzzle_harness_record(
        puzzle_input_bundle=puzzle_input_bundle,
        harness_run_id=harness_run_id,
        harness_execution_status=harness_execution_status,
        harness_sequence_register=harness_sequence_register,
        config_consistency_posture=config_consistency_posture,
        puzzle_run_inputs=puzzle_run_inputs,
        run_summary=run_summary,
        evidence_refs=evidence_refs,
        aggregated_local_eval_ref=aggregated_local_eval_ref,
        aggregated_scorecard_posture_ref=aggregated_scorecard_posture_ref,
        aggregated_submission_posture_ref=aggregated_submission_posture_ref,
    )
