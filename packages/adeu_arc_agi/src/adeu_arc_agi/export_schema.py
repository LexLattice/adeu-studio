from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .action_rollout import (
    ADEU_ARC_ACTION_PROPOSAL_SCHEMA,
    ADEU_ARC_ROLLOUT_TRACE_SCHEMA,
    AdeuArcActionProposal,
    AdeuArcRolloutTrace,
)
from .local_eval import (
    ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA,
    AdeuArcLocalEvalRecord,
)
from .observation_hypothesis import (
    ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA,
    ADEU_ARC_OBSERVATION_FRAME_SCHEMA,
    AdeuArcHypothesisFrame,
    AdeuArcObservationFrame,
)
from .puzzle_input_bundle import (
    ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA,
    AdeuArcPuzzleInputBundle,
)
from .reasoning_run_record import (
    ADEU_ARC_REASONING_RUN_RECORD_SCHEMA,
    AdeuArcReasoningRunRecord,
)
from .scorecard import (
    ADEU_ARC_SCORECARD_MANIFEST_SCHEMA,
    AdeuArcScorecardManifest,
)
from .submission_execution import (
    ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA,
    AdeuArcSubmissionExecutionRecord,
)
from .task_packet import ADEU_ARC_TASK_PACKET_SCHEMA, AdeuArcTaskPacket
from .three_puzzle_harness import (
    ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA,
    AdeuArcThreePuzzleHarnessRecord,
)


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    task_packet_schema = AdeuArcTaskPacket.model_json_schema(by_alias=True)
    if task_packet_schema["properties"]["schema"]["const"] != ADEU_ARC_TASK_PACKET_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_task_packet@1")
    observation_schema = AdeuArcObservationFrame.model_json_schema(by_alias=True)
    if observation_schema["properties"]["schema"]["const"] != ADEU_ARC_OBSERVATION_FRAME_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_observation_frame@1")
    hypothesis_schema = AdeuArcHypothesisFrame.model_json_schema(by_alias=True)
    if hypothesis_schema["properties"]["schema"]["const"] != ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_hypothesis_frame@1")
    action_proposal_schema = AdeuArcActionProposal.model_json_schema(by_alias=True)
    if action_proposal_schema["properties"]["schema"]["const"] != ADEU_ARC_ACTION_PROPOSAL_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_action_proposal@1")
    rollout_trace_schema = AdeuArcRolloutTrace.model_json_schema(by_alias=True)
    if rollout_trace_schema["properties"]["schema"]["const"] != ADEU_ARC_ROLLOUT_TRACE_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_rollout_trace@1")
    local_eval_record_schema = AdeuArcLocalEvalRecord.model_json_schema(by_alias=True)
    if (
        local_eval_record_schema["properties"]["schema"]["const"]
        != ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA
    ):
        raise ValueError("exported schema marker drift for adeu_arc_local_eval_record@1")
    scorecard_manifest_schema = AdeuArcScorecardManifest.model_json_schema(by_alias=True)
    if (
        scorecard_manifest_schema["properties"]["schema"]["const"]
        != ADEU_ARC_SCORECARD_MANIFEST_SCHEMA
    ):
        raise ValueError("exported schema marker drift for adeu_arc_scorecard_manifest@1")
    submission_execution_schema = AdeuArcSubmissionExecutionRecord.model_json_schema(by_alias=True)
    if (
        submission_execution_schema["properties"]["schema"]["const"]
        != ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA
    ):
        raise ValueError(
            "exported schema marker drift for adeu_arc_submission_execution_record@1"
        )
    puzzle_input_bundle_schema = AdeuArcPuzzleInputBundle.model_json_schema(by_alias=True)
    if (
        puzzle_input_bundle_schema["properties"]["schema"]["const"]
        != ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA
    ):
        raise ValueError("exported schema marker drift for adeu_arc_puzzle_input_bundle@1")
    reasoning_run_record_schema = AdeuArcReasoningRunRecord.model_json_schema(by_alias=True)
    if (
        reasoning_run_record_schema["properties"]["schema"]["const"]
        != ADEU_ARC_REASONING_RUN_RECORD_SCHEMA
    ):
        raise ValueError("exported schema marker drift for adeu_arc_reasoning_run_record@1")
    three_puzzle_harness_schema = AdeuArcThreePuzzleHarnessRecord.model_json_schema(by_alias=True)
    if (
        three_puzzle_harness_schema["properties"]["schema"]["const"]
        != ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA
    ):
        raise ValueError(
            "exported schema marker drift for adeu_arc_three_puzzle_harness_record@1"
        )

    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_task_packet.v1.json",
        task_packet_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_observation_frame.v1.json",
        observation_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_hypothesis_frame.v1.json",
        hypothesis_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_action_proposal.v1.json",
        action_proposal_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_rollout_trace.v1.json",
        rollout_trace_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_local_eval_record.v1.json",
        local_eval_record_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_scorecard_manifest.v1.json",
        scorecard_manifest_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_puzzle_input_bundle.v1.json",
        puzzle_input_bundle_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_reasoning_run_record.v1.json",
        reasoning_run_record_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_arc_agi"
        / "schema"
        / "adeu_arc_submission_execution_record.v1.json",
        submission_execution_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_arc_agi"
        / "schema"
        / "adeu_arc_three_puzzle_harness_record.v1.json",
        three_puzzle_harness_schema,
    )
    _write_schema(root / "spec" / "adeu_arc_task_packet.schema.json", task_packet_schema)
    _write_schema(
        root / "spec" / "adeu_arc_observation_frame.schema.json",
        observation_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_hypothesis_frame.schema.json",
        hypothesis_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_action_proposal.schema.json",
        action_proposal_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_rollout_trace.schema.json",
        rollout_trace_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_local_eval_record.schema.json",
        local_eval_record_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_scorecard_manifest.schema.json",
        scorecard_manifest_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_puzzle_input_bundle.schema.json",
        puzzle_input_bundle_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_reasoning_run_record.schema.json",
        reasoning_run_record_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_submission_execution_record.schema.json",
        submission_execution_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_three_puzzle_harness_record.schema.json",
        three_puzzle_harness_schema,
    )


if __name__ == "__main__":
    main()
