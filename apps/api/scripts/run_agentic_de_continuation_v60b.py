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
    DEFAULT_ACTION_PROPOSAL_PATH,
    DEFAULT_DOMAIN_PACKET_PATH,
    DEFAULT_INTERACTION_CONTRACT_PATH,
    DEFAULT_MORPH_IR_PATH,
    DEFAULT_V56A_CHECKPOINT_PATH,
    DEFAULT_V56A_CONFORMANCE_PATH,
    DEFAULT_V56A_DIAGNOSTICS_PATH,
    DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH,
    DEFAULT_V56B_CONFORMANCE_PATH,
    DEFAULT_V56B_DIAGNOSTICS_PATH,
    DEFAULT_V56B_LANE_DRIFT_PATH,
    DEFAULT_V56B_RUNTIME_STATE_PATH,
    DEFAULT_V56B_TICKET_PATH,
    DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    DEFAULT_V56C_LANE_DRIFT_PATH,
    DEFAULT_V56C_MIGRATION_DECISION_PATH,
    DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    DEFAULT_V59A_CONTINUITY_ADMISSION_PATH,
    DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH,
    DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    DEFAULT_V59A_EVIDENCE_PATH,
    DEFAULT_V59A_LANE_DRIFT_PATH,
    DEFAULT_V59A_LIVE_TURN_ADMISSION_PATH,
    DEFAULT_V59A_LIVE_TURN_HANDOFF_PATH,
    DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    DEFAULT_V59A_OBSERVATION_PATH,
    DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    DEFAULT_V59B_CONTINUITY_RESTORATION_HANDOFF_PATH,
    DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH,
    DEFAULT_V59B_EVIDENCE_PATH,
    DEFAULT_V59B_LANE_DRIFT_PATH,
    DEFAULT_V59B_RESTORATION_PATH,
    DEFAULT_V60A_CONTINUATION_DECISION_PATH,
    DEFAULT_V60A_EVIDENCE_PATH,
    DEFAULT_V60A_LANE_DRIFT_PATH,
    DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    DEFAULT_V60A_SEED_INTENT_PATH,
    DEFAULT_V60A_TASK_CHARTER_PATH,
    DEFAULT_V60A_TASK_RESIDUAL_PATH,
    DEFAULT_V60B_LANE_DRIFT_PATH,
    render_continuation_refresh_decision_payload,
    render_task_residual_refresh_payload,
    run_agentic_de_continuation_v60b,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V60-B continuation refresh / reproposal seam over the shipped "
            "V60-A loop identity and one latest reintegrated downstream act lineage."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument("--domain-packet", type=Path, default=DEFAULT_DOMAIN_PACKET_PATH)
    parser.add_argument("--morph-ir", type=Path, default=DEFAULT_MORPH_IR_PATH)
    parser.add_argument(
        "--interaction-contract",
        type=Path,
        default=DEFAULT_INTERACTION_CONTRACT_PATH,
    )
    parser.add_argument("--action-proposal", type=Path, default=DEFAULT_ACTION_PROPOSAL_PATH)
    parser.add_argument("--v56a-checkpoint", type=Path, default=DEFAULT_V56A_CHECKPOINT_PATH)
    parser.add_argument("--v56a-diagnostics", type=Path, default=DEFAULT_V56A_DIAGNOSTICS_PATH)
    parser.add_argument("--v56a-conformance", type=Path, default=DEFAULT_V56A_CONFORMANCE_PATH)
    parser.add_argument("--v56b-lane-drift", type=Path, default=DEFAULT_V56B_LANE_DRIFT_PATH)
    parser.add_argument(
        "--v56b-action-class-taxonomy",
        type=Path,
        default=DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH,
    )
    parser.add_argument("--v56b-runtime-state", type=Path, default=DEFAULT_V56B_RUNTIME_STATE_PATH)
    parser.add_argument("--v56b-action-ticket", type=Path, default=DEFAULT_V56B_TICKET_PATH)
    parser.add_argument("--v56b-diagnostics", type=Path, default=DEFAULT_V56B_DIAGNOSTICS_PATH)
    parser.add_argument("--v56b-conformance", type=Path, default=DEFAULT_V56B_CONFORMANCE_PATH)
    parser.add_argument("--v56c-lane-drift", type=Path, default=DEFAULT_V56C_LANE_DRIFT_PATH)
    parser.add_argument(
        "--v56c-runtime-harvest",
        type=Path,
        default=DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    )
    parser.add_argument(
        "--v56c-governance-calibration",
        type=Path,
        default=DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    )
    parser.add_argument(
        "--v56c-migration-decision",
        type=Path,
        default=DEFAULT_V56C_MIGRATION_DECISION_PATH,
    )
    parser.add_argument("--v59a-lane-drift", type=Path, default=DEFAULT_V59A_LANE_DRIFT_PATH)
    parser.add_argument(
        "--v59a-continuity-region",
        type=Path,
        default=DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH,
    )
    parser.add_argument(
        "--v59a-continuity-admission",
        type=Path,
        default=DEFAULT_V59A_CONTINUITY_ADMISSION_PATH,
    )
    parser.add_argument("--v59a-occupancy", type=Path, default=DEFAULT_V59A_OCCUPANCY_REPORT_PATH)
    parser.add_argument(
        "--v59a-live-turn-admission",
        type=Path,
        default=DEFAULT_V59A_LIVE_TURN_ADMISSION_PATH,
    )
    parser.add_argument(
        "--v59a-live-turn-handoff",
        type=Path,
        default=DEFAULT_V59A_LIVE_TURN_HANDOFF_PATH,
    )
    parser.add_argument("--v59a-observation", type=Path, default=DEFAULT_V59A_OBSERVATION_PATH)
    parser.add_argument(
        "--v59a-local-effect-conformance",
        type=Path,
        default=DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    )
    parser.add_argument(
        "--v59a-live-turn-reintegration",
        type=Path,
        default=DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    )
    parser.add_argument(
        "--v59a-continuity-reintegration",
        type=Path,
        default=DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    )
    parser.add_argument("--v59b-lane-drift", type=Path, default=DEFAULT_V59B_LANE_DRIFT_PATH)
    parser.add_argument(
        "--v59b-continuity-restoration-handoff",
        type=Path,
        default=DEFAULT_V59B_CONTINUITY_RESTORATION_HANDOFF_PATH,
    )
    parser.add_argument("--v59b-restoration", type=Path, default=DEFAULT_V59B_RESTORATION_PATH)
    parser.add_argument(
        "--v59b-continuity-restoration-reintegration",
        type=Path,
        default=DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH,
    )
    parser.add_argument("--v60a-lane-drift", type=Path, default=DEFAULT_V60A_LANE_DRIFT_PATH)
    parser.add_argument("--v60a-seed-intent", type=Path, default=DEFAULT_V60A_SEED_INTENT_PATH)
    parser.add_argument("--v60a-task-charter", type=Path, default=DEFAULT_V60A_TASK_CHARTER_PATH)
    parser.add_argument("--v60a-task-residual", type=Path, default=DEFAULT_V60A_TASK_RESIDUAL_PATH)
    parser.add_argument(
        "--v60a-loop-state-ledger", type=Path, default=DEFAULT_V60A_LOOP_STATE_LEDGER_PATH
    )
    parser.add_argument(
        "--v60a-continuation-decision",
        type=Path,
        default=DEFAULT_V60A_CONTINUATION_DECISION_PATH,
    )
    parser.add_argument("--v60b-lane-drift", type=Path, default=DEFAULT_V60B_LANE_DRIFT_PATH)
    parser.add_argument("--v59a-evidence", type=Path, default=DEFAULT_V59A_EVIDENCE_PATH)
    parser.add_argument("--v59b-evidence", type=Path, default=DEFAULT_V59B_EVIDENCE_PATH)
    parser.add_argument("--v60a-evidence", type=Path, default=DEFAULT_V60A_EVIDENCE_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--task-residual-refresh-output", type=Path, default=None)
    parser.add_argument("--continuation-refresh-decision-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        refreshed_task_residual, refreshed_continuation_decision = (
            run_agentic_de_continuation_v60b(
                repo_root_path=args.repo_root,
                domain_packet_path=args.domain_packet,
                morph_ir_path=args.morph_ir,
                interaction_contract_path=args.interaction_contract,
                action_proposal_path=args.action_proposal,
                v56a_checkpoint_path=args.v56a_checkpoint,
                v56a_diagnostics_path=args.v56a_diagnostics,
                v56a_conformance_path=args.v56a_conformance,
                v56b_lane_drift_path=args.v56b_lane_drift,
                v56b_action_class_taxonomy_path=args.v56b_action_class_taxonomy,
                v56b_runtime_state_path=args.v56b_runtime_state,
                v56b_action_ticket_path=args.v56b_action_ticket,
                v56b_diagnostics_path=args.v56b_diagnostics,
                v56b_conformance_path=args.v56b_conformance,
                v56c_lane_drift_path=args.v56c_lane_drift,
                v56c_runtime_harvest_path=args.v56c_runtime_harvest,
                v56c_governance_calibration_path=args.v56c_governance_calibration,
                v56c_migration_decision_path=args.v56c_migration_decision,
                v59a_lane_drift_path=args.v59a_lane_drift,
                v59a_continuity_region_path=args.v59a_continuity_region,
                v59a_continuity_admission_path=args.v59a_continuity_admission,
                v59a_occupancy_path=args.v59a_occupancy,
                v59a_live_turn_admission_path=args.v59a_live_turn_admission,
                v59a_live_turn_handoff_path=args.v59a_live_turn_handoff,
                v59a_observation_path=args.v59a_observation,
                v59a_local_effect_conformance_path=args.v59a_local_effect_conformance,
                v59a_live_turn_reintegration_path=args.v59a_live_turn_reintegration,
                v59a_continuity_reintegration_path=args.v59a_continuity_reintegration,
                v59b_lane_drift_path=args.v59b_lane_drift,
                v59b_continuity_restoration_handoff_path=args.v59b_continuity_restoration_handoff,
                v59b_restoration_path=args.v59b_restoration,
                v59b_continuity_restoration_reintegration_path=(
                    args.v59b_continuity_restoration_reintegration
                ),
                v60a_lane_drift_path=args.v60a_lane_drift,
                v60a_seed_intent_path=args.v60a_seed_intent,
                v60a_task_charter_path=args.v60a_task_charter,
                v60a_task_residual_path=args.v60a_task_residual,
                v60a_loop_state_ledger_path=args.v60a_loop_state_ledger,
                v60a_continuation_decision_path=args.v60a_continuation_decision,
                lane_drift_path=args.v60b_lane_drift,
                v59a_evidence_path=args.v59a_evidence,
                v59b_evidence_path=args.v59b_evidence,
                v60a_evidence_path=args.v60a_evidence,
                target_relative_path=args.target_relative_path,
            )
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    task_residual_refresh_payload = render_task_residual_refresh_payload(refreshed_task_residual)
    continuation_refresh_decision_payload = render_continuation_refresh_decision_payload(
        refreshed_continuation_decision
    )

    if args.task_residual_refresh_output is not None:
        _write_text(args.task_residual_refresh_output, task_residual_refresh_payload)
    if args.continuation_refresh_decision_output is not None:
        _write_text(
            args.continuation_refresh_decision_output,
            continuation_refresh_decision_payload,
        )
    else:
        sys.stdout.write(continuation_refresh_decision_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
