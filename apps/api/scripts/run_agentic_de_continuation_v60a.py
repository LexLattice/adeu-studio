from __future__ import annotations

import argparse
import json
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
    DEFAULT_V59A_LANE_DRIFT_PATH,
    DEFAULT_V59A_LIVE_TURN_ADMISSION_PATH,
    DEFAULT_V59A_LIVE_TURN_HANDOFF_PATH,
    DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    DEFAULT_V59A_OBSERVATION_PATH,
    DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    DEFAULT_V59B_CONTINUITY_RESTORATION_HANDOFF_PATH,
    DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH,
    DEFAULT_V59B_LANE_DRIFT_PATH,
    DEFAULT_V59B_RESTORATION_PATH,
    DEFAULT_V59C_HARDENING_PATH,
    DEFAULT_V59C_LANE_DRIFT_PATH,
    DEFAULT_V60A_LANE_DRIFT_PATH,
    DEFAULT_V60A_SEED_INTENT_PATH,
    render_continuation_decision_payload,
    render_loop_state_ledger_payload,
    render_seed_intent_payload,
    render_task_charter_payload,
    render_task_residual_payload,
    run_agentic_de_continuation_v60a,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)
from adeu_ir.repo import repo_root  # noqa: E402
from urm_runtime import CopilotTurnSnapshot  # noqa: E402


def _default_live_turn_snapshot_path_for_root(root: Path) -> Path:
    return (
        root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v60a"
        / "reference_copilot_turn_snapshot.json"
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V60-A continuation / residual-intent starter over one typed "
            "seed intent and the shipped V56/V59 lineage."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument("--live-turn-snapshot", type=Path, default=None)
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
    parser.add_argument("--v59c-lane-drift", type=Path, default=DEFAULT_V59C_LANE_DRIFT_PATH)
    parser.add_argument("--v59c-hardening", type=Path, default=DEFAULT_V59C_HARDENING_PATH)
    parser.add_argument("--v60a-lane-drift", type=Path, default=DEFAULT_V60A_LANE_DRIFT_PATH)
    parser.add_argument("--seed-intent", type=Path, default=DEFAULT_V60A_SEED_INTENT_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument("--seed-intent-output", type=Path, default=None)
    parser.add_argument("--task-charter-output", type=Path, default=None)
    parser.add_argument("--task-residual-output", type=Path, default=None)
    parser.add_argument("--loop-state-ledger-output", type=Path, default=None)
    parser.add_argument("--continuation-decision-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def _load_live_turn_snapshot(path: Path) -> CopilotTurnSnapshot:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("live-turn snapshot payload must be an object")
    return CopilotTurnSnapshot.model_validate(payload)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        default_root = (
            repo_root(anchor=Path(__file__)) if args.repo_root is None else args.repo_root
        )
        live_turn_snapshot_path = (
            args.live_turn_snapshot
            if args.live_turn_snapshot is not None
            else _default_live_turn_snapshot_path_for_root(default_root)
        )
        (
            seed_intent,
            task_charter,
            task_residual,
            loop_state_ledger,
            continuation_decision,
        ) = run_agentic_de_continuation_v60a(
            live_turn_snapshot=_load_live_turn_snapshot(live_turn_snapshot_path),
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
            v59c_lane_drift_path=args.v59c_lane_drift,
            v59c_hardening_path=args.v59c_hardening,
            lane_drift_path=args.v60a_lane_drift,
            seed_intent_path=args.seed_intent,
            target_relative_path=args.target_relative_path,
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    seed_intent_payload = render_seed_intent_payload(seed_intent)
    task_charter_payload = render_task_charter_payload(task_charter)
    task_residual_payload = render_task_residual_payload(task_residual)
    loop_state_ledger_payload = render_loop_state_ledger_payload(loop_state_ledger)
    continuation_decision_payload = render_continuation_decision_payload(continuation_decision)

    if args.seed_intent_output is not None:
        _write_text(args.seed_intent_output, seed_intent_payload)
    if args.task_charter_output is not None:
        _write_text(args.task_charter_output, task_charter_payload)
    if args.task_residual_output is not None:
        _write_text(args.task_residual_output, task_residual_payload)
    if args.loop_state_ledger_output is not None:
        _write_text(args.loop_state_ledger_output, loop_state_ledger_payload)
    if args.continuation_decision_output is not None:
        _write_text(args.continuation_decision_output, continuation_decision_payload)
    else:
        sys.stdout.write(continuation_decision_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
