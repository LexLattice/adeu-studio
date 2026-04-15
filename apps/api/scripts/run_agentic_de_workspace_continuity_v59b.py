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
    DEFAULT_V59A_EVIDENCE_PATH,
    DEFAULT_V59A_LANE_DRIFT_PATH,
    DEFAULT_V59A_LIVE_TURN_ADMISSION_PATH,
    DEFAULT_V59A_LIVE_TURN_HANDOFF_PATH,
    DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    DEFAULT_V59A_OBSERVATION_PATH,
    DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    DEFAULT_V59B_LANE_DRIFT_PATH,
    render_local_effect_restoration_payload,
    render_workspace_continuity_restoration_handoff_payload,
    render_workspace_continuity_restoration_reintegration_payload,
    run_agentic_de_workspace_continuity_v59b,
)
from adeu_agentic_de.workspace_continuity import (  # noqa: E402
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
)
from adeu_ir.repo import repo_root  # noqa: E402
from urm_runtime import CopilotTurnSnapshot  # noqa: E402


def _default_live_turn_snapshot_path() -> Path:
    root = repo_root(anchor=Path(__file__))
    return _default_live_turn_snapshot_path_for_root(root)


def _default_live_turn_snapshot_path_for_root(root: Path) -> Path:
    return (
        root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v59b"
        / "reference_copilot_turn_snapshot.json"
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the bounded V59-B continuity-safe restoration seam over the shipped "
            "V59-A continuity lineage."
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
    parser.add_argument("--v59a-evidence", type=Path, default=DEFAULT_V59A_EVIDENCE_PATH)
    parser.add_argument("--v59b-lane-drift", type=Path, default=DEFAULT_V59B_LANE_DRIFT_PATH)
    parser.add_argument(
        "--target-relative-path",
        default=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    )
    parser.add_argument(
        "--expected-relative-path",
        action="append",
        dest="expected_relative_paths",
        default=None,
    )
    parser.add_argument("--handoff-output", type=Path, default=None)
    parser.add_argument("--restoration-output", type=Path, default=None)
    parser.add_argument("--reintegration-output", type=Path, default=None)
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
        if args.repo_root is None:
            default_root = repo_root(anchor=Path(__file__))
        else:
            default_root = args.repo_root
        live_turn_snapshot_path = (
            args.live_turn_snapshot
            if args.live_turn_snapshot is not None
            else _default_live_turn_snapshot_path_for_root(default_root)
        )
        handoff, restoration, reintegration = run_agentic_de_workspace_continuity_v59b(
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
            lane_drift_path=args.v59b_lane_drift,
            v59a_evidence_path=args.v59a_evidence,
            target_relative_path=args.target_relative_path,
            expected_relative_paths=(
                tuple(args.expected_relative_paths)
                if args.expected_relative_paths
                else None
            ),
        )
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    if args.handoff_output is not None:
        _write_text(
            args.handoff_output,
            render_workspace_continuity_restoration_handoff_payload(handoff),
        )
    if args.restoration_output is not None:
        _write_text(
            args.restoration_output,
            render_local_effect_restoration_payload(restoration),
        )
    if args.reintegration_output is not None:
        _write_text(
            args.reintegration_output,
            render_workspace_continuity_restoration_reintegration_payload(reintegration),
        )
    else:
        sys.stdout.write(
            render_workspace_continuity_restoration_reintegration_payload(reintegration)
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
