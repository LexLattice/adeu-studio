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
    DEFAULT_V56C_V56A_EVIDENCE_PATH,
    DEFAULT_V56C_V56B_EVIDENCE_PATH,
    DEFAULT_V57A_EVIDENCE_PATH,
    DEFAULT_V57A_LANE_DRIFT_PATH,
    DEFAULT_V57A_LOCAL_EFFECT_CONFORMANCE_PATH,
    DEFAULT_V57A_OBSERVATION_PATH,
    DEFAULT_V57A_V56C_EVIDENCE_PATH,
    DEFAULT_V57B_EVIDENCE_PATH,
    DEFAULT_V57B_LANE_DRIFT_PATH,
    DEFAULT_V57B_RESTORATION_PATH,
    DEFAULT_V57C_LANE_DRIFT_PATH,
    render_local_effect_hardening_payload,
    run_agentic_de_local_effect_v57c,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Evaluate the advisory-only V57-C local hardening decision slice over the "
            "shipped observed-and-restored create_new exemplar."
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
    parser.add_argument("--v57a-lane-drift", type=Path, default=DEFAULT_V57A_LANE_DRIFT_PATH)
    parser.add_argument("--v57a-observation", type=Path, default=DEFAULT_V57A_OBSERVATION_PATH)
    parser.add_argument(
        "--v57a-local-effect-conformance",
        type=Path,
        default=DEFAULT_V57A_LOCAL_EFFECT_CONFORMANCE_PATH,
    )
    parser.add_argument("--v57b-lane-drift", type=Path, default=DEFAULT_V57B_LANE_DRIFT_PATH)
    parser.add_argument("--v57b-restoration", type=Path, default=DEFAULT_V57B_RESTORATION_PATH)
    parser.add_argument("--lane-drift", type=Path, default=DEFAULT_V57C_LANE_DRIFT_PATH)
    parser.add_argument("--v56a-evidence", type=Path, default=DEFAULT_V56C_V56A_EVIDENCE_PATH)
    parser.add_argument("--v56b-evidence", type=Path, default=DEFAULT_V56C_V56B_EVIDENCE_PATH)
    parser.add_argument("--v56c-evidence", type=Path, default=DEFAULT_V57A_V56C_EVIDENCE_PATH)
    parser.add_argument("--v57a-evidence", type=Path, default=DEFAULT_V57A_EVIDENCE_PATH)
    parser.add_argument("--v57b-evidence", type=Path, default=DEFAULT_V57B_EVIDENCE_PATH)
    parser.add_argument("--hardening-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        register = run_agentic_de_local_effect_v57c(
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
            v57a_lane_drift_path=args.v57a_lane_drift,
            v57a_observation_path=args.v57a_observation,
            v57a_local_effect_conformance_path=args.v57a_local_effect_conformance,
            v57b_lane_drift_path=args.v57b_lane_drift,
            v57b_restoration_path=args.v57b_restoration,
            lane_drift_path=args.lane_drift,
            v56a_evidence_path=args.v56a_evidence,
            v56b_evidence_path=args.v56b_evidence,
            v56c_evidence_path=args.v56c_evidence,
            v57a_evidence_path=args.v57a_evidence,
            v57b_evidence_path=args.v57b_evidence,
        )
    except (FileNotFoundError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2

    payload = render_local_effect_hardening_payload(register)
    if args.hardening_output:
        _write_text(args.hardening_output, payload)
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
