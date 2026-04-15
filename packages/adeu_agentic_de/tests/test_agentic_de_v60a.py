from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_continuation_v60a
from adeu_agentic_de.workspace_continuity import (
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
    DESIGNATED_WORKSPACE_CONTINUITY_ROOT,
)
from adeu_ir.repo import repo_root
from urm_runtime import CopilotTurnSnapshot

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v60a"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v56a",
    "packages/adeu_agentic_de/tests/fixtures/v56b",
    "packages/adeu_agentic_de/tests/fixtures/v56c",
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v59b",
    "packages/adeu_agentic_de/tests/fixtures/v59c",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
    "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
    "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
    "artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json",
    "artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json",
    "artifacts/agent_harness/v157/evidence_inputs/v57c_local_effect_hardening_evidence_v157.json",
    "artifacts/agent_harness/v158/evidence_inputs/v58a_live_harness_bind_evidence_v158.json",
    "artifacts/agent_harness/v159/evidence_inputs/v58b_live_restoration_state_evidence_v159.json",
    "artifacts/agent_harness/v160/evidence_inputs/v58c_live_harness_hardening_evidence_v160.json",
    "artifacts/agent_harness/v161/evidence_inputs/v59a_workspace_continuity_starter_evidence_v161.json",
    "artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json",
    "artifacts/agent_harness/v163/evidence_inputs/v59c_workspace_continuity_hardening_evidence_v163.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v60a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
    repo_root_path = _repo_root_path()
    for relative_dir in FIXTURE_DIRS:
        shutil.copytree(
            repo_root_path / relative_dir,
            tmp_path / relative_dir,
            dirs_exist_ok=True,
        )
    extra_paths = [
        *EVIDENCE_FILES,
        "artifacts/agentic_de/v59/workspace_continuity/.gitignore",
    ]
    for relative_path in extra_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return (
        tmp_path,
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v60a",
    )


def _load_snapshot(root: Path) -> CopilotTurnSnapshot:
    return CopilotTurnSnapshot.model_validate(
        _load_json(root, "reference_copilot_turn_snapshot.json")
    )


def _expected_selected_path_summary() -> str:
    return (
        "urm_copilot_session_path::local_write/create_new::"
        f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/"
        f"{DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH.as_posix()}"
    )


def test_reference_outputs_match_live_v60a_runner(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60a_input_tree(tmp_path)

    seed_intent, task_charter, task_residual, loop_state_ledger, continuation_decision = (
        run_agentic_de_continuation_v60a(
            repo_root_path=temp_root,
            live_turn_snapshot=_load_snapshot(fixture_root),
        )
    )

    assert seed_intent.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_seed_intent_record.json",
    )
    assert task_charter.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_task_charter_packet.json",
    )
    assert task_residual.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_task_residual_packet.json",
    )
    assert loop_state_ledger.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_loop_state_ledger.json",
    )
    assert continuation_decision.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_continuation_decision_record.json",
    )


def test_v60a_outputs_remain_evidence_only_and_exact_path_bound(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60a_input_tree(tmp_path)

    seed_intent, task_charter, task_residual, loop_state_ledger, continuation_decision = (
        run_agentic_de_continuation_v60a(
            repo_root_path=temp_root,
            live_turn_snapshot=_load_snapshot(fixture_root),
        )
    )

    assert seed_intent.target_arc == "vNext+164"
    assert seed_intent.target_path == "V60-A"
    assert seed_intent.evidence_only is True
    assert task_charter.selected_downstream_path_summary == _expected_selected_path_summary()
    assert task_charter.frozen_policy_basis_ref == (
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS164.md#machine-checkable-contract"
    )
    assert task_residual.open_approval_refs == []
    assert "deferred" in task_residual.open_obligation_summary
    assert loop_state_ledger.latest_continuity_reintegration_ref_or_none is not None
    assert continuation_decision.continuation_outcome == "continue_to_governed_act"
    assert continuation_decision.selected_next_path_summary == _expected_selected_path_summary()
    assert "communication_law_still_deferred_to_v61" in (
        continuation_decision.continuation_reason_codes
    )


def test_selected_downstream_path_drift_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60a_input_tree(tmp_path)
    seed_intent_path = fixture_root / "reference_agentic_de_seed_intent_record.json"
    payload = _load_json(fixture_root, "reference_agentic_de_seed_intent_record.json")
    assert isinstance(payload, dict)
    payload["selected_downstream_path_summary"] = (
        "urm_copilot_session_path::local_write/create_new::"
        "artifacts/agentic_de/v59/workspace_continuity/runtime/widened.diff"
    )
    payload["seed_intent_id"] = None
    seed_intent_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="exact shipped downstream path"):
        run_agentic_de_continuation_v60a(
            repo_root_path=temp_root,
            live_turn_snapshot=_load_snapshot(fixture_root),
        )


def test_live_turn_mismatch_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60a_input_tree(tmp_path)
    payload = _load_json(fixture_root, "reference_copilot_turn_snapshot.json")
    assert isinstance(payload, dict)
    payload["selected_turn_id"] = "turn-v60a-mismatch"

    with pytest.raises(ValueError, match="same live turn"):
        run_agentic_de_continuation_v60a(
            repo_root_path=temp_root,
            live_turn_snapshot=CopilotTurnSnapshot.model_validate(payload),
        )
