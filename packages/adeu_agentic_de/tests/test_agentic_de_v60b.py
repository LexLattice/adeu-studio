from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import (
    load_loop_state_ledger,
    load_task_residual_packet,
    run_agentic_de_continuation_v60b,
)
from adeu_agentic_de.workspace_continuity import (
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
    DESIGNATED_WORKSPACE_CONTINUITY_ROOT,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v60b"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v56a",
    "packages/adeu_agentic_de/tests/fixtures/v56b",
    "packages/adeu_agentic_de/tests/fixtures/v56c",
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v59b",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v161/evidence_inputs/v59a_workspace_continuity_starter_evidence_v161.json",
    "artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json",
    "artifacts/agent_harness/v164/evidence_inputs/v60a_continuation_starter_evidence_v164.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v60b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
    repo_root_path = _repo_root_path()
    for relative_dir in FIXTURE_DIRS:
        shutil.copytree(
            repo_root_path / relative_dir,
            tmp_path / relative_dir,
            dirs_exist_ok=True,
        )
    for relative_path in EVIDENCE_FILES:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return (
        tmp_path,
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v60b",
    )


def _expected_selected_path_summary() -> str:
    return (
        "urm_copilot_session_path::local_write/create_new::"
        f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/"
        f"{DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH.as_posix()}"
    )


def _reanchor_v60a_chain_after_residual_mutation(v60a_root: Path) -> None:
    task_residual_path = v60a_root / "reference_agentic_de_task_residual_packet.json"
    loop_state_ledger_path = v60a_root / "reference_agentic_de_loop_state_ledger.json"
    continuation_decision_path = (
        v60a_root / "reference_agentic_de_continuation_decision_record.json"
    )

    residual = load_task_residual_packet(task_residual_path)
    loop_state_payload = json.loads(loop_state_ledger_path.read_text(encoding="utf-8"))
    loop_state_payload["task_residual_ref"] = residual.residual_id
    loop_state_payload["ledger_id"] = None
    loop_state_ledger_path.write_text(
        json.dumps(loop_state_payload, indent=2) + "\n",
        encoding="utf-8",
    )

    loop_state_ledger = load_loop_state_ledger(loop_state_ledger_path)
    continuation_decision_payload = json.loads(
        continuation_decision_path.read_text(encoding="utf-8")
    )
    continuation_decision_payload["loop_state_ledger_ref"] = loop_state_ledger.ledger_id
    continuation_decision_payload["decision_id"] = None
    continuation_decision_path.write_text(
        json.dumps(continuation_decision_payload, indent=2) + "\n",
        encoding="utf-8",
    )


def test_reference_outputs_match_live_v60b_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60b_input_tree(tmp_path)

    refreshed_task_residual, refreshed_continuation_decision = run_agentic_de_continuation_v60b(
        repo_root_path=temp_root,
    )

    assert refreshed_task_residual.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_task_residual_refresh_packet.json",
    )
    assert refreshed_continuation_decision.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_continuation_refresh_decision_record.json",
    )


def test_v60b_outputs_preserve_loop_identity_and_exact_path(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60b_input_tree(tmp_path)

    refreshed_task_residual, refreshed_continuation_decision = run_agentic_de_continuation_v60b(
        repo_root_path=temp_root,
    )

    assert refreshed_task_residual.target_arc == "vNext+165"
    assert refreshed_task_residual.target_path == "V60-B"
    assert (
        refreshed_task_residual.prior_loop_identity_ref
        == refreshed_task_residual.prior_loop_state_ledger_ref
    )
    assert (
        refreshed_continuation_decision.stable_loop_identity_ref
        == refreshed_continuation_decision.prior_loop_state_ledger_ref
    )
    assert refreshed_continuation_decision.refresh_outcome == "continue_to_governed_act"
    assert (
        refreshed_continuation_decision.selected_next_path_summary_or_none
        == _expected_selected_path_summary()
    )
    assert refreshed_continuation_decision.reproposal_basis_summary_or_none is None
    assert "latest_reintegrated_act_selected_explicitly" in (
        refreshed_continuation_decision.refresh_reason_codes
    )


def test_latest_live_turn_selection_mismatch_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60b_input_tree(tmp_path / "repo")
    v60a_root = fixture_root.parent / "v60a"
    task_residual_path = v60a_root / "reference_agentic_de_task_residual_packet.json"
    payload = json.loads(task_residual_path.read_text(encoding="utf-8"))
    payload["latest_live_turn_reintegration_ref_or_none"] = (
        "agentic_de_live_turn_reintegration_report_wrong"
    )
    payload["residual_id"] = None
    task_residual_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    _reanchor_v60a_chain_after_residual_mutation(v60a_root)

    with pytest.raises(ValueError, match="latest live turn"):
        run_agentic_de_continuation_v60b(repo_root_path=temp_root)


def test_blocker_summary_yields_reproposal_required(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60b_input_tree(tmp_path / "repo")
    v60a_root = fixture_root.parent / "v60a"
    task_residual_path = v60a_root / "reference_agentic_de_task_residual_packet.json"
    payload = json.loads(task_residual_path.read_text(encoding="utf-8"))
    payload["blocker_summary"] = "current_frontier_requires_structured_reproposal"
    payload["residual_id"] = None
    task_residual_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    _reanchor_v60a_chain_after_residual_mutation(v60a_root)

    _refreshed_task_residual, refreshed_continuation_decision = run_agentic_de_continuation_v60b(
        repo_root_path=temp_root,
    )

    assert refreshed_continuation_decision.refresh_outcome == "reproposal_required"
    assert refreshed_continuation_decision.selected_next_path_summary_or_none is None
    assert refreshed_continuation_decision.reproposal_basis_summary_or_none is not None
