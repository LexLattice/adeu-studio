from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_continuation_v60c
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v60c"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v56a",
    "packages/adeu_agentic_de/tests/fixtures/v56b",
    "packages/adeu_agentic_de/tests/fixtures/v56c",
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v59b",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v60c",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v161/evidence_inputs/v59a_workspace_continuity_starter_evidence_v161.json",
    "artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json",
    "artifacts/agent_harness/v164/evidence_inputs/v60a_continuation_starter_evidence_v164.json",
    "artifacts/agent_harness/v165/evidence_inputs/v60b_continuation_refresh_evidence_v165.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v60c_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v60c",
    )


def test_reference_outputs_match_live_v60c_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60c_input_tree(tmp_path)

    register = run_agentic_de_continuation_v60c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_continuation_hardening_register.json",
    )


def test_v60c_output_remains_advisory_only_path_level_and_policy_anchored(
    tmp_path: Path,
) -> None:
    temp_root, _fixture_root = _copy_v60c_input_tree(tmp_path)

    register = run_agentic_de_continuation_v60c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+166"
    assert register.target_path == "V60-C"
    assert register.advisory_only is True
    assert register.candidate_only is True
    assert register.path_level_only is True
    assert register.exemplar_evidence_non_generalizing_by_default is True
    assert register.changes_live_behavior_by_default is False
    assert register.recommendation_function_extensional_and_replayable is True
    assert register.explicit_frozen_policy_anchor_required is True
    assert register.lineage_root_non_independence_dedup_applied is True
    entry = register.entries[0]
    assert (
        entry.selected_hardening_target_surface
        == "shipped_v60a_v60b_continuation_lineage_over_continuity_bound_create_new_exemplar_only"
    )
    assert (
        entry.frozen_policy_ref
        == "docs/LOCKED_CONTINUATION_vNEXT_PLUS166.md#machine-checkable-contract"
    )
    assert entry.recommended_outcome == "candidate_for_later_continuation_hardening"
    assert entry.starter_continuation_outcome == "continue_to_governed_act"
    assert entry.refresh_outcome == "continue_to_governed_act"
    assert entry.selected_next_path_summary_or_none is not None
    assert entry.reproposal_basis_summary_or_none is None
    assert len(entry.root_origin_ids) == len(set(entry.root_origin_ids))
    assert "non-independent advisory support" in entry.root_origin_dedup_summary


def test_v60c_recommendation_is_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60c_input_tree(tmp_path)

    first = run_agentic_de_continuation_v60c(repo_root_path=temp_root)
    second = run_agentic_de_continuation_v60c(repo_root_path=temp_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_missing_required_v60c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60c_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V60-C lane drift record does not satisfy"):
        run_agentic_de_continuation_v60c(repo_root_path=temp_root)


def test_non_v60b_refresh_surface_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60c_input_tree(tmp_path / "repo")
    refresh_decision_path = (
        fixture_root.parent
        / "v60b"
        / "reference_agentic_de_continuation_refresh_decision_record.json"
    )
    payload = json.loads(refresh_decision_path.read_text(encoding="utf-8"))
    payload["target_arc"] = "vNext+999"
    payload["refresh_decision_id"] = None
    refresh_decision_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped V60-B continuation refresh decision surface"):
        run_agentic_de_continuation_v60c(repo_root_path=temp_root)


def test_v60c_rejects_broadened_selected_path_dependence_tags(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60c_input_tree(tmp_path / "repo")
    refresh_decision_path = (
        fixture_root.parent
        / "v60b"
        / "reference_agentic_de_continuation_refresh_decision_record.json"
    )
    payload = json.loads(refresh_decision_path.read_text(encoding="utf-8"))
    payload["field_dependence_tags"]["selected_next_path_summary_or_none"].append(
        "extra:ambient_ref"
    )
    payload["refresh_decision_id"] = None
    refresh_decision_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="selected-next-path dependence tags"):
        run_agentic_de_continuation_v60c(repo_root_path=temp_root)


def test_v60c_rejects_extra_v60b_refresh_reason_codes(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60c_input_tree(tmp_path / "repo")
    refresh_decision_path = (
        fixture_root.parent
        / "v60b"
        / "reference_agentic_de_continuation_refresh_decision_record.json"
    )
    payload = json.loads(refresh_decision_path.read_text(encoding="utf-8"))
    payload["refresh_reason_codes"].append("extra:ambient_escalation_semantics")
    payload["refresh_decision_id"] = None
    refresh_decision_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped reason codes"):
        run_agentic_de_continuation_v60c(repo_root_path=temp_root)


def test_v60c_rejects_symlinked_repo_root(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60c_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    with pytest.raises(ValueError, match="repository root may not be a symlink"):
        run_agentic_de_continuation_v60c(repo_root_path=symlink_root)
