from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_remote_operator_control_bridge_v63b
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v63b"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v63a",
    "packages/adeu_agentic_de/tests/fixtures/v63b",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v173/evidence_inputs/v63a_remote_operator_starter_evidence_v173.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v63b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v63b",
    )


def test_reference_output_matches_live_v63b_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63b_input_tree(tmp_path)

    bridge_packet = run_agentic_de_remote_operator_control_bridge_v63b(repo_root_path=temp_root)

    assert bridge_packet.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_remote_operator_control_bridge_packet.json",
    )


def test_v63b_output_remains_bounded_richer_bridge_only(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63b_input_tree(tmp_path)

    bridge_packet = run_agentic_de_remote_operator_control_bridge_v63b(repo_root_path=temp_root)

    assert bridge_packet.target_arc == "vNext+174"
    assert bridge_packet.target_path == "V63-B"
    assert bridge_packet.selected_intervention_kind == "structured_answer"
    assert bridge_packet.consumed_remote_view_ref_or_equivalent.startswith(
        "agentic_de_remote_operator_view_"
    )
    assert bridge_packet.consumed_control_basis_ref_or_equivalent.startswith(
        "agentic_de_ingress_interpretation_"
    )
    assert "does not, by itself, mutate charter" in bridge_packet.intervention_basis_summary


def test_v63b_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63b_input_tree(tmp_path)

    first = run_agentic_de_remote_operator_control_bridge_v63b(repo_root_path=temp_root)
    second = run_agentic_de_remote_operator_control_bridge_v63b(repo_root_path=temp_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_v63b_accepts_explicit_inspect_rich_kind(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63b_input_tree(tmp_path)

    bridge_packet = run_agentic_de_remote_operator_control_bridge_v63b(
        repo_root_path=temp_root,
        selected_intervention_kind="inspect_rich",
    )

    assert bridge_packet.selected_intervention_kind == "inspect_rich"
    assert bridge_packet.consumed_control_basis_ref_or_equivalent.startswith(
        "agentic_de_continuation_refresh_decision_"
    )
    assert "loop/evidence context only" in bridge_packet.intervention_basis_summary


def test_v63b_rejects_unsupported_intervention_kind(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63b_input_tree(tmp_path / "repo")

    with pytest.raises(ValueError, match="selected_intervention_kind"):
        run_agentic_de_remote_operator_control_bridge_v63b(
            repo_root_path=temp_root,
            selected_intervention_kind="file_edit",
        )


def test_v63b_rejects_view_bound_to_wrong_remote_session(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v63b_input_tree(tmp_path / "repo")
    view_path = (
        fixture_root.parent / "v63a" / "reference_agentic_de_remote_operator_view_packet.json"
    )
    payload = _load_json(
        fixture_root.parent / "v63a", "reference_agentic_de_remote_operator_view_packet.json"
    )
    assert isinstance(payload, dict)
    payload["remote_operator_session_ref"] = "agentic_de_remote_operator_session_wrong"
    payload["remote_operator_view_id"] = None
    view_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V63-B remote view must bind the shipped V63-A remote session",
    ):
        run_agentic_de_remote_operator_control_bridge_v63b(repo_root_path=temp_root)


def test_v63b_rejects_premature_repo_or_execute_selection_in_v63a_evidence(
    tmp_path: Path,
) -> None:
    temp_root, _fixture_root = _copy_v63b_input_tree(tmp_path / "repo")
    evidence_path = (
        temp_root
        / "artifacts"
        / "agent_harness"
        / "v173"
        / "evidence_inputs"
        / "v63a_remote_operator_starter_evidence_v173.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload["repo_or_execute_authority_selected_for_v63a"] = True
    evidence_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V63-A evidence must preserve repo/execute deferral"):
        run_agentic_de_remote_operator_control_bridge_v63b(repo_root_path=temp_root)


def test_v63b_rejects_symlinked_repo_root(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63b_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    with pytest.raises(ValueError, match="repository root may not be a symlink"):
        run_agentic_de_remote_operator_control_bridge_v63b(repo_root_path=symlink_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63b_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v63b"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_remote_operator_control_bridge_v63b(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )
