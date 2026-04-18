from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_remote_operator_hardening_v63c
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v63c"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v63a",
    "packages/adeu_agentic_de/tests/fixtures/v63b",
    "packages/adeu_agentic_de/tests/fixtures/v63c",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v173/evidence_inputs/v63a_remote_operator_starter_evidence_v173.json",
    "artifacts/agent_harness/v174/evidence_inputs/v63b_remote_operator_control_bridge_evidence_v174.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v63c_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v63c",
    )


def test_reference_output_matches_live_v63c_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63c_input_tree(tmp_path)

    register = run_agentic_de_remote_operator_hardening_v63c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_remote_operator_hardening_register.json",
    )


def test_v63c_output_remains_advisory_only_and_policy_anchored(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63c_input_tree(tmp_path)

    register = run_agentic_de_remote_operator_hardening_v63c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+175"
    assert register.target_path == "V63-C"
    assert register.baseline_checker_version == "agentic_de_remote_operator_hardening_v63c"
    assert register.advisory_only is True
    assert register.candidate_only is True
    assert register.path_level_only is True
    assert register.exemplar_evidence_non_generalizing_by_default is True
    assert register.changes_live_behavior_by_default is False
    assert register.committed_lane_artifacts_outrank_narrative_docs is True
    assert register.evidence_basis_distinct_from_recommendation is True
    assert register.recommendation_function_extensional_and_replayable is True
    assert register.explicit_frozen_policy_anchor_required is True
    assert register.keep_warning_only_retains_current_advisory_posture_only is True
    assert register.optional_upstream_basis_consistency_fails_closed is True
    entry = register.entries[0]
    assert (
        entry.selected_hardening_target_surface
        == "shipped_v63a_v63b_remote_operator_lineage_over_one_admitted_remote_operator_path_only"
    )
    assert (
        entry.frozen_policy_ref
        == "docs/LOCKED_CONTINUATION_vNEXT_PLUS175.md#machine-checkable-contract"
    )
    assert entry.recommended_outcome == "candidate_for_later_remote_operator_hardening"
    assert entry.selected_remote_principal_class == "remote_operator"
    assert entry.remote_session_admission_verdict == "admitted"
    assert entry.selected_remote_surface_class == "read_mostly_phone_safe_remote_operator_surface"
    assert entry.remote_operator_response_ref_or_none is not None
    assert entry.remote_operator_control_bridge_ref_or_none is not None
    assert entry.selected_response_or_control_kind_summary_or_none is not None
    assert len(entry.root_origin_ids) == len(set(entry.root_origin_ids))
    assert "non-independent remote-hardening support" in entry.root_origin_dedup_summary


def test_v63c_recommendation_is_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63c_input_tree(tmp_path)

    first = run_agentic_de_remote_operator_hardening_v63c(repo_root_path=temp_root)
    second = run_agentic_de_remote_operator_hardening_v63c(repo_root_path=temp_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_missing_required_v63c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v63c_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V63-C lane drift record does not satisfy"):
        run_agentic_de_remote_operator_hardening_v63c(repo_root_path=temp_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63c_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v63c"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_remote_operator_hardening_v63c(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )


def test_v63c_keep_warning_only_when_optional_upstream_basis_absent(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63c_input_tree(tmp_path / "repo")

    register = run_agentic_de_remote_operator_hardening_v63c(
        repo_root_path=temp_root,
        v63a_remote_operator_response_path=None,
        v63b_remote_operator_control_bridge_path=None,
    )

    entry = register.entries[0]
    assert entry.recommended_outcome == "keep_warning_only"
    assert entry.selected_response_or_control_kind_summary_or_none is None
    assert entry.remote_operator_response_ref_or_none is None
    assert entry.remote_operator_control_bridge_ref_or_none is None


def test_v63c_rejects_mismatched_v63a_response_session(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v63c_input_tree(tmp_path / "repo")
    response_path = (
        fixture_root.parent / "v63a" / "reference_agentic_de_remote_operator_response_record.json"
    )
    payload = _load_json(
        fixture_root.parent / "v63a", "reference_agentic_de_remote_operator_response_record.json"
    )
    assert isinstance(payload, dict)
    payload["remote_operator_session_ref"] = "agentic_de_remote_operator_session_wrong"
    payload["remote_operator_response_id"] = None
    response_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V63-C remote response must bind the shipped V63-A remote session",
    ):
        run_agentic_de_remote_operator_hardening_v63c(repo_root_path=temp_root)


def test_v63c_rejects_mismatched_v63b_control_bridge_view(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v63c_input_tree(tmp_path / "repo")
    bridge_path = (
        fixture_root.parent
        / "v63b"
        / "reference_agentic_de_remote_operator_control_bridge_packet.json"
    )
    payload = _load_json(
        fixture_root.parent / "v63b",
        "reference_agentic_de_remote_operator_control_bridge_packet.json",
    )
    assert isinstance(payload, dict)
    payload["consumed_remote_view_ref_or_equivalent"] = "agentic_de_remote_operator_view_wrong"
    payload["remote_operator_control_bridge_id"] = None
    bridge_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V63-C control bridge must bind the shipped V63-A remote view",
    ):
        run_agentic_de_remote_operator_hardening_v63c(repo_root_path=temp_root)


def test_v63c_rejects_non_shipped_v63b_evidence_drift(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63c_input_tree(tmp_path / "repo")
    evidence_path = (
        temp_root
        / "artifacts"
        / "agent_harness"
        / "v174"
        / "evidence_inputs"
        / "v63b_remote_operator_control_bridge_evidence_v174.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload[
        "selected_bridge_path_may_not_generalize_by_default_into_all_device_or_all_surface_law"
    ] = False
    evidence_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V63-B evidence must preserve all-device/all-surface non-generalization",
    ):
        run_agentic_de_remote_operator_hardening_v63c(repo_root_path=temp_root)


def test_v63c_rejects_symlinked_repo_root(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63c_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    with pytest.raises(ValueError, match="repository root may not be a symlink"):
        run_agentic_de_remote_operator_hardening_v63c(repo_root_path=symlink_root)
