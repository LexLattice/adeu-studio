from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_repo_writable_surface_v64a
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v64a"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v64a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v163/evidence_inputs/v59c_workspace_continuity_hardening_evidence_v163.json",
    "artifacts/agent_harness/v166/evidence_inputs/v60c_continuation_hardening_evidence_v166.json",
    "artifacts/agent_harness/v169/evidence_inputs/v61c_governed_communication_hardening_evidence_v169.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v64a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v64a",
    )


def test_reference_outputs_match_live_v64a_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64a_input_tree(tmp_path)

    descriptor, lease, admission = run_agentic_de_repo_writable_surface_v64a(
        repo_root_path=temp_root
    )

    assert descriptor.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_repo_writable_surface_descriptor.json",
    )
    assert lease.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_repo_write_lease_record.json",
    )
    assert admission.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_repo_write_surface_admission_record.json",
    )


def test_v64a_outputs_remain_bounded_surface_only(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64a_input_tree(tmp_path)

    descriptor, lease, admission = run_agentic_de_repo_writable_surface_v64a(
        repo_root_path=temp_root
    )

    assert descriptor.target_arc == "vNext+176"
    assert descriptor.target_path == "V64-A"
    assert descriptor.selected_surface_class == "declared_subtree"
    assert descriptor.selected_surface_identity_summary.endswith("/runtime/")
    assert lease.lease_verdict == "admitted"
    assert "continuity state is not writable entitlement" in lease.consumed_continuity_basis_summary
    assert "not the lease or writable authority" in (
        lease.consumed_communication_basis_summary_or_none or ""
    )
    assert admission.admission_verdict == "admitted"
    assert admission.selected_target_path_summary.endswith("runtime/reference_patch_candidate.diff")
    assert "lease alone is not blanket entitlement" in (
        admission.target_occupancy_or_admissibility_basis_summary
    )


def test_v64a_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64a_input_tree(tmp_path)

    first = run_agentic_de_repo_writable_surface_v64a(repo_root_path=temp_root)
    second = run_agentic_de_repo_writable_surface_v64a(repo_root_path=temp_root)

    assert [item.model_dump(mode="json") for item in first] == [
        item.model_dump(mode="json") for item in second
    ]


def test_v64a_normalizes_equivalent_target_relative_path_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64a_input_tree(tmp_path)

    descriptor, lease, admission = run_agentic_de_repo_writable_surface_v64a(
        repo_root_path=temp_root,
        target_relative_path=" runtime//reference_patch_candidate.diff ",
    )

    assert descriptor.selected_surface_identity_summary.endswith("/runtime/")
    assert lease.writable_surface_descriptor_ref == descriptor.repo_writable_surface_descriptor_id
    assert admission.selected_target_path_summary.endswith("runtime/reference_patch_candidate.diff")


def test_v64a_rejects_non_unoccupied_target_basis(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64a_input_tree(tmp_path / "repo")
    occupancy_path = (
        fixture_root.parent / "v59a" / "reference_agentic_de_workspace_occupancy_report.json"
    )
    payload = _load_json(
        fixture_root.parent / "v59a",
        "reference_agentic_de_workspace_occupancy_report.json",
    )
    assert isinstance(payload, dict)
    payload["occupancy_verdict"] = "occupied_out_of_band"
    payload["occupancy_report_id"] = None
    occupancy_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="per-target unoccupied admissibility"):
        run_agentic_de_repo_writable_surface_v64a(repo_root_path=temp_root)


def test_v64a_rejects_wrong_v60_write_posture_even_with_v61_lineage_present(
    tmp_path: Path,
) -> None:
    temp_root, fixture_root = _copy_v64a_input_tree(tmp_path / "repo")
    refresh_path = (
        fixture_root.parent
        / "v60b"
        / "reference_agentic_de_continuation_refresh_decision_record.json"
    )
    payload = _load_json(
        fixture_root.parent / "v60b",
        "reference_agentic_de_continuation_refresh_decision_record.json",
    )
    assert isinstance(payload, dict)
    payload["selected_next_path_summary_or_none"] = (
        "urm_copilot_session_path::local_write/create_new::"
        "artifacts/agentic_de/v59/workspace_continuity/runtime/other_target.diff"
    )
    payload["refresh_decision_id"] = None
    refresh_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped exact V60 selected downstream path"):
        run_agentic_de_repo_writable_surface_v64a(repo_root_path=temp_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64a_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v64a"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_repo_writable_surface_v64a(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )


def test_v64a_rejects_symlinked_repo_root(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64a_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    with pytest.raises(ValueError, match="repository root may not be a symlink"):
        run_agentic_de_repo_writable_surface_v64a(repo_root_path=symlink_root)
