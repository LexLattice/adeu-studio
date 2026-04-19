from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_repo_write_restoration_v64b
from adeu_agentic_de.workspace_continuity import DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v64b"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v64a",
    "packages/adeu_agentic_de/tests/fixtures/v64b",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v176/evidence_inputs/v64a_repo_writable_surface_starter_evidence_v176.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _seed_prior_governed_target_state(temp_root: Path) -> None:
    observation_payload = _load_json(
        _repo_root_path() / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v59a",
        "reference_agentic_de_local_effect_observation_record.json",
    )
    assert isinstance(observation_payload, dict)
    observed_write_set = observation_payload["observed_write_set"]
    assert isinstance(observed_write_set, list) and len(observed_write_set) == 1
    observed_entry = observed_write_set[0]
    assert isinstance(observed_entry, dict)
    target_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "runtime"
        / "reference_patch_candidate.diff"
    )
    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text(DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT, encoding="utf-8")
    marker_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "_observer"
        / "reference_governed_target_lineage.json"
    )
    marker_path.parent.mkdir(parents=True, exist_ok=True)
    marker_payload = {
        "target_relative_path": "runtime/reference_patch_candidate.diff",
        "governed_observation_ref": observation_payload["observation_id"],
        "target_content_sha256": observed_entry["content_sha256"],
    }
    marker_path.write_text(json.dumps(marker_payload, indent=2) + "\n", encoding="utf-8")


def _copy_v64b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
    _seed_prior_governed_target_state(tmp_path)
    return (
        tmp_path,
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v64b",
    )


def test_reference_outputs_match_live_v64b_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64b_input_tree(tmp_path)

    restoration, reintegration = run_agentic_de_repo_write_restoration_v64b(
        repo_root_path=temp_root
    )

    assert restoration.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_repo_write_restoration_record.json",
    )
    assert reintegration.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_repo_write_reintegration_report.json",
    )


def test_v64b_outputs_remain_bounded_restoration_only(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64b_input_tree(tmp_path)
    target_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "runtime"
        / "reference_patch_candidate.diff"
    )

    restoration, reintegration = run_agentic_de_repo_write_restoration_v64b(
        repo_root_path=temp_root
    )

    assert restoration.target_arc == "vNext+177"
    assert restoration.target_path == "V64-B"
    assert restoration.restoration_status == "restored"
    assert "not become fresh target admission" in (
        restoration.target_occupancy_or_admissibility_basis_summary
    )
    assert reintegration.reintegration_status == "reintegrated"
    assert not target_path.exists()


def test_v64b_replayable_for_same_seeded_inputs(tmp_path: Path) -> None:
    first_root, _fixture_root = _copy_v64b_input_tree(tmp_path / "first")
    second_root, _fixture_root = _copy_v64b_input_tree(tmp_path / "second")

    first = run_agentic_de_repo_write_restoration_v64b(repo_root_path=first_root)
    second = run_agentic_de_repo_write_restoration_v64b(repo_root_path=second_root)

    assert [item.model_dump(mode="json") for item in first] == [
        item.model_dump(mode="json") for item in second
    ]


def test_v64b_accepts_equivalent_normalized_target_relative_path(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64b_input_tree(tmp_path)

    restoration, reintegration = run_agentic_de_repo_write_restoration_v64b(
        repo_root_path=temp_root,
        target_relative_path=" runtime//reference_patch_candidate.diff ",
    )

    assert restoration.selected_target_path_summary.endswith(
        "runtime/reference_patch_candidate.diff"
    )
    assert reintegration.repo_write_restoration_ref == restoration.repo_write_restoration_id


def test_v64b_rejects_mismatched_v64a_target_admission(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64b_input_tree(tmp_path / "repo")
    admission_path = (
        fixture_root.parent
        / "v64a"
        / "reference_agentic_de_repo_write_surface_admission_record.json"
    )
    payload = _load_json(
        fixture_root.parent / "v64a",
        "reference_agentic_de_repo_write_surface_admission_record.json",
    )
    assert isinstance(payload, dict)
    payload["selected_target_path_summary"] = (
        "artifacts/agentic_de/v59/workspace_continuity/runtime/other_target.diff"
    )
    payload["repo_write_surface_admission_id"] = None
    admission_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped exact V64-A admitted target path"):
        run_agentic_de_repo_write_restoration_v64b(repo_root_path=temp_root)


def test_v64b_rejects_mismatched_v59a_conformance_basis(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64b_input_tree(tmp_path / "repo")
    conformance_path = (
        fixture_root.parent / "v59a" / "reference_agentic_de_local_effect_conformance_report.json"
    )
    payload = _load_json(
        fixture_root.parent / "v59a",
        "reference_agentic_de_local_effect_conformance_report.json",
    )
    assert isinstance(payload, dict)
    payload["observation_ref"] = "agentic_de_local_effect_observation_wrong"
    payload["report_id"] = None
    conformance_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="conformance must bind the shipped V59-A observation"):
        run_agentic_de_repo_write_restoration_v64b(repo_root_path=temp_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64b_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v64b"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_repo_write_restoration_v64b(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )


def test_v64b_rejects_symlinked_repo_root(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64b_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    with pytest.raises(ValueError, match="repository root may not be a symlink"):
        run_agentic_de_repo_write_restoration_v64b(repo_root_path=symlink_root)
