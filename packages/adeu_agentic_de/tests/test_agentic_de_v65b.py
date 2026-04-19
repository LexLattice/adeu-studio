from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_delegated_worker_reconciliation_v65b
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v65b"

FIXTURE_DIRS = (
    "packages/adeu_agent_harness/tests/fixtures/v48e",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v65a",
    "packages/adeu_agentic_de/tests/fixtures/v65b",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v115/evidence_inputs/v48d_worker_boundary_conformance_evidence_v115.json",
    "artifacts/agent_harness/v116/evidence_inputs/v48e_worker_delegation_topology_evidence_v116.json",
    "artifacts/agent_harness/v179/evidence_inputs/v65a_delegated_worker_export_starter_evidence_v179.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v65b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v65b",
    )


def test_reference_output_matches_live_v65b_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65b_input_tree(tmp_path)

    report = run_agentic_de_delegated_worker_reconciliation_v65b(repo_root_path=temp_root)

    assert report.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_delegated_worker_reconciliation_report.json",
    )


def test_v65b_output_remains_reconciliation_only(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65b_input_tree(tmp_path)

    report = run_agentic_de_delegated_worker_reconciliation_v65b(repo_root_path=temp_root)

    assert report.target_arc == "vNext+180"
    assert report.target_path == "V65-B"
    assert report.reconciliation_status == "reconciled_to_export_lineage"
    assert report.selected_target_or_patch_or_artifact_summary.endswith(
        "runtime/reference_patch_candidate.diff"
    )
    assert report.worker_carrier_basis_ref_or_equivalent.endswith(
        "reference_child/compiled_policy_taskpack_binding.json"
    )
    assert report.selected_worker_result_or_conformance_kind_summary.startswith(
        "worker_result_or_conformance_kind=boundary_conformance_report"
    )
    assert "local_write/create_new" in report.preserved_write_semantics_summary


def test_v65b_replayable_for_same_inputs(tmp_path: Path) -> None:
    first_root, _fixture_root = _copy_v65b_input_tree(tmp_path / "first")
    second_root, _fixture_root = _copy_v65b_input_tree(tmp_path / "second")

    first = run_agentic_de_delegated_worker_reconciliation_v65b(repo_root_path=first_root)
    second = run_agentic_de_delegated_worker_reconciliation_v65b(repo_root_path=second_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_invalid_v65b_lane_drift_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v65b_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V65-B lane drift record does not satisfy"):
        run_agentic_de_delegated_worker_reconciliation_v65b(repo_root_path=temp_root)


def test_v65b_rejects_worker_result_basis_mismatch(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65b_input_tree(tmp_path / "repo")
    report_path = (
        temp_root
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48e"
        / "reference_child"
        / "worker_boundary_conformance_report.json"
    )
    payload = json.loads(report_path.read_text(encoding="utf-8"))
    payload["compiled_binding_ref"] = "artifacts/agent_harness/v48e/mutated_child_binding.json"
    payload["semantic_hash"] = "mutated"
    report_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="selected worker carrier"):
        run_agentic_de_delegated_worker_reconciliation_v65b(repo_root_path=temp_root)


def test_v65b_rejects_alternate_worker_result_input_path(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65b_input_tree(tmp_path / "repo")
    original_path = (
        temp_root
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48e"
        / "reference_child"
        / "worker_boundary_conformance_report.json"
    )
    alternate_path = (
        temp_root
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48e"
        / "reference_child"
        / "worker_boundary_conformance_report_copy.json"
    )
    shutil.copyfile(original_path, alternate_path)

    with pytest.raises(
        ValueError,
        match="current selected released-worker input path",
    ):
        run_agentic_de_delegated_worker_reconciliation_v65b(
            repo_root_path=temp_root,
            worker_boundary_conformance_path=alternate_path,
        )


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65b_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v65b"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_delegated_worker_reconciliation_v65b(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )
