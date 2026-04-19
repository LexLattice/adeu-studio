from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_delegated_worker_export_v65a
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v65a"

FIXTURE_DIRS = (
    "packages/adeu_agent_harness/tests/fixtures/v48e",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v64a",
    "packages/adeu_agentic_de/tests/fixtures/v64c",
    "packages/adeu_agentic_de/tests/fixtures/v65a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v116/evidence_inputs/v48e_worker_delegation_topology_evidence_v116.json",
    "artifacts/agent_harness/v178/evidence_inputs/v64c_repo_writable_surface_hardening_evidence_v178.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v65a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v65a",
    )


def test_reference_output_matches_live_v65a_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65a_input_tree(tmp_path)

    packet = run_agentic_de_delegated_worker_export_v65a(repo_root_path=temp_root)

    assert packet.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_delegated_worker_export_packet.json",
    )


def test_v65a_output_remains_export_bridge_only(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65a_input_tree(tmp_path)

    packet = run_agentic_de_delegated_worker_export_v65a(repo_root_path=temp_root)

    assert packet.target_arc == "vNext+179"
    assert packet.target_path == "V65-A"
    assert packet.export_verdict == "admitted_for_export"
    assert packet.selected_target_or_patch_or_artifact_summary.endswith(
        "runtime/reference_patch_candidate.diff"
    )
    assert packet.worker_carrier_basis_ref_or_equivalent.endswith(
        "reference_child/compiled_policy_taskpack_binding.json"
    )
    assert packet.selected_worker_topology_basis_ref_or_equivalent.startswith(
        "worker_delegation_topology:"
    )
    assert "local_write/create_new" in packet.preserved_write_semantics_summary
    assert "does not mint export authority" in (
        packet.consumed_communication_basis_summary_or_none or ""
    )


def test_v65a_replayable_for_same_inputs(tmp_path: Path) -> None:
    first_root, _fixture_root = _copy_v65a_input_tree(tmp_path / "first")
    second_root, _fixture_root = _copy_v65a_input_tree(tmp_path / "second")

    first = run_agentic_de_delegated_worker_export_v65a(repo_root_path=first_root)
    second = run_agentic_de_delegated_worker_export_v65a(repo_root_path=second_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_invalid_v65a_lane_drift_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v65a_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V65-A lane drift record does not satisfy"):
        run_agentic_de_delegated_worker_export_v65a(repo_root_path=temp_root)


def test_v65a_rejects_non_completed_worker_topology(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v65a_input_tree(tmp_path / "repo")
    topology_path = (
        temp_root
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48e"
        / "reference_worker_delegation_topology.json"
    )
    payload = json.loads(topology_path.read_text(encoding="utf-8"))
    payload["handoff_result"] = "incomplete_lineage"
    payload["worker_delegation_topology_id"] = "worker_delegation_topology:mutated"
    payload["semantic_hash"] = "mutated"
    topology_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="released completed V48-E worker topology"):
        run_agentic_de_delegated_worker_export_v65a(repo_root_path=temp_root)


def test_v65a_rejects_topology_lineage_mismatch(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65a_input_tree(tmp_path / "repo")
    topology_path = (
        temp_root
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48e"
        / "reference_worker_delegation_topology.json"
    )
    payload = json.loads(topology_path.read_text(encoding="utf-8"))
    payload["child_compiled_binding_ref"] = "artifacts/agent_harness/v48e/mutated_child.json"
    payload["semantic_hash"] = "mutated-lineage"
    topology_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="released exact V48-E child compiled binding"):
        run_agentic_de_delegated_worker_export_v65a(repo_root_path=temp_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65a_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v65a"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_delegated_worker_export_v65a(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )
