from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_governed_communication_v61c
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v61c"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v61b",
    "packages/adeu_agentic_de/tests/fixtures/v61c",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v167/evidence_inputs/v61a_governed_communication_evidence_v167.json",
    "artifacts/agent_harness/v168/evidence_inputs/v61b_bridge_office_rewitness_evidence_v168.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v61c_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v61c",
    )


def test_reference_outputs_match_live_v61c_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61c_input_tree(tmp_path)

    register = run_agentic_de_governed_communication_v61c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_governed_communication_hardening_register.json",
    )


def test_v61c_output_remains_advisory_only_path_level_and_policy_anchored(
    tmp_path: Path,
) -> None:
    temp_root, _fixture_root = _copy_v61c_input_tree(tmp_path)

    register = run_agentic_de_governed_communication_v61c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+169"
    assert register.target_path == "V61-C"
    assert register.baseline_checker_version == "agentic_de_governed_communication_v61c"
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
        == "shipped_v61a_v61b_governed_communication_lineage_over_continuity_bound_"
        "create_new_exemplar_only"
    )
    assert (
        entry.frozen_policy_ref
        == "docs/LOCKED_CONTINUATION_vNEXT_PLUS169.md#machine-checkable-contract"
    )
    assert entry.recommended_outcome == "candidate_for_later_communication_hardening"
    assert entry.selected_bridge_office_posture == "resident_bridge_bound"
    assert entry.rewitness_outcome == "witness_candidate_promoted"
    assert entry.positive_rewitness_witness_basis_ref_or_none is not None
    assert entry.positive_rewitness_certificate_ref_or_none is None
    assert len(entry.root_origin_ids) == len(set(entry.root_origin_ids))
    assert "non-independent advisory support" in entry.root_origin_dedup_summary


def test_v61c_recommendation_is_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61c_input_tree(tmp_path)

    first = run_agentic_de_governed_communication_v61c(repo_root_path=temp_root)
    second = run_agentic_de_governed_communication_v61c(repo_root_path=temp_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_missing_required_v61c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61c_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V61-C lane drift record does not satisfy"):
        run_agentic_de_governed_communication_v61c(repo_root_path=temp_root)


def test_non_v61b_rewitness_surface_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61c_input_tree(tmp_path / "repo")
    rewitness_path = (
        fixture_root.parent / "v61b" / "reference_agentic_de_message_rewitness_gate_record.json"
    )
    payload = json.loads(rewitness_path.read_text(encoding="utf-8"))
    payload["target_arc"] = "vNext+999"
    payload["message_rewitness_gate_id"] = None
    rewitness_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped V61-B message rewitness gate surface"):
        run_agentic_de_governed_communication_v61c(repo_root_path=temp_root)


def test_positive_rewitness_basis_is_required_for_v61c(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61c_input_tree(tmp_path / "repo")
    rewitness_path = (
        fixture_root.parent / "v61b" / "reference_agentic_de_message_rewitness_gate_record.json"
    )
    payload = json.loads(rewitness_path.read_text(encoding="utf-8"))
    payload["witness_basis_ref_or_none"] = None
    payload["certificate_ref_or_none"] = None
    payload["message_rewitness_gate_id"] = None
    rewitness_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="witness_basis_ref_or_none or certificate_ref_or_none",
    ):
        run_agentic_de_governed_communication_v61c(repo_root_path=temp_root)


def test_v61c_rejects_non_shipped_v61b_policy_anchor(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61c_input_tree(tmp_path / "repo")
    bridge_binding_path = (
        fixture_root.parent / "v61b" / "reference_agentic_de_bridge_office_binding_record.json"
    )
    payload = json.loads(bridge_binding_path.read_text(encoding="utf-8"))
    payload["frozen_policy_anchor_ref"] = "docs/LOCKED_CONTINUATION_vNEXT_PLUS999.md#other"
    payload["bridge_office_binding_id"] = None
    bridge_binding_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="bridge binding policy anchor"):
        run_agentic_de_governed_communication_v61c(repo_root_path=temp_root)


def test_v61c_rejects_symlinked_repo_root(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61c_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    with pytest.raises(ValueError, match="repository root may not be a symlink"):
        run_agentic_de_governed_communication_v61c(repo_root_path=symlink_root)
