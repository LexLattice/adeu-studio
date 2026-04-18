from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_connector_bridge_hardening_v62c
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v62c"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v61b",
    "packages/adeu_agentic_de/tests/fixtures/v61c",
    "packages/adeu_agentic_de/tests/fixtures/v62a",
    "packages/adeu_agentic_de/tests/fixtures/v62b",
    "packages/adeu_agentic_de/tests/fixtures/v62c",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v170/evidence_inputs/v62a_connector_admission_evidence_v170.json",
    "artifacts/agent_harness/v171/evidence_inputs/v62b_external_assistant_egress_bridge_evidence_v171.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v62c_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v62c",
    )


def test_reference_output_matches_live_v62c_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62c_input_tree(tmp_path)

    register = run_agentic_de_connector_bridge_hardening_v62c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_connector_bridge_hardening_register.json",
    )


def test_v62c_output_remains_advisory_only_and_policy_anchored(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62c_input_tree(tmp_path)

    register = run_agentic_de_connector_bridge_hardening_v62c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+172"
    assert register.target_path == "V62-C"
    assert register.baseline_checker_version == "agentic_de_connector_bridge_hardening_v62c"
    assert register.advisory_only is True
    assert register.candidate_only is True
    assert register.path_level_only is True
    assert register.exemplar_evidence_non_generalizing_by_default is True
    assert register.changes_live_behavior_by_default is False
    assert register.committed_lane_artifacts_outrank_narrative_docs is True
    assert register.explicit_frozen_policy_anchor_required is True
    assert register.keep_warning_only_retains_current_advisory_posture_only is True
    assert register.positive_rewitness_carry_through_fails_closed is True
    entry = register.entries[0]
    assert (
        entry.selected_hardening_target_surface
        == "shipped_v62a_v62b_external_assistant_connector_lineage_over_continuity_bound_"
        "create_new_exemplar_only"
    )
    assert (
        entry.frozen_policy_ref
        == "docs/LOCKED_CONTINUATION_vNEXT_PLUS172.md#machine-checkable-contract"
    )
    assert entry.recommended_outcome == "candidate_for_later_connector_hardening"
    assert entry.connector_provider_class == "codex"
    assert entry.selected_connector_principal_class == "external_assistant"
    assert entry.selected_bridge_office_posture_or_none == "resident_bridge_bound"
    assert entry.selected_rewitness_outcome_or_none == "witness_candidate_promoted"
    assert entry.positive_rewitness_witness_basis_ref_or_none is not None
    assert entry.positive_rewitness_certificate_ref_or_none is None
    assert len(entry.root_origin_ids) == len(set(entry.root_origin_ids))
    assert "non-independent connector-hardening support" in entry.root_origin_dedup_summary


def test_v62c_recommendation_is_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62c_input_tree(tmp_path)

    first = run_agentic_de_connector_bridge_hardening_v62c(repo_root_path=temp_root)
    second = run_agentic_de_connector_bridge_hardening_v62c(repo_root_path=temp_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_missing_required_v62c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v62c_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V62-C lane drift record does not satisfy"):
        run_agentic_de_connector_bridge_hardening_v62c(repo_root_path=temp_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62c_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v62c"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_connector_bridge_hardening_v62c(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )


def test_v62c_rejects_mismatched_v61c_positive_rewitness_basis(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v62c_input_tree(tmp_path / "repo")
    register_path = (
        fixture_root.parent
        / "v61c"
        / "reference_agentic_de_governed_communication_hardening_register.json"
    )
    payload = _load_json(
        fixture_root.parent / "v61c",
        "reference_agentic_de_governed_communication_hardening_register.json",
    )
    assert isinstance(payload, dict)
    payload["entries"][0]["positive_rewitness_witness_basis_ref_or_none"] = "wrong-basis"
    payload["entries"][0]["hardening_id"] = None
    payload["register_id"] = None
    register_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V62-C requires the shipped V61-C positive rewitness witness-basis carry-through",
    ):
        run_agentic_de_connector_bridge_hardening_v62c(repo_root_path=temp_root)


def test_v62c_rejects_mismatched_v62b_rewitness_lineage(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v62c_input_tree(tmp_path / "repo")
    egress_path = (
        fixture_root.parent
        / "v62b"
        / "reference_agentic_de_external_assistant_egress_bridge_packet.json"
    )
    payload = _load_json(
        fixture_root.parent / "v62b",
        "reference_agentic_de_external_assistant_egress_bridge_packet.json",
    )
    assert isinstance(payload, dict)
    payload["consumed_message_rewitness_gate_ref_or_none"] = (
        "agentic_de_message_rewitness_gate_wrong"
    )
    payload["egress_bridge_packet_id"] = None
    egress_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V62-C egress bridge must bind the shipped V61-B rewitness gate",
    ):
        run_agentic_de_connector_bridge_hardening_v62c(repo_root_path=temp_root)


def test_v62c_rejects_symlinked_repo_root(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62c_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    with pytest.raises(ValueError, match="repository root may not be a symlink"):
        run_agentic_de_connector_bridge_hardening_v62c(repo_root_path=symlink_root)
