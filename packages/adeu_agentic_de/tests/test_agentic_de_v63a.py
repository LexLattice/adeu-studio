from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_remote_operator_starter_v63a
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v63a"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v63a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v169/evidence_inputs/v61c_governed_communication_hardening_evidence_v169.json",
    "artifacts/agent_harness/v172/evidence_inputs/v62c_connector_bridge_hardening_evidence_v172.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v63a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v63a",
    )


def test_reference_output_matches_live_v63a_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63a_input_tree(tmp_path)

    session_record, view_packet, response_record = run_agentic_de_remote_operator_starter_v63a(
        repo_root_path=temp_root
    )

    assert session_record.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_remote_operator_session_record.json",
    )
    assert view_packet.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_remote_operator_view_packet.json",
    )
    assert response_record.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_remote_operator_response_record.json",
    )


def test_v63a_output_remains_bounded_remote_operator_starter(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63a_input_tree(tmp_path)

    session_record, view_packet, response_record = run_agentic_de_remote_operator_starter_v63a(
        repo_root_path=temp_root
    )

    assert session_record.target_arc == "vNext+173"
    assert session_record.target_path == "V63-A"
    assert session_record.remote_operator_principal_class == "remote_operator"
    assert session_record.remote_surface_class == "read_mostly_phone_safe_remote_operator_surface"
    assert session_record.admission_verdict == "admitted"
    assert session_record.frozen_policy_anchor_ref == (
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS173.md#machine-checkable-contract"
    )
    assert view_packet.remote_operator_session_ref == session_record.remote_operator_session_id
    assert len(view_packet.consumed_communication_refs) == 4
    assert "read-mostly" in view_packet.ask_blocker_summary
    assert response_record.remote_operator_session_ref == session_record.remote_operator_session_id
    assert response_record.selected_response_kind == "acknowledge"
    assert response_record.consumed_control_basis_ref_or_equivalent.startswith("session:")
    assert "may not mutate continuation" in response_record.response_basis_summary


def test_v63a_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63a_input_tree(tmp_path)

    first = run_agentic_de_remote_operator_starter_v63a(repo_root_path=temp_root)
    second = run_agentic_de_remote_operator_starter_v63a(repo_root_path=temp_root)

    assert [item.model_dump(mode="json") for item in first] == [
        item.model_dump(mode="json") for item in second
    ]


def test_v63a_accepts_explicit_approve_response_kind(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63a_input_tree(tmp_path)

    _session_record, _view_packet, response_record = run_agentic_de_remote_operator_starter_v63a(
        repo_root_path=temp_root,
        selected_response_kind="approve",
    )

    assert response_record.selected_response_kind == "approve"
    assert response_record.consumed_control_basis_ref_or_equivalent.endswith(
        "#approval_state_or_equivalent"
    )
    assert "URM approval/session posture" in response_record.response_basis_summary


def test_missing_required_v63a_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v63a_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V63-A lane drift record does not satisfy"):
        run_agentic_de_remote_operator_starter_v63a(repo_root_path=temp_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63a_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v63a"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_remote_operator_starter_v63a(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )


def test_v63a_rejects_non_shipped_v61a_egress_seam(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v63a_input_tree(tmp_path / "repo")
    communication_egress_path = (
        fixture_root.parent / "v61a" / "reference_agentic_de_communication_egress_packet.json"
    )
    payload = _load_json(
        fixture_root.parent / "v61a",
        "reference_agentic_de_communication_egress_packet.json",
    )
    assert isinstance(payload, dict)
    payload["selected_egress_surface_ref"] = "apps/api/src/adeu_api/urm_routes.py:/remote/operator"
    payload["communication_egress_id"] = None
    communication_egress_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V63-A requires the shipped exact resident V61-A egress seam",
    ):
        run_agentic_de_remote_operator_starter_v63a(repo_root_path=temp_root)


def test_v63a_rejects_premature_remote_operator_selection_in_v62c_evidence(
    tmp_path: Path,
) -> None:
    temp_root, _fixture_root = _copy_v63a_input_tree(tmp_path / "repo")
    evidence_path = (
        temp_root
        / "artifacts"
        / "agent_harness"
        / "v172"
        / "evidence_inputs"
        / "v62c_connector_bridge_hardening_evidence_v172.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload["remote_operator_law_selected_for_v62c"] = True
    evidence_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V62-C evidence must preserve remote-operator deferral"):
        run_agentic_de_remote_operator_starter_v63a(repo_root_path=temp_root)


def test_v63a_rejects_unsupported_response_kind(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63a_input_tree(tmp_path / "repo")

    with pytest.raises(ValueError, match="selected_response_kind"):
        run_agentic_de_remote_operator_starter_v63a(
            repo_root_path=temp_root,
            selected_response_kind="file_edit",
        )


def test_v63a_rejects_symlinked_repo_root(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v63a_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    with pytest.raises(ValueError, match="repository root may not be a symlink"):
        run_agentic_de_remote_operator_starter_v63a(repo_root_path=symlink_root)
