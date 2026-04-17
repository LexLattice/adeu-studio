from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_external_assistant_egress_bridge_v62b
from adeu_ir.repo import repo_root
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v62b"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v61b",
    "packages/adeu_agentic_de/tests/fixtures/v62a",
    "packages/adeu_agentic_de/tests/fixtures/v62b",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v170/evidence_inputs/v62a_connector_admission_evidence_v170.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v62b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v62b",
    )


def test_reference_output_matches_live_v62b_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62b_input_tree(tmp_path)

    egress_bridge = run_agentic_de_external_assistant_egress_bridge_v62b(
        repo_root_path=temp_root,
    )

    assert egress_bridge.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_external_assistant_egress_bridge_packet.json",
    )


def test_v62b_output_remains_explicit_egress_follow_on_only(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62b_input_tree(tmp_path)

    egress_bridge = run_agentic_de_external_assistant_egress_bridge_v62b(
        repo_root_path=temp_root,
    )

    assert egress_bridge.target_arc == "vNext+171"
    assert egress_bridge.target_path == "V62-B"
    assert egress_bridge.selected_connector_principal_class == "external_assistant"
    assert egress_bridge.consumed_bridge_office_binding_ref_or_none is not None
    assert egress_bridge.consumed_message_rewitness_gate_ref_or_none is not None
    assert egress_bridge.consumed_rewitness_basis_summary_or_none is not None
    assert "explicit_positive_rewitness_basis_carried" in egress_bridge.reason_codes


def test_missing_positive_rewitness_basis_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v62b_input_tree(tmp_path / "repo")
    rewitness_path = (
        fixture_root.parent
        / "v61b"
        / "reference_agentic_de_message_rewitness_gate_record.json"
    )
    payload = _load_json(
        fixture_root.parent / "v61b", "reference_agentic_de_message_rewitness_gate_record.json"
    )
    assert isinstance(payload, dict)
    payload["witness_basis_ref_or_none"] = None
    payload["certificate_ref_or_none"] = None
    payload["message_rewitness_gate_id"] = None
    rewitness_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValidationError, match="positive rewitness requires"):
        run_agentic_de_external_assistant_egress_bridge_v62b(repo_root_path=temp_root)


def test_default_symlinked_repo_root_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import adeu_agentic_de.checker as checker_module

    temp_root, _fixture_root = _copy_v62b_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    monkeypatch.setattr(checker_module, "repo_root", lambda anchor: symlink_root)

    with pytest.raises(
        ValueError,
        match="repository root may not be a symlink for V62-B external assistant bridge",
    ):
        run_agentic_de_external_assistant_egress_bridge_v62b()


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v62b_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v62b"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_external_assistant_egress_bridge_v62b(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )


def test_mismatched_v61a_egress_interpretation_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v62b_input_tree(tmp_path / "repo")
    egress_path = (
        fixture_root.parent / "v61a" / "reference_agentic_de_communication_egress_packet.json"
    )
    payload = _load_json(
        fixture_root.parent / "v61a", "reference_agentic_de_communication_egress_packet.json"
    )
    assert isinstance(payload, dict)
    payload["ingress_interpretation_ref"] = "agentic_de_ingress_interpretation_wrong"
    payload["communication_egress_id"] = None
    egress_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V62-B communication egress must bind the shipped V62-A interpretation basis",
    ):
        run_agentic_de_external_assistant_egress_bridge_v62b(repo_root_path=temp_root)
