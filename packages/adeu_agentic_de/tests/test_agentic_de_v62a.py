from __future__ import annotations

import json
import shutil
from datetime import datetime, timezone
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_connector_admission_v62a
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v62a"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v62a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v167/evidence_inputs/v61a_governed_communication_evidence_v167.json",
    "artifacts/agent_harness/v168/evidence_inputs/v61b_bridge_office_rewitness_evidence_v168.json",
    "artifacts/agent_harness/v169/evidence_inputs/v61c_governed_communication_hardening_evidence_v169.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v62a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v62a",
    )


def test_reference_outputs_match_live_v62a_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62a_input_tree(tmp_path)

    admission, ingress_bridge = run_agentic_de_connector_admission_v62a(repo_root_path=temp_root)

    assert admission.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_connector_admission_record.json",
    )
    assert ingress_bridge.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_external_assistant_ingress_bridge_packet.json",
    )


def test_v62a_outputs_remain_ingress_only_and_external_assistant_only(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62a_input_tree(tmp_path)

    admission, ingress_bridge = run_agentic_de_connector_admission_v62a(repo_root_path=temp_root)

    assert admission.target_arc == "vNext+170"
    assert admission.target_path == "V62-A"
    assert admission.admission_verdict == "admitted"
    assert admission.selected_connector_principal_class == "external_assistant"
    assert admission.connector_provider_class == "codex"
    assert ingress_bridge.selected_connector_principal_class == "external_assistant"
    assert ingress_bridge.connector_admission_ref == admission.connector_admission_id
    assert ingress_bridge.consumed_communication_ingress_ref.startswith(
        "agentic_de_communication_ingress_"
    )
    assert "V61-A" in ingress_bridge.bridge_basis_summary


def test_missing_exposed_connectors_fail_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v62a_input_tree(tmp_path)
    snapshot_path = fixture_root / "reference_connector_snapshot_response.json"
    payload = _load_json(fixture_root, "reference_connector_snapshot_response.json")
    assert isinstance(payload, dict)
    payload["exposed_connectors"] = []
    payload["connector_exposure"] = []
    snapshot_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="at least one exposed connector"):
        run_agentic_de_connector_admission_v62a(repo_root_path=temp_root)


def test_min_acceptable_ts_fail_closed_on_stale_snapshot(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62a_input_tree(tmp_path)

    with pytest.raises(ValueError, match="older than min_acceptable_ts"):
        run_agentic_de_connector_admission_v62a(
            repo_root_path=temp_root,
            min_acceptable_ts=datetime(2026, 4, 17, 0, 1, tzinfo=timezone.utc),
        )


def test_malformed_connector_ids_fail_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v62a_input_tree(tmp_path)
    snapshot_path = fixture_root / "reference_connector_snapshot_response.json"
    payload = _load_json(fixture_root, "reference_connector_snapshot_response.json")
    assert isinstance(payload, dict)
    assert isinstance(payload["exposed_connectors"], list)
    payload["exposed_connectors"][0]["id"] = None
    snapshot_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="snapshot\\.exposed_connectors\\[0\\] must carry one non-empty string id",
    ):
        run_agentic_de_connector_admission_v62a(repo_root_path=temp_root)


def test_default_symlinked_repo_root_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import adeu_agentic_de.checker as checker_module

    temp_root, _fixture_root = _copy_v62a_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    monkeypatch.setattr(checker_module, "repo_root", lambda anchor: symlink_root)

    with pytest.raises(
        ValueError,
        match="repository root may not be a symlink for V62-A connector admission",
    ):
        run_agentic_de_connector_admission_v62a()
