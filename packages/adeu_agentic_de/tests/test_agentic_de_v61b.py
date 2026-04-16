from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import (
    AgenticDeMessageRewitnessGateRecord,
    run_agentic_de_governed_communication_v61b,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v61b"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v61b",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v167/evidence_inputs/v61a_governed_communication_evidence_v167.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v61b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v61b",
    )


def test_reference_outputs_match_live_v61b_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61b_input_tree(tmp_path)

    bridge_binding, rewitness_gate = run_agentic_de_governed_communication_v61b(
        repo_root_path=temp_root,
    )

    assert bridge_binding.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_bridge_office_binding_record.json",
    )
    assert rewitness_gate.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_message_rewitness_gate_record.json",
    )


def test_v61b_outputs_remain_bridge_and_witness_candidate_only(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61b_input_tree(tmp_path)

    bridge_binding, rewitness_gate = run_agentic_de_governed_communication_v61b(
        repo_root_path=temp_root,
    )

    assert bridge_binding.target_arc == "vNext+168"
    assert bridge_binding.target_path == "V61-B"
    assert bridge_binding.evidence_only is True
    assert bridge_binding.changes_live_behavior_by_default is False
    assert bridge_binding.selected_bridge_office_posture == "resident_bridge_bound"
    assert bridge_binding.frozen_policy_anchor_ref == (
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS168.md#machine-checkable-contract"
    )
    assert rewitness_gate.rewitness_outcome == "witness_candidate_promoted"
    assert rewitness_gate.witness_basis_ref_or_none == rewitness_gate.communication_egress_ref
    assert rewitness_gate.certificate_ref_or_none is None
    assert "rewitness_non_mutating_for_v60_state" in rewitness_gate.rewitness_reason_codes


def test_invalid_v61a_route_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61b_input_tree(tmp_path / "repo")
    ingress_path = (
        fixture_root.parent / "v61a" / "reference_agentic_de_communication_ingress_packet.json"
    )
    payload = _load_json(
        fixture_root.parent / "v61a", "reference_agentic_de_communication_ingress_packet.json"
    )
    assert isinstance(payload, dict)
    payload["selected_api_route_ref_or_equivalent"] = (
        "apps/api/src/adeu_api/urm_routes.py:/copilot/other"
    )
    payload["communication_ingress_id"] = None
    ingress_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="exact resident V61-A API route"):
        run_agentic_de_governed_communication_v61b(repo_root_path=temp_root)


def test_positive_rewitness_without_basis_fails_closed() -> None:
    with pytest.raises(ValueError, match="positive rewitness requires"):
        AgenticDeMessageRewitnessGateRecord(
            target_arc="vNext+168",
            target_path="V61-B",
            communication_ingress_ref="ingress",
            ingress_interpretation_ref="interpretation",
            communication_egress_ref="egress",
            bridge_office_binding_ref="bridge",
            task_charter_ref="charter",
            latest_continuation_basis_ref="refresh",
            rewitness_outcome="witness_candidate_promoted",
            rewitness_reason_codes=["rewitness_outcome_witness_candidate_promoted"],
            frozen_policy_anchor_ref="docs/LOCKED_CONTINUATION_vNEXT_PLUS168.md#machine-checkable-contract",
            rewitness_basis_summary="explicit bridge binding required",
            field_origin_tags={
                "rewitness_outcome": "current_turn_derived",
                "frozen_policy_anchor_ref": "shaping_only",
                "rewitness_basis_summary": "current_turn_derived",
                "root_origin_dedup_summary": "current_turn_derived",
            },
            field_dependence_tags={
                "rewitness_outcome": ["ingress", "interpretation", "egress", "bridge", "refresh"],
                "frozen_policy_anchor_ref": [],
                "rewitness_basis_summary": ["ingress", "bridge"],
                "root_origin_dedup_summary": ["ingress", "bridge"],
            },
            root_origin_ids=["root:1"],
            root_origin_dedup_summary="deduped roots",
            evidence_refs=["ingress", "bridge"],
        )


def test_default_symlinked_repo_root_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import adeu_agentic_de.checker as checker_module

    temp_root, _fixture_root = _copy_v61b_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    monkeypatch.setattr(checker_module, "repo_root", lambda anchor: symlink_root)

    with pytest.raises(
        ValueError,
        match="repository root may not be a symlink for V61-B communication",
    ):
        run_agentic_de_governed_communication_v61b()


def test_ingress_symlink_component_input_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61b_input_tree(tmp_path / "repo")
    broken_dir = temp_root / "broken-link"
    broken_dir.symlink_to(temp_root / "missing-target", target_is_directory=True)

    with pytest.raises(ValueError, match="may not traverse symlink components"):
        run_agentic_de_governed_communication_v61b(
            repo_root_path=temp_root,
            v61a_communication_ingress_path=broken_dir
            / "reference_agentic_de_communication_ingress_packet.json",
        )
