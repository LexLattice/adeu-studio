from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_repo_writable_surface_hardening_v64c
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v64c"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v64a",
    "packages/adeu_agentic_de/tests/fixtures/v64b",
    "packages/adeu_agentic_de/tests/fixtures/v64c",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v176/evidence_inputs/v64a_repo_writable_surface_starter_evidence_v176.json",
    "artifacts/agent_harness/v177/evidence_inputs/v64b_repo_write_restoration_evidence_v177.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v64c_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v64c",
    )


def test_reference_output_matches_live_v64c_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64c_input_tree(tmp_path)

    register = run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_repo_writable_surface_hardening_register.json",
    )


def test_v64c_output_remains_advisory_only_and_policy_anchored(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64c_input_tree(tmp_path)

    register = run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+178"
    assert register.target_path == "V64-C"
    assert register.baseline_checker_version == "agentic_de_repo_writable_surface_hardening_v64c"
    assert register.advisory_only is True
    assert register.candidate_only is True
    assert register.path_level_only is True
    assert register.exemplar_evidence_non_generalizing_by_default is True
    assert register.changes_live_behavior_by_default is False
    assert register.committed_lane_artifacts_outrank_narrative_docs is True
    assert register.evidence_basis_distinct_from_recommendation is True
    assert register.recommendation_function_extensional_and_replayable is True
    assert register.explicit_frozen_policy_anchor_required is True
    assert register.keep_warning_only_retains_current_advisory_posture_only is True
    assert register.optional_upstream_basis_consistency_fails_closed is True
    entry = register.entries[0]
    assert (
        entry.selected_hardening_target_surface
        == "shipped_v64a_v64b_writable_surface_lineage_over_one_exact_admitted_repo_path_only"
    )
    assert (
        entry.frozen_policy_ref
        == "docs/LOCKED_CONTINUATION_vNEXT_PLUS178.md#machine-checkable-contract"
    )
    assert entry.recommended_outcome == "candidate_for_later_writable_surface_hardening"
    assert entry.target_admission_verdict == "admitted"
    assert entry.repo_write_restoration_ref_or_none is not None
    assert entry.repo_write_reintegration_ref_or_none is not None
    assert entry.selected_write_effect_or_restoration_kind_summary_or_none is not None
    assert "local_write/create_new" in entry.preserved_write_semantics_summary
    assert len(entry.root_origin_ids) == len(set(entry.root_origin_ids))
    assert "non-independent writable-surface hardening support" in entry.root_origin_dedup_summary


def test_v64c_recommendation_is_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64c_input_tree(tmp_path)

    first = run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)
    second = run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_missing_required_v64c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64c_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V64-C lane drift record does not satisfy"):
        run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64c_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v64c"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_repo_writable_surface_hardening_v64c(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )


def test_v64c_keep_warning_only_when_optional_upstream_basis_absent(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64c_input_tree(tmp_path / "repo")

    register = run_agentic_de_repo_writable_surface_hardening_v64c(
        repo_root_path=temp_root,
        v64b_repo_write_restoration_path=None,
        v64b_repo_write_reintegration_path=None,
    )

    entry = register.entries[0]
    assert entry.recommended_outcome == "keep_warning_only"
    assert entry.selected_write_effect_or_restoration_kind_summary_or_none is None
    assert entry.repo_write_restoration_ref_or_none is None
    assert entry.repo_write_reintegration_ref_or_none is None


def test_v64c_rejects_reintegration_without_restoration(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64c_input_tree(tmp_path / "repo")

    with pytest.raises(
        ValueError,
        match="reintegration basis requires the shipped V64-B restoration",
    ):
        run_agentic_de_repo_writable_surface_hardening_v64c(
            repo_root_path=temp_root,
            v64b_repo_write_restoration_path=None,
        )


def test_v64c_rejects_mismatched_v64b_restoration_target(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64c_input_tree(tmp_path / "repo")
    restoration_path = (
        fixture_root.parent / "v64b" / "reference_agentic_de_repo_write_restoration_record.json"
    )
    payload = _load_json(
        fixture_root.parent / "v64b", "reference_agentic_de_repo_write_restoration_record.json"
    )
    assert isinstance(payload, dict)
    payload["selected_target_path_summary"] = (
        "artifacts/agentic_de/v59/workspace_continuity/runtime/other_target.diff"
    )
    payload["repo_write_restoration_id"] = None
    restoration_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V64-C restoration must preserve the shipped exact admitted target",
    ):
        run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)


def test_v64c_rejects_mismatched_v64b_reintegration_chain(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64c_input_tree(tmp_path / "repo")
    reintegration_path = (
        fixture_root.parent / "v64b" / "reference_agentic_de_repo_write_reintegration_report.json"
    )
    payload = _load_json(
        fixture_root.parent / "v64b", "reference_agentic_de_repo_write_reintegration_report.json"
    )
    assert isinstance(payload, dict)
    payload["repo_write_restoration_ref"] = "agentic_de_repo_write_restoration_wrong"
    payload["repo_write_reintegration_report_id"] = None
    reintegration_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V64-C reintegration must bind the same shipped V64-B restoration chain",
    ):
        run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)


def test_v64c_rejects_non_shipped_v61a_ingress_seam(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64c_input_tree(tmp_path / "repo")
    ingress_path = (
        fixture_root.parent / "v61a" / "reference_agentic_de_communication_ingress_packet.json"
    )
    payload = _load_json(
        fixture_root.parent / "v61a", "reference_agentic_de_communication_ingress_packet.json"
    )
    assert isinstance(payload, dict)
    payload["selected_api_route_ref_or_equivalent"] = (
        "apps/api/src/adeu_api/urm_routes.py:/copilot/send_alt"
    )
    payload["communication_ingress_id"] = None
    ingress_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V64-C requires the shipped exact resident V61-A ingress seam",
    ):
        run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)


def test_v64c_rejects_malformed_v64b_evidence_selected_record_shapes(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64c_input_tree(tmp_path / "repo")
    evidence_path = (
        temp_root
        / "artifacts"
        / "agent_harness"
        / "v177"
        / "evidence_inputs"
        / "v64b_repo_write_restoration_evidence_v177.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload["selected_record_shapes"] = [
        "agentic_de_repo_write_restoration_record@1",
        {"unexpected": "object"},
    ]
    evidence_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="selected_record_shapes must be a list of strings"):
        run_agentic_de_repo_writable_surface_hardening_v64c(repo_root_path=temp_root)
