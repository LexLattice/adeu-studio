from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_delegated_worker_hardening_v65c
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v65c"

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v65a",
    "packages/adeu_agentic_de/tests/fixtures/v65b",
    "packages/adeu_agentic_de/tests/fixtures/v65c",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v179/evidence_inputs/v65a_delegated_worker_export_starter_evidence_v179.json",
    "artifacts/agent_harness/v180/evidence_inputs/v65b_delegated_worker_reconciliation_evidence_v180.json",
)


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v65c_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v65c",
    )


def test_reference_output_matches_live_v65c_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65c_input_tree(tmp_path)

    register = run_agentic_de_delegated_worker_hardening_v65c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_delegated_worker_hardening_register.json",
    )


def test_v65c_output_remains_advisory_only_and_policy_anchored(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65c_input_tree(tmp_path)

    register = run_agentic_de_delegated_worker_hardening_v65c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+181"
    assert register.target_path == "V65-C"
    assert register.baseline_checker_version == "agentic_de_delegated_worker_hardening_v65c"
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
        == "shipped_v65a_v65b_delegated_lineage_over_one_exact_exported_scope_only"
    )
    assert (
        entry.frozen_policy_ref
        == "docs/LOCKED_CONTINUATION_vNEXT_PLUS181.md#machine-checkable-contract"
    )
    assert entry.recommended_outcome == "candidate_for_later_delegated_worker_hardening"
    assert entry.delegated_worker_reconciliation_report_ref_or_none is not None
    assert entry.worker_result_or_conformance_basis_ref_or_equivalent_or_none is not None
    assert (
        entry.selected_worker_result_or_conformance_kind_summary_or_none
        is not None
    )
    assert "local_write/create_new" in entry.preserved_write_semantics_summary
    assert len(entry.root_origin_ids) == len(set(entry.root_origin_ids))
    assert "non-independent delegated-worker hardening support" in entry.root_origin_dedup_summary


def test_v65c_recommendation_is_replayable_for_same_inputs(tmp_path: Path) -> None:
    first_root, _fixture_root = _copy_v65c_input_tree(tmp_path / "first")
    second_root, _fixture_root = _copy_v65c_input_tree(tmp_path / "second")

    first = run_agentic_de_delegated_worker_hardening_v65c(repo_root_path=first_root)
    second = run_agentic_de_delegated_worker_hardening_v65c(repo_root_path=second_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_missing_repo_root_path_fails_closed(tmp_path: Path) -> None:
    missing_root = tmp_path / "missing-root"

    with pytest.raises(FileNotFoundError, match="repository root not found"):
        run_agentic_de_delegated_worker_hardening_v65c(repo_root_path=missing_root)


def test_missing_required_v65c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v65c_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V65-C lane drift record does not satisfy"):
        run_agentic_de_delegated_worker_hardening_v65c(repo_root_path=temp_root)


def test_lexically_outside_symlinked_input_path_fails_closed(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65c_input_tree(tmp_path / "repo")
    outside_root = tmp_path / "outside"
    outside_root.mkdir()
    aliased_packages = outside_root / "packages-link"
    aliased_packages.symlink_to(temp_root / "packages", target_is_directory=True)
    aliased_lane_drift = (
        aliased_packages
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v65c"
        / "reference_agentic_de_lane_drift_record.json"
    )

    with pytest.raises(
        ValueError,
        match="lane_drift_path must be lexically within the repository root",
    ):
        run_agentic_de_delegated_worker_hardening_v65c(
            repo_root_path=temp_root,
            lane_drift_path=aliased_lane_drift,
        )


def test_v65c_keep_warning_only_when_reconciliation_basis_absent(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65c_input_tree(tmp_path / "repo")

    register = run_agentic_de_delegated_worker_hardening_v65c(
        repo_root_path=temp_root,
        v65b_delegated_worker_reconciliation_path=None,
    )

    entry = register.entries[0]
    assert entry.recommended_outcome == "keep_warning_only"
    assert entry.delegated_worker_reconciliation_report_ref_or_none is None
    assert entry.worker_result_or_conformance_basis_ref_or_equivalent_or_none is None
    assert entry.selected_worker_result_or_conformance_kind_summary_or_none is None


def test_v65c_rejects_mismatched_v65b_export_binding(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v65c_input_tree(tmp_path / "repo")
    report_name = "reference_agentic_de_delegated_worker_reconciliation_report.json"
    report_path = fixture_root.parent / "v65b" / report_name
    payload = _load_json(
        fixture_root.parent / "v65b",
        report_name,
    )
    assert isinstance(payload, dict)
    payload["delegated_worker_export_packet_ref"] = (
        "agentic_de_delegated_worker_export_packet_wrong"
    )
    payload["delegated_worker_reconciliation_report_id"] = None
    report_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="V65-C reconciliation must bind the shipped V65-A export packet",
    ):
        run_agentic_de_delegated_worker_hardening_v65c(repo_root_path=temp_root)


def test_v65c_rejects_malformed_v65b_evidence_selected_record_shapes(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65c_input_tree(tmp_path / "repo")
    evidence_path = (
        temp_root
        / "artifacts"
        / "agent_harness"
        / "v180"
        / "evidence_inputs"
        / "v65b_delegated_worker_reconciliation_evidence_v180.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload["selected_record_shapes"] = [
        "agentic_de_delegated_worker_reconciliation_report@1",
        {"unexpected": "object"},
    ]
    evidence_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="selected_record_shapes must be a list of strings"):
        run_agentic_de_delegated_worker_hardening_v65c(repo_root_path=temp_root)
