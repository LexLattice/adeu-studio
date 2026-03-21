from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_core_ir import (
    DEFAULT_EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_REFERENCE_PATH,
    DEFAULT_MODULE_CONFORMANCE_REPORT_REFERENCE_PATH,
    DEFAULT_V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_PATH,
    materialize_v39a_external_contribution_alignment_evidence,
)
from adeu_core_ir.external_contribution_alignment_evidence import (
    ExternalContributionAlignmentEvidenceError,
)
from adeu_ir.repo import repo_root


def _source_repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _copy_repo_relative_file(*, source_root: Path, target_root: Path, relative_path: str) -> None:
    source = source_root / relative_path
    target = target_root / relative_path
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)


def _build_temp_repo_fixture_tree(tmp_path: Path) -> Path:
    source_root = _source_repo_root()
    repo_root_path = tmp_path / "repo"
    repo_root_path.mkdir()
    for relative_path in (
        "AGENTS.md",
        "docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md",
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS72.md",
        "apps/api/fixtures/external_contribution_alignment/vnext_plus72/pr293_poetry_utility_claimed_scope_snapshot.md",
        "apps/api/fixtures/external_contribution_alignment/vnext_plus72/pr293_poetry_utility_diff_snapshot.patch",
        "apps/api/fixtures/external_contribution_alignment/vnext_plus72/pr293_poetry_utility_metadata_snapshot.json",
        DEFAULT_EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_REFERENCE_PATH,
        DEFAULT_MODULE_CONFORMANCE_REPORT_REFERENCE_PATH,
        DEFAULT_V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_PATH,
    ):
        _copy_repo_relative_file(
            source_root=source_root,
            target_root=repo_root_path,
            relative_path=relative_path,
        )
    return repo_root_path


def test_materialized_evidence_matches_committed_reference_fixture() -> None:
    root = _source_repo_root()
    materialized = materialize_v39a_external_contribution_alignment_evidence(repository_root=root)
    fixture_payload = _load_json(root / DEFAULT_V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_PATH)

    assert materialized.path == DEFAULT_V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_EVIDENCE_PATH
    assert materialized.payload == fixture_payload
    assert materialized.payload["three_layer_scope_model_verified"] is True
    assert materialized.payload["default_negative_precedent_verified"] is True


def test_materializer_rejects_report_drift_against_packet(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    report_path = repo_root_path / DEFAULT_MODULE_CONFORMANCE_REPORT_REFERENCE_PATH
    report_payload = _load_json(report_path)
    report_payload["overall_judgment"] = "pass"
    report_path.write_text(json.dumps(report_payload, indent=2, sort_keys=True) + "\n")

    with pytest.raises(
        ExternalContributionAlignmentEvidenceError,
        match="module conformance report must match deterministic derivation from packet",
    ):
        materialize_v39a_external_contribution_alignment_evidence(
            repository_root=repo_root_path,
        )


def test_materializer_rejects_missing_localized_subject_input(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    missing_path = (
        repo_root_path
        / "apps/api/fixtures/external_contribution_alignment/vnext_plus72"
        / "pr293_poetry_utility_diff_snapshot.patch"
    )
    missing_path.unlink()

    with pytest.raises(
        ExternalContributionAlignmentEvidenceError,
        match="localized_subject_inputs\\[diff\\]\\.path must resolve to an existing repo file",
    ):
        materialize_v39a_external_contribution_alignment_evidence(
            repository_root=repo_root_path,
        )
