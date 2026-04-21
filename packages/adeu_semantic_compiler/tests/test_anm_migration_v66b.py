from __future__ import annotations

from pathlib import Path

import pytest
from adeu_semantic_compiler import check_v66a_anm_source_set, check_v66b_anm_migration_projection
from adeu_semantic_source import AnmCompileError


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _build_v66a_basis(root: Path):
    _write(
        root / "docs" / "LOCKED_CONTINUATION_vNEXT_PLUS182.md",
        """
:::adeu.doc_profile@1
schema: anm_doc_authority_profile@1
doc_id: adeu.lock.vnext_plus182
doc_class: lock
authority_layer: lock
source_posture: legacy_markdown
allowed_authority_blocks:
- D@1
- adeu.doc_profile@1
:::

supersession scope:
- docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md
- docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md
""".strip(),
    )
    _write(
        root / "docs" / "overlays" / "LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md",
        """
:::adeu.doc_profile@1
schema: anm_doc_authority_profile@1
doc_id: adeu.lock.vnext_plus182.overlay
doc_class: lock
authority_layer: lock
source_posture: companion_anm
allowed_authority_blocks:
- D@1
- adeu.doc_profile@1
:::
""".strip(),
    )
    registered_entries = [
        {
            "doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
            "doc_id_or_none": "adeu.lock.vnext_plus182",
            "doc_class": "lock",
            "authority_layer": "lock",
            "source_posture": "legacy_markdown",
            "lifecycle_status": "living",
            "classification_status": "classified",
            "companion_registration_status_or_none": "registered_host_document",
        },
        {
            "doc_ref": "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md",
            "doc_id_or_none": "adeu.lock.vnext_plus182.overlay",
            "doc_class": "lock",
            "authority_layer": "lock",
            "source_posture": "companion_anm",
            "lifecycle_status": "living",
            "classification_status": "classified",
            "host_doc_ref_or_none": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
            "companion_registration_status_or_none": "registered_companion_overlay",
        },
    ]
    return check_v66a_anm_source_set(repo_root_path=root, registered_entries=registered_entries)


def _profile_ref_by_doc_ref(v66a_result) -> dict[str, str]:
    return {
        profile.doc_ref: f"anm_doc_authority_profile:{profile.doc_id}"
        for profile in v66a_result.authority_profiles
    }


def test_v66b_builds_migration_projection_and_initial_diff(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result = _build_v66a_basis(root)
    _write(
        root / "docs" / "generated" / "anm_reader" / "LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md",
        """
# Reader View

Non-authoritative generated view.
""".strip(),
    )
    profile_refs = _profile_ref_by_doc_ref(v66a_result)

    result = check_v66b_anm_migration_projection(
        repo_root_path=root,
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        binding_rows=[
            {
                "binding_id": "binding:lock182-overlay",
                "host_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "companion_doc_ref_or_none": (
                    "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md"
                ),
                "host_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                "companion_profile_ref_or_none": profile_refs[
                    "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md"
                ],
                "binding_posture": "registered_non_overriding_companion",
                "current_markdown_authority_relation": "current_markdown_controlling",
                "supersession_claim_status": "none",
            }
        ],
        projection_rows=[
            {
                "projection_doc_ref": (
                    "docs/generated/anm_reader/LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md"
                ),
                "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "source_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                "projection_required": True,
                "projection_requirement_source": "explicit_projection_manifest",
                "projection_status": "current",
                "projection_authority_posture": "non_authoritative_generated_view",
                "drift_status": "in_sync",
            }
        ],
    )

    assert result.migration_binding_profile.binding_rows[0].semantic_diff_ref_or_none == (
        "anm_semantic_diff_report:diff:v66b-starter"
    )
    assert result.reader_projection_manifest.projection_rows[0].projection_content_hash_or_none
    assert result.semantic_diff_report.baseline_kind == "none_initial_report"
    assert {row.surface_kind for row in result.semantic_diff_report.change_rows} >= {
        "migration_binding",
        "reader_projection_manifest",
    }


def test_v66b_rejects_transition_law_ref_to_planning_doc(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result = _build_v66a_basis(root)
    _write(
        root / "docs" / "DRAFT_NEXT_ARC_OPTIONS_v51.md",
        """
docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md
docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md
supersession
""".strip(),
    )
    profile_refs = _profile_ref_by_doc_ref(v66a_result)

    with pytest.raises(AnmCompileError, match="lock-authority"):
        check_v66b_anm_migration_projection(
            repo_root_path=root,
            manifest=v66a_result.manifest,
            authority_profiles=v66a_result.authority_profiles,
            class_policy=v66a_result.class_policy,
            binding_rows=[
                {
                    "binding_id": "binding:lock182-overlay",
                    "host_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                    "companion_doc_ref_or_none": (
                        "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md"
                    ),
                    "host_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                    "companion_profile_ref_or_none": profile_refs[
                        "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md"
                    ],
                    "binding_posture": "registered_non_overriding_companion",
                    "current_markdown_authority_relation": "current_markdown_controlling",
                    "supersession_claim_status": "claimed_with_explicit_transition_law",
                    "explicit_transition_law_ref_or_none": "docs/DRAFT_NEXT_ARC_OPTIONS_v51.md#bad",
                }
            ],
            projection_rows=[],
        )


def test_v66b_rejects_generated_projection_authority_claim(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result = _build_v66a_basis(root)
    _write(
        root / "docs" / "generated" / "anm_reader" / "LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md",
        """
# Reader View

Non-authoritative generated view.
""".strip(),
    )
    profile_refs = _profile_ref_by_doc_ref(v66a_result)

    with pytest.raises(AnmCompileError, match="claims authority"):
        check_v66b_anm_migration_projection(
            repo_root_path=root,
            manifest=v66a_result.manifest,
            authority_profiles=v66a_result.authority_profiles,
            class_policy=v66a_result.class_policy,
            binding_rows=[],
            projection_rows=[
                {
                    "projection_doc_ref": (
                        "docs/generated/anm_reader/LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md"
                    ),
                    "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                    "source_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                    "projection_required": True,
                    "projection_requirement_source": "explicit_projection_manifest",
                    "projection_status": "current",
                    "projection_authority_posture": "invalid_claims_authority",
                    "drift_status": "in_sync",
                }
            ],
        )


def test_v66b_explicit_baseline_marks_changed_projection(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result = _build_v66a_basis(root)
    projection_path = (
        root / "docs" / "generated" / "anm_reader" / "LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md"
    )
    _write(
        projection_path,
        """
# Reader View

Non-authoritative generated view.
""".strip(),
    )
    profile_refs = _profile_ref_by_doc_ref(v66a_result)

    initial = check_v66b_anm_migration_projection(
        repo_root_path=root,
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        binding_rows=[],
        projection_rows=[
            {
                "projection_doc_ref": (
                    "docs/generated/anm_reader/LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md"
                ),
                "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "source_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                "projection_required": True,
                "projection_requirement_source": "explicit_projection_manifest",
                "projection_status": "current",
                "projection_authority_posture": "non_authoritative_generated_view",
                "drift_status": "in_sync",
            }
        ],
    )

    _write(
        projection_path,
        """
# Reader View

Non-authoritative generated view.

Updated content.
""".strip(),
    )
    changed = check_v66b_anm_migration_projection(
        repo_root_path=root,
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        binding_rows=[],
        projection_rows=[
            {
                "projection_doc_ref": (
                    "docs/generated/anm_reader/LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md"
                ),
                "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "source_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                "projection_required": True,
                "projection_requirement_source": "explicit_projection_manifest",
                "projection_status": "stale",
                "projection_authority_posture": "non_authoritative_generated_view",
                "drift_status": "source_changed_projection_stale",
            }
        ],
        baseline_kind="prior_committed_artifact",
        baseline_report=initial.semantic_diff_report,
    )

    assert any(
        row.surface_kind == "reader_projection_manifest" and row.change_kind == "changed"
        for row in changed.semantic_diff_report.change_rows
    )


def test_v66b_rejects_companion_binding_for_wrong_host(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result = _build_v66a_basis(root)
    manifest = v66a_result.manifest.model_copy(deep=True)
    for entry in manifest.source_entries:
        if entry.doc_ref == "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md":
            entry.host_doc_ref_or_none = "docs/SOME_OTHER_LOCK.md"
            break
    profile_refs = _profile_ref_by_doc_ref(v66a_result)

    with pytest.raises(AnmCompileError, match="companion host mismatch"):
        check_v66b_anm_migration_projection(
            repo_root_path=root,
            manifest=manifest,
            authority_profiles=v66a_result.authority_profiles,
            class_policy=v66a_result.class_policy,
            binding_rows=[
                {
                    "binding_id": "binding:lock182-overlay",
                    "host_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                    "companion_doc_ref_or_none": (
                        "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md"
                    ),
                    "host_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                    "companion_profile_ref_or_none": profile_refs[
                        "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md"
                    ],
                    "binding_posture": "registered_non_overriding_companion",
                    "current_markdown_authority_relation": "current_markdown_controlling",
                    "supersession_claim_status": "none",
                }
            ],
            projection_rows=[],
        )


def test_v66b_prior_committed_baseline_does_not_repeat_removed_rows(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result = _build_v66a_basis(root)
    projection_path = (
        root / "docs" / "generated" / "anm_reader" / "LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md"
    )
    _write(
        projection_path,
        """
# Reader View

Non-authoritative generated view.
""".strip(),
    )
    profile_refs = _profile_ref_by_doc_ref(v66a_result)

    initial = check_v66b_anm_migration_projection(
        repo_root_path=root,
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        binding_rows=[
            {
                "binding_id": "binding:lock182-overlay",
                "host_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "companion_doc_ref_or_none": (
                    "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md"
                ),
                "host_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                "companion_profile_ref_or_none": profile_refs[
                    "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md"
                ],
                "binding_posture": "registered_non_overriding_companion",
                "current_markdown_authority_relation": "current_markdown_controlling",
                "supersession_claim_status": "none",
            }
        ],
        projection_rows=[
            {
                "projection_doc_ref": (
                    "docs/generated/anm_reader/LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md"
                ),
                "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "source_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                "projection_required": True,
                "projection_requirement_source": "explicit_projection_manifest",
                "projection_status": "current",
                "projection_authority_posture": "non_authoritative_generated_view",
                "drift_status": "in_sync",
            }
        ],
    )

    removed = check_v66b_anm_migration_projection(
        repo_root_path=root,
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        binding_rows=[],
        projection_rows=[],
        baseline_kind="prior_committed_artifact",
        baseline_report=initial.semantic_diff_report,
    )

    stable = check_v66b_anm_migration_projection(
        repo_root_path=root,
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        binding_rows=[],
        projection_rows=[],
        baseline_kind="prior_committed_artifact",
        baseline_report=removed.semantic_diff_report,
    )

    assert not any(
        row.change_kind == "removed"
        and row.surface_kind in {"migration_binding", "reader_projection_manifest"}
        for row in stable.semantic_diff_report.change_rows
    )
