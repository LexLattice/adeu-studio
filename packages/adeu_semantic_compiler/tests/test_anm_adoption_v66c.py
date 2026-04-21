from __future__ import annotations

from pathlib import Path

import adeu_semantic_compiler.anm_adoption as anm_adoption
from adeu_semantic_compiler import (
    build_v66c_compile_report,
    build_v66c_prose_boundary_notice_set,
    check_v66a_anm_source_set,
    check_v66b_anm_migration_projection,
    check_v66c_anm_adoption_hardening,
)


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _build_v66a_basis(root: Path, *, include_transition_doc: bool = False):
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
    if include_transition_doc:
        registered_entries.append(
            {
                "doc_ref": "docs/LOCKED_CONTINUATION_TRANSITION_SCOPE.md",
                "doc_id_or_none": "adeu.lock.transition_scope",
                "doc_class": "lock",
                "authority_layer": "lock",
                "source_posture": "legacy_markdown",
                "lifecycle_status": "living",
                "classification_status": "classified",
            }
        )
    return check_v66a_anm_source_set(repo_root_path=root, registered_entries=registered_entries)


def _profile_ref_by_doc_ref(v66a_result) -> dict[str, str]:
    return {
        profile.doc_ref: f"anm_doc_authority_profile:{profile.doc_id}"
        for profile in v66a_result.authority_profiles
    }


def _build_v66b_basis(
    root: Path,
    *,
    projection_status: str = "current",
    drift_status: str = "in_sync",
    projection_authority_posture: str = "non_authoritative_generated_view",
    with_transition_law: bool = False,
):
    if with_transition_law:
        _write(
            root / "docs" / "LOCKED_CONTINUATION_TRANSITION_SCOPE.md",
            """
supersession scope:
- docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md
- docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md
""".strip(),
        )
    v66a_result = _build_v66a_basis(root, include_transition_doc=with_transition_law)
    projection_doc_ref = "docs/generated/anm_reader/LOCKED_CONTINUATION_vNEXT_PLUS182.reader.md"
    _write(
        root / projection_doc_ref,
        """
# Reader View

Non-authoritative generated view.
""".strip(),
    )
    profile_refs = _profile_ref_by_doc_ref(v66a_result)
    return v66a_result, check_v66b_anm_migration_projection(
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
                "supersession_claim_status": (
                    "claimed_with_explicit_transition_law"
                    if with_transition_law
                    else "none"
                ),
                "explicit_transition_law_ref_or_none": (
                    "docs/LOCKED_CONTINUATION_TRANSITION_SCOPE.md#scope"
                    if with_transition_law
                    else None
                ),
            }
        ],
        projection_rows=[
            {
                "projection_doc_ref": projection_doc_ref,
                "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "source_profile_ref": profile_refs["docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"],
                "projection_required": True,
                "projection_requirement_source": "explicit_projection_manifest",
                "projection_status": projection_status,
                "projection_authority_posture": projection_authority_posture,
                "drift_status": drift_status,
            }
        ],
    )


def test_v66c_flags_normative_prose_but_ignores_examples_and_quotes(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result, v66b_result = _build_v66b_basis(
        root,
        projection_status="stale",
        drift_status="source_changed_projection_stale",
    )

    result = check_v66c_anm_adoption_hardening(
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        migration_binding_profile=v66b_result.migration_binding_profile,
        reader_projection_manifest=v66b_result.reader_projection_manifest,
        semantic_diff_report=v66b_result.semantic_diff_report,
        prose_boundary_samples=[
            {
                "sample_ref": "sample:example",
                "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "sample_text": "must remain inside example text",
                "sample_kind": "example_block",
            },
            {
                "sample_ref": "sample:plain",
                "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "sample_text": "This migration must stay review-only for now.",
                "sample_kind": "plain_prose",
            },
            {
                "sample_ref": "sample:quoted",
                "source_doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                "sample_text": "> must remain quoted text",
                "sample_kind": "quoted_text",
            },
        ],
    )

    assert result.prose_boundary_notice_set.report_status == "valid"
    assert {
        row.notice_kind for row in result.prose_boundary_notice_set.notice_rows
    } == {
        "normative_tone_without_compiled_authority_block",
        "projection_staleness_visible",
    }
    assert (
        result.compile_report.advisory_result.recommended_adoption_posture_or_none
        == "needs_projection_refresh"
    )


def test_v66c_invalidates_report_when_projection_claims_authority(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result, v66b_result = _build_v66b_basis(root)
    projection_payload = v66b_result.reader_projection_manifest.model_dump(mode="json")
    projection_payload["projection_rows"][0]["projection_authority_posture"] = (
        "invalid_claims_authority"
    )

    result = check_v66c_anm_adoption_hardening(
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        migration_binding_profile=v66b_result.migration_binding_profile,
        reader_projection_manifest=projection_payload,
        semantic_diff_report=v66b_result.semantic_diff_report,
    )

    assert result.compile_report.report_status == "invalid_authority_claim_rejected"
    assert result.compile_report.advisory_result.recommended_adoption_posture_or_none is None


def test_v66c_invalidates_hash_mismatch_against_shipped_v66a_basis(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result, v66b_result = _build_v66b_basis(root)
    migration_payload = v66b_result.migration_binding_profile.model_dump(mode="json")
    migration_payload["consumed_source_set_manifest_hash"] = "deadbeef"

    result = check_v66c_anm_adoption_hardening(
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        migration_binding_profile=migration_payload,
        reader_projection_manifest=v66b_result.reader_projection_manifest,
        semantic_diff_report=v66b_result.semantic_diff_report,
    )

    assert result.compile_report.report_status == "invalid_prior_basis_hash_mismatch"
    assert result.compile_report.advisory_result.recommended_adoption_posture_or_none is None


def test_v66c_compile_report_uses_recomputed_invalid_status_reason_code(tmp_path: Path) -> None:
    root = tmp_path
    v66a_result, v66b_result = _build_v66b_basis(root)
    notice_set, diagnostics = build_v66c_prose_boundary_notice_set(
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        migration_binding_profile=v66b_result.migration_binding_profile,
        reader_projection_manifest=v66b_result.reader_projection_manifest,
        semantic_diff_report=v66b_result.semantic_diff_report,
    )
    notice_payload = notice_set.model_dump(mode="json")
    notice_payload["consumed_lineage"]["consumed_v66b_migration_binding_profile_hash"] = "deadbeef"

    report = build_v66c_compile_report(
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        migration_binding_profile=v66b_result.migration_binding_profile,
        reader_projection_manifest=v66b_result.reader_projection_manifest,
        semantic_diff_report=v66b_result.semantic_diff_report,
        prose_boundary_notice_set=notice_payload,
        structural_diagnostics=diagnostics,
    )

    assert report.report_status == "invalid_prior_basis_hash_mismatch"
    assert report.advisory_result.reason_codes == ["ANM_V66C_INVALID_PRIOR_BASIS"]
    assert report.advisory_result.recommended_adoption_posture_or_none is None


def test_v66c_policy_anchor_fallback_returns_diagnostic(monkeypatch) -> None:
    def _raise_policy_error():
        raise ValueError("broken policy anchor")

    monkeypatch.setattr(anm_adoption, "_policy_anchor", _raise_policy_error)

    fallback, diagnostics = anm_adoption._build_policy_anchor_or_diagnostic()

    assert fallback.policy_anchor_ref == "anm_v66c_policy_anchor:starter"
    assert diagnostics[0].diagnostic_kind == "policy_anchor_invalid"


def test_v66c_emits_transition_review_candidate_only_with_explicit_transition_law(
    tmp_path: Path,
) -> None:
    root = tmp_path
    v66a_result, v66b_result = _build_v66b_basis(root, with_transition_law=True)

    result = check_v66c_anm_adoption_hardening(
        manifest=v66a_result.manifest,
        authority_profiles=v66a_result.authority_profiles,
        class_policy=v66a_result.class_policy,
        migration_binding_profile=v66b_result.migration_binding_profile,
        reader_projection_manifest=v66b_result.reader_projection_manifest,
        semantic_diff_report=v66b_result.semantic_diff_report,
    )

    assert result.compile_report.report_status == "valid"
    assert (
        result.compile_report.advisory_result.recommended_adoption_posture_or_none
        == "candidate_for_later_markdown_transition_review"
    )
