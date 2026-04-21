from __future__ import annotations

from pathlib import Path

import pytest
from adeu_semantic_compiler import check_v66a_anm_source_set
from adeu_semantic_source import AnmCompileError


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def test_v66a_inventory_builds_manifest_profiles_and_policy(tmp_path: Path) -> None:
    root = tmp_path
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
""".strip(),
    )
    _write(
        root / "docs" / "overlays" / "LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md",
        """
:::D@1 id=overlay_surface
ON artifact.emitted[*]
@identity MUST REQUIRED snapshot.identity
:::
""".strip(),
    )
    _write(
        root / "docs" / "support" / "notes.md",
        """
```markdown
:::D@1 id=example_only
ON artifact.emitted[*]
@example MUST REQUIRED snapshot.identity
:::
```
""".strip(),
    )

    result = check_v66a_anm_source_set(
        repo_root_path=root,
        registered_entries=[
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
        ],
    )

    assert result.discovered_doc_inventory == [
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
        "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md",
        "docs/support/notes.md",
    ]
    assert result.governed_anm_source_set == [
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
        "docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md",
    ]
    assert (
        [entry.doc_ref for entry in result.manifest.source_entries]
        == result.governed_anm_source_set
    )
    assert (
        [profile.doc_ref for profile in result.authority_profiles]
        == result.governed_anm_source_set
    )
    assert len(result.class_policy.policy_rows) == 5


def test_v66a_inventory_rejects_unregistered_companion_overlay(tmp_path: Path) -> None:
    root = tmp_path
    _write(
        root / "docs" / "overlays" / "LOCKED_CONTINUATION_vNEXT_PLUS182.anm.adeu.md",
        """
:::D@1 id=overlay_surface
ON artifact.emitted[*]
@identity MUST REQUIRED snapshot.identity
:::
""".strip(),
    )

    with pytest.raises(AnmCompileError, match="unregistered companion posture"):
        check_v66a_anm_source_set(repo_root_path=root)


def test_v66a_inventory_rejects_explicit_registered_profile_drift(tmp_path: Path) -> None:
    root = tmp_path
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
""".strip(),
    )

    with pytest.raises(AnmCompileError, match="contradictory profile sources"):
        check_v66a_anm_source_set(
            repo_root_path=root,
            registered_entries=[
                {
                    "doc_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
                    "doc_id_or_none": "adeu.lock.vnext_plus182",
                    "doc_class": "planning",
                    "authority_layer": "lock",
                    "source_posture": "legacy_markdown",
                    "lifecycle_status": "living",
                    "classification_status": "classified",
                    "companion_registration_status_or_none": "registered_host_document",
                }
            ],
        )


def test_v66a_inventory_rejects_symlinked_discovered_doc_path(tmp_path: Path) -> None:
    root = tmp_path
    real_doc = root / "real.md"
    real_doc.write_text("# outside\n", encoding="utf-8")
    docs_dir = root / "docs"
    docs_dir.mkdir()
    (docs_dir / "linked.md").symlink_to(real_doc)

    with pytest.raises(AnmCompileError, match="contains a symlinked component"):
        check_v66a_anm_source_set(repo_root_path=root)
