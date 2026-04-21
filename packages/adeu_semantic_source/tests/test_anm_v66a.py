from __future__ import annotations

import pytest
from adeu_semantic_source import (
    AnmCompileError,
    build_v66a_doc_authority_profile,
    inspect_v66a_source,
)


def test_v66a_inspect_ignores_code_fenced_d1_examples() -> None:
    source_text = """
```markdown
:::D@1 id=example_only
ON artifact.emitted[*]
@example MUST REQUIRED snapshot.identity
:::
```
""".strip()

    inspected = inspect_v66a_source(source_text=source_text)

    assert inspected["explicit_profile"] is None
    assert inspected["has_recognized_d1_blocks"] is False


def test_v66a_builds_authority_profile_from_explicit_profile_block() -> None:
    source_text = """
---
doc_id: adeu.lock.vnext_plus182
doc_class: lock
authority_layer: lock
---

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

:::D@1 id=release_surface
ON artifact.emitted[*]
@identity MUST REQUIRED snapshot.identity
:::
""".strip()

    profile = build_v66a_doc_authority_profile(
        source_text=source_text,
        source_doc_ref="docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
        doc_id="adeu.lock.vnext_plus182",
        doc_class="lock",
        authority_layer="lock",
        source_posture="legacy_markdown",
        lifecycle_status="living",
        allowed_authority_blocks=["D@1", "adeu.doc_profile@1"],
        allowed_outputs=[
            "anm_doc_authority_profile@1",
            "d1_normalized_ir@1",
            "policy_obligation_ledger@1",
        ],
        forbidden_outputs=[],
        current_markdown_authority_relation="current_markdown_controlling",
        allowed_consumers=["semantic_compiler", "semantic_source"],
        requires_transition_law_for_supersession=True,
    )

    assert profile.doc_id == "adeu.lock.vnext_plus182"
    assert profile.allowed_authority_blocks == ["D@1", "adeu.doc_profile@1"]


def test_v66a_rejects_explicit_profile_mismatch() -> None:
    source_text = """
:::adeu.doc_profile@1
schema: anm_doc_authority_profile@1
doc_id: adeu.lock.vnext_plus182
doc_class: planning
authority_layer: planning
source_posture: legacy_markdown
allowed_authority_blocks:
- adeu.doc_profile@1
:::
""".strip()

    with pytest.raises(AnmCompileError, match="explicit profile doc_class must match"):
        build_v66a_doc_authority_profile(
            source_text=source_text,
            source_doc_ref="docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
            doc_id="adeu.lock.vnext_plus182",
            doc_class="lock",
            authority_layer="lock",
            source_posture="legacy_markdown",
            lifecycle_status="living",
            allowed_authority_blocks=["adeu.doc_profile@1"],
            allowed_outputs=["anm_doc_authority_profile@1"],
            forbidden_outputs=[],
            current_markdown_authority_relation="current_markdown_controlling",
            allowed_consumers=["semantic_compiler"],
            requires_transition_law_for_supersession=True,
        )
