from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_commitments_ir import AnmMarkdownCoexistenceProfile
from adeu_semantic_source import (
    AnmCompileError,
    build_v47d_selector_predicate_ownership_profile,
    compile_authoritative_normative_markdown,
    default_bootstrap_predicate_contracts,
)


def _fixture_path_v47c(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47c" / name


def _fixture_path_v47d(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47d" / name


def _read_text_v47c(name: str) -> str:
    return _fixture_path_v47c(name).read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_spec_v47d(name: str) -> dict[str, object]:
    return _read_json(_fixture_path_v47d(name))


def _read_commitments_fixture_v47d(name: str) -> dict[str, object]:
    path = (
        Path(__file__).resolve().parents[2]
        / "adeu_commitments_ir"
        / "tests"
        / "fixtures"
        / "v47d"
        / name
    )
    return _read_json(path)


def _reference_d1_ir():
    return compile_authoritative_normative_markdown(
        source_text=_read_text_v47c("standalone_policy.adeu.md"),
        source_doc_ref="packages/adeu_semantic_source/tests/fixtures/v47c/standalone_policy.adeu.md",
    )


def _reference_coexistence_profile() -> AnmMarkdownCoexistenceProfile:
    fixture = (
        Path(__file__).resolve().parents[2]
        / "adeu_commitments_ir"
        / "tests"
        / "fixtures"
        / "v47c"
        / "reference_anm_markdown_coexistence_profile.json"
    )
    return AnmMarkdownCoexistenceProfile.model_validate(_read_json(fixture))


def test_v47d_reference_profile_replays_deterministically() -> None:
    spec = _read_spec_v47d("reference_ownership_spec.json")

    profile = build_v47d_selector_predicate_ownership_profile(
        snapshot_id=spec["snapshot_id"],
        source_scope_profile=spec["source_scope_profile"],
        released_stack_refs=spec["released_stack_refs"],
        d1_ir=_reference_d1_ir(),
        predicate_contracts=default_bootstrap_predicate_contracts(),
        coexistence_profile=_reference_coexistence_profile(),
        selector_row_specs=spec["selector_row_specs"],
        predicate_row_specs=spec["predicate_row_specs"],
        compatibility_rule_specs=spec["compatibility_rule_specs"],
        imported_selector_registry=spec["imported_selector_registry"],
        imported_predicate_registry=spec["imported_predicate_registry"],
    )

    assert profile.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47d(
        "reference_anm_selector_predicate_ownership_profile.json"
    )


def test_v47d_bootstrap_only_profile_preserves_released_replay() -> None:
    spec = _read_spec_v47d("bootstrap_only_ownership_spec.json")

    profile = build_v47d_selector_predicate_ownership_profile(
        snapshot_id=spec["snapshot_id"],
        source_scope_profile=spec["source_scope_profile"],
        released_stack_refs=spec["released_stack_refs"],
        d1_ir=_reference_d1_ir(),
        predicate_contracts=default_bootstrap_predicate_contracts(),
        coexistence_profile=_reference_coexistence_profile(),
        selector_row_specs=spec["selector_row_specs"],
        predicate_row_specs=spec["predicate_row_specs"],
        compatibility_rule_specs=spec["compatibility_rule_specs"],
    )

    assert len(profile.selector_rows) == 1
    assert {row.selector_owner_layer for row in profile.selector_rows} == {"bootstrap"}
    assert {row.selector_ref for row in profile.selector_rows} == {"release_surface:selector"}
    assert len(profile.predicate_rows) == 5
    assert {row.predicate_owner_layer for row in profile.predicate_rows} == {"bootstrap"}
    assert {row.predicate_ref for row in profile.predicate_rows} == {
        "bind_to",
        "cardinality_eq",
        "eq",
        "explicit",
        "present",
    }


def test_v47d_rejects_implicit_selector_promotion() -> None:
    spec = _read_spec_v47d("reject_implicit_selector_promotion_spec.json")

    with pytest.raises(
        AnmCompileError,
        match="imported_o_owned_selector_handle rows require imported_selector_handle_ref",
    ):
        build_v47d_selector_predicate_ownership_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=_reference_d1_ir(),
            predicate_contracts=default_bootstrap_predicate_contracts(),
            coexistence_profile=_reference_coexistence_profile(),
            selector_row_specs=spec["selector_row_specs"],
            predicate_row_specs=spec["predicate_row_specs"],
            compatibility_rule_specs=spec["compatibility_rule_specs"],
            imported_selector_registry=spec.get("imported_selector_registry"),
            imported_predicate_registry=spec.get("imported_predicate_registry"),
        )


def test_v47d_rejects_dangling_imported_selector_handle() -> None:
    spec = _read_spec_v47d("reject_dangling_imported_selector_spec.json")

    with pytest.raises(
        AnmCompileError,
        match="imported selector handle selector-handle:artifact-emitted:v1 is dangling",
    ):
        build_v47d_selector_predicate_ownership_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=_reference_d1_ir(),
            predicate_contracts=default_bootstrap_predicate_contracts(),
            coexistence_profile=_reference_coexistence_profile(),
            selector_row_specs=spec["selector_row_specs"],
            predicate_row_specs=spec["predicate_row_specs"],
            compatibility_rule_specs=spec["compatibility_rule_specs"],
            imported_selector_registry=spec.get("imported_selector_registry"),
            imported_predicate_registry=spec.get("imported_predicate_registry"),
        )


def test_v47d_rejects_incompatible_imported_predicate_version() -> None:
    spec = _read_spec_v47d("reject_incompatible_imported_predicate_version_spec.json")

    with pytest.raises(
        AnmCompileError,
        match=(
            "imported predicate registry ref predicate-registry:present:v2 has incompatible "
            "declared version"
        ),
    ):
        build_v47d_selector_predicate_ownership_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=_reference_d1_ir(),
            predicate_contracts=default_bootstrap_predicate_contracts(),
            coexistence_profile=_reference_coexistence_profile(),
            selector_row_specs=spec["selector_row_specs"],
            predicate_row_specs=spec["predicate_row_specs"],
            compatibility_rule_specs=spec["compatibility_rule_specs"],
            imported_selector_registry=spec.get("imported_selector_registry"),
            imported_predicate_registry=spec.get("imported_predicate_registry"),
        )


def test_v47d_rejects_present_mixed_combination_marked_forbidden() -> None:
    spec = _read_spec_v47d("reference_ownership_spec.json")
    spec["compatibility_rule_specs"][2]["combination_allowed"] = False
    spec["compatibility_rule_specs"][2]["compatibility_posture"] = "mixed_ownership_forbidden"

    with pytest.raises(
        AnmCompileError,
        match=(
            "contradictory mixed ownership posture forbids present combination "
            "imported_o_owned_selector_handle \\+ bootstrap_predicate_contract"
        ),
    ):
        build_v47d_selector_predicate_ownership_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            d1_ir=_reference_d1_ir(),
            predicate_contracts=default_bootstrap_predicate_contracts(),
            coexistence_profile=_reference_coexistence_profile(),
            selector_row_specs=spec["selector_row_specs"],
            predicate_row_specs=spec["predicate_row_specs"],
            compatibility_rule_specs=spec["compatibility_rule_specs"],
            imported_selector_registry=spec.get("imported_selector_registry"),
            imported_predicate_registry=spec.get("imported_predicate_registry"),
        )
