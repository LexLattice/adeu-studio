from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_api.cross_ir_bridge_vnext_plus20 import (
    CrossIRBridgeVnextPlus20Error,
    build_cross_ir_bridge_manifest_vnext_plus20,
    canonical_bridge_manifest_hash_vnext_plus20,
    list_cross_ir_catalog_pairs_vnext_plus20,
)
from adeu_api.hashing import canonical_json


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _vnext_plus20_pair() -> dict[str, str]:
    return {
        "source_text_hash": "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa",
        "core_ir_artifact_id": "core_ir.case_a_1",
        "concept_artifact_id": "concept.case_a_1",
    }


def _absolutize_catalog_artifact_paths(
    *,
    payload: dict[str, object],
    catalog_path: Path,
) -> None:
    catalog_dir = catalog_path.parent
    artifact_refs = payload.get("artifact_refs")
    if not isinstance(artifact_refs, list):
        return
    for artifact_ref in artifact_refs:
        if not isinstance(artifact_ref, dict):
            continue
        artifact_path_value = artifact_ref.get("path")
        if not isinstance(artifact_path_value, str):
            continue
        artifact_path = Path(artifact_path_value)
        if artifact_path.is_absolute():
            continue
        artifact_ref["path"] = str((catalog_dir / artifact_path).resolve())


def test_list_cross_ir_catalog_pairs_is_sorted_and_complete() -> None:
    assert list_cross_ir_catalog_pairs_vnext_plus20() == [_vnext_plus20_pair()]


def test_build_cross_ir_bridge_manifest_is_deterministic() -> None:
    first = build_cross_ir_bridge_manifest_vnext_plus20(**_vnext_plus20_pair())
    second = build_cross_ir_bridge_manifest_vnext_plus20(**_vnext_plus20_pair())

    assert first["schema"] == "adeu_cross_ir_bridge_manifest@0.1"
    assert first["bridge_mapping_version"] == "adeu_to_concepts.v1"
    assert (
        first["mapping_hash"]
        == "5f2a9f84df19e1f8d43167f2d5190054f2cf07f4b0232f918f6e6f95be939eb3"
    )
    assert first["created_at"] == "2026-02-01T00:00:00Z"
    assert first["unmapped_concept_objects"] == ["amb1"]
    assert "u1" in first["unmapped_core_ir_objects"]

    mapped_entries = [entry for entry in first["entries"] if entry["mapping_status"] == "mapped"]
    assert any(
        entry["concept_object_id"] == "o1" and entry["core_ir_object_id"] == "o1"
        for entry in mapped_entries
    )
    assert any(
        entry["concept_object_id"] == "edge:supports:e1:c1"
        and entry["core_ir_object_id"] == "edge:supports:e1:c1"
        and entry["core_ir_kind"] == "edge_signature"
        for entry in mapped_entries
    )

    assert canonical_json(first) == canonical_json(second)


def test_build_cross_ir_bridge_manifest_unknown_pair_fails_closed() -> None:
    with pytest.raises(CrossIRBridgeVnextPlus20Error) as exc_info:
        build_cross_ir_bridge_manifest_vnext_plus20(
            source_text_hash="0" * 64,
            core_ir_artifact_id="core_ir.case_a_1",
            concept_artifact_id="concept.case_a_1",
        )

    assert exc_info.value.code == "URM_ADEU_CROSS_IR_ARTIFACT_NOT_FOUND"


def test_build_cross_ir_bridge_manifest_fails_when_catalog_core_hash_mismatches(
    tmp_path: Path,
) -> None:
    catalog_path = (
        _repo_root() / "apps" / "api" / "fixtures" / "cross_ir" / "vnext_plus20_catalog.json"
    )
    payload = json.loads(catalog_path.read_text(encoding="utf-8"))
    _absolutize_catalog_artifact_paths(payload=payload, catalog_path=catalog_path)
    payload["entries"][0]["source_text_hash"] = "f" * 64

    patched_catalog_path = tmp_path / "vnext_plus20_catalog.json"
    patched_catalog_path.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(CrossIRBridgeVnextPlus20Error) as exc_info:
        build_cross_ir_bridge_manifest_vnext_plus20(
            source_text_hash="f" * 64,
            core_ir_artifact_id="core_ir.case_a_1",
            concept_artifact_id="concept.case_a_1",
            catalog_path=patched_catalog_path,
        )

    assert exc_info.value.code == "URM_ADEU_CROSS_IR_FIXTURE_INVALID"


def test_canonical_bridge_manifest_hash_excludes_mapping_hash_and_created_at() -> None:
    manifest = build_cross_ir_bridge_manifest_vnext_plus20(**_vnext_plus20_pair())
    baseline_hash = canonical_bridge_manifest_hash_vnext_plus20(manifest)

    mutated = dict(manifest)
    mutated["mapping_hash"] = "0" * 64
    mutated["created_at"] = "2030-01-01T00:00:00Z"

    assert canonical_bridge_manifest_hash_vnext_plus20(mutated) == baseline_hash


def test_build_cross_ir_bridge_manifest_fails_when_intentional_allowlist_drifts(
    tmp_path: Path,
) -> None:
    catalog_path = (
        _repo_root() / "apps" / "api" / "fixtures" / "cross_ir" / "vnext_plus20_catalog.json"
    )
    payload = json.loads(catalog_path.read_text(encoding="utf-8"))
    _absolutize_catalog_artifact_paths(payload=payload, catalog_path=catalog_path)
    payload["entries"][0]["intentional_core_ir_only_object_ids"] = ["not_in_unmapped_set"]

    patched_catalog_path = tmp_path / "vnext_plus20_catalog.json"
    patched_catalog_path.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(CrossIRBridgeVnextPlus20Error) as exc_info:
        build_cross_ir_bridge_manifest_vnext_plus20(
            source_text_hash="3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa",
            core_ir_artifact_id="core_ir.case_a_1",
            concept_artifact_id="concept.case_a_1",
            catalog_path=patched_catalog_path,
        )

    assert exc_info.value.code == "URM_ADEU_CROSS_IR_FIXTURE_INVALID"
    assert exc_info.value.context["missing_intentional_core_ir_only_object_ids"] == [
        "not_in_unmapped_set"
    ]
