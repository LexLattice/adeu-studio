from __future__ import annotations

import json
from pathlib import Path

import adeu_api.main as api_main
import pytest
from adeu_api.hashing import canonical_json
from adeu_api.read_surface_payload_vnext_plus19 import (
    ReadSurfacePayloadVnextPlus19Error,
    build_read_surface_payload_vnext_plus19,
)
from adeu_core_ir import FROZEN_READ_SURFACE_INTEGRITY_FAMILIES


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


@pytest.fixture(autouse=True)
def _clear_read_surface_catalog_cache() -> None:
    api_main._read_surface_catalog_index.cache_clear()
    yield
    api_main._read_surface_catalog_index.cache_clear()


def test_build_read_surface_payload_is_deterministic() -> None:
    first = build_read_surface_payload_vnext_plus19(artifact_id="core_ir.case_a_1")
    second = build_read_surface_payload_vnext_plus19(artifact_id="core_ir.case_a_1")

    assert first["schema"] == "adeu_read_surface_payload@0.1"
    assert first["artifact_id"] == "core_ir.case_a_1"
    assert canonical_json(first) == canonical_json(second)
    assert list(first["integrity"].keys()) == list(FROZEN_READ_SURFACE_INTEGRITY_FAMILIES)

    summary = first["render_summary"]
    assert summary["core_ir_node_count"] == 7
    assert summary["core_ir_edge_count"] == 8
    assert summary["lane_projection_edge_count"] == 8
    assert summary["lane_node_counts"] == {"O": 1, "E": 4, "D": 1, "U": 1}
    assert summary["lane_edge_counts"] == {"O": 0, "E": 7, "D": 1, "U": 0}
    assert summary["integrity_present_family_count"] == 6
    assert summary["integrity_missing_family_count"] == 0
    assert summary["integrity_issue_counts"] == {
        "dangling_reference": 2,
        "cycle_policy": 2,
        "deontic_conflict": 1,
        "reference_integrity_extended": 3,
        "cycle_policy_extended": 3,
        "deontic_conflict_extended": 2,
    }


def test_build_read_surface_payload_with_correlations_is_node_keyed() -> None:
    payload = build_read_surface_payload_vnext_plus19(
        artifact_id="core_ir.case_a_1",
        include_correlations=True,
    )
    assert "correlations" in payload
    correlations = payload["correlations"]
    node_ids = sorted(node["id"] for node in payload["core_ir"]["nodes"])
    assert list(correlations.keys()) == node_ids
    assert correlations["c1"]["lane_refs"] == [
        {"source": "lane_projection", "lane": "E"},
        {"source": "lane_report", "lane": "E"},
    ]


def test_build_read_surface_payload_uses_missing_integrity_placeholder(
    tmp_path: Path,
) -> None:
    catalog_path = (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "read_surface"
        / "vnext_plus19_catalog.json"
    )
    catalog_dir = catalog_path.parent
    catalog_payload = json.loads(catalog_path.read_text(encoding="utf-8"))
    artifact_refs = []
    for artifact_ref in catalog_payload["artifact_refs"]:
        if artifact_ref["schema"] == "adeu_integrity_cycle_policy_extended@0.1":
            continue
        artifact_path = Path(str(artifact_ref["path"]))
        if not artifact_path.is_absolute():
            artifact_ref["path"] = str((catalog_dir / artifact_path).resolve())
        artifact_refs.append(artifact_ref)
    catalog_payload["artifact_refs"] = artifact_refs
    for entry in catalog_payload["entries"]:
        entry["parent_links"].pop("adeu_integrity_cycle_policy_extended@0.1", None)

    patched_catalog = tmp_path / "vnext_plus19_catalog.json"
    patched_catalog.write_text(json.dumps(catalog_payload), encoding="utf-8")

    payload = build_read_surface_payload_vnext_plus19(
        artifact_id="core_ir.case_a_1",
        catalog_path=patched_catalog,
    )
    placeholder = payload["integrity"]["cycle_policy_extended"]
    assert placeholder["artifact"] is None
    assert placeholder["missing_reason"] == "ARTIFACT_NOT_FOUND"
    assert payload["render_summary"]["integrity_present_family_count"] == 5
    assert payload["render_summary"]["integrity_missing_family_count"] == 1


def test_build_read_surface_payload_rejects_unknown_artifact_id() -> None:
    with pytest.raises(
        ReadSurfacePayloadVnextPlus19Error,
        match="URM_ADEU_READ_SURFACE_ARTIFACT_NOT_FOUND",
    ):
        build_read_surface_payload_vnext_plus19(artifact_id="core_ir.missing")
