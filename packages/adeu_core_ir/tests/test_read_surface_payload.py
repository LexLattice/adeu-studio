from __future__ import annotations

import pytest
from adeu_core_ir import (
    FROZEN_READ_SURFACE_INTEGRITY_FAMILIES,
    AdeuReadSurfacePayload,
    canonicalize_read_surface_payload,
)


def _minimal_payload() -> dict:
    source_text_hash = "hash-minimal-read-surface"
    return {
        "schema": "adeu_read_surface_payload@0.1",
        "artifact_id": "core_ir.minimal",
        "source_text_hash": source_text_hash,
        "core_ir": {
            "schema": "adeu_core_ir@0.1",
            "source_text_hash": source_text_hash,
            "nodes": [
                {
                    "id": "o1",
                    "layer": "O",
                    "kind": "Concept",
                    "label": "minimal",
                }
            ],
            "edges": [],
        },
        "lane_projection": {
            "schema": "adeu_lane_projection@0.1",
            "source_text_hash": source_text_hash,
            "lanes": {"O": ["o1"], "E": [], "D": [], "U": []},
            "edges": [],
        },
        "lane_report": {
            "schema": "adeu_lane_report@0.1",
            "source_text_hash": source_text_hash,
            "lane_nodes": {"O": ["o1"], "E": [], "D": [], "U": []},
            "lane_edge_counts": {"O": 0, "E": 0, "D": 0, "U": 0},
        },
        "integrity": {
            family: {"artifact": None, "missing_reason": "ARTIFACT_NOT_FOUND"}
            for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES
        },
        "render_summary": {
            "core_ir_node_count": 1,
            "core_ir_edge_count": 0,
            "lane_projection_edge_count": 0,
            "lane_node_counts": {"O": 1, "E": 0, "D": 0, "U": 0},
            "lane_edge_counts": {"O": 0, "E": 0, "D": 0, "U": 0},
            "integrity_present_family_count": 0,
            "integrity_missing_family_count": len(FROZEN_READ_SURFACE_INTEGRITY_FAMILIES),
            "integrity_issue_counts": {
                family: 0 for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES
            },
        },
    }


def test_read_surface_payload_contract_accepts_minimal_payload() -> None:
    payload = _minimal_payload()
    normalized = AdeuReadSurfacePayload.model_validate(payload)
    assert normalized.schema == "adeu_read_surface_payload@0.1"
    assert normalized.artifact_id == "core_ir.minimal"


def test_canonicalize_read_surface_payload_keeps_artifact_null_placeholders() -> None:
    canonical = canonicalize_read_surface_payload(_minimal_payload())
    for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES:
        assert "artifact" in canonical["integrity"][family]
        assert canonical["integrity"][family]["artifact"] is None
        assert canonical["integrity"][family]["missing_reason"] == "ARTIFACT_NOT_FOUND"


def test_read_surface_payload_rejects_integrity_family_order_drift() -> None:
    payload = _minimal_payload()
    first_family = FROZEN_READ_SURFACE_INTEGRITY_FAMILIES[0]
    last_family = FROZEN_READ_SURFACE_INTEGRITY_FAMILIES[-1]
    payload["integrity"] = {
        last_family: payload["integrity"][last_family],
        **{
            family: payload["integrity"][family]
            for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES[1:-1]
        },
        first_family: payload["integrity"][first_family],
    }
    with pytest.raises(ValueError, match="frozen family keys"):
        AdeuReadSurfacePayload.model_validate(payload)

