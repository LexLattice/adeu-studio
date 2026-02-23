from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from adeu_api.cross_ir_bridge_vnext_plus20 import (
    build_cross_ir_bridge_manifest_vnext_plus20,
    canonical_bridge_manifest_hash_vnext_plus20,
)
from adeu_api.cross_ir_coherence_vnext_plus20 import (
    build_cross_ir_coherence_diagnostics_vnext_plus20,
    build_cross_ir_quality_projection_vnext_plus20,
)
from adeu_api.hashing import canonical_json, sha256_text


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


def _issue_sort_key(issue: dict[str, Any]) -> tuple[str, str, str, str]:
    concept_refs = issue.get("concept_refs", [])
    core_ir_refs = issue.get("core_ir_refs", [])
    return (
        str(issue.get("issue_code", "")),
        str(concept_refs[0]) if concept_refs else "",
        str(core_ir_refs[0]) if core_ir_refs else "",
        str(issue.get("issue_id", "")),
    )


def test_build_cross_ir_coherence_is_deterministic_and_hashes_bridge_manifest() -> None:
    first = build_cross_ir_coherence_diagnostics_vnext_plus20(**_vnext_plus20_pair())
    second = build_cross_ir_coherence_diagnostics_vnext_plus20(**_vnext_plus20_pair())
    bridge_manifest = build_cross_ir_bridge_manifest_vnext_plus20(**_vnext_plus20_pair())

    assert first["schema"] == "adeu_cross_ir_coherence_diagnostics@0.1"
    assert first["bridge_manifest_hash"] == canonical_bridge_manifest_hash_vnext_plus20(
        bridge_manifest
    )
    assert first["issue_summary"]["total_issues"] == len(first["issues"])
    assert first["issues"] == sorted(first["issues"], key=_issue_sort_key)
    assert list(first["issue_summary"]["counts_by_code"].keys()) == sorted(
        first["issue_summary"]["counts_by_code"].keys()
    )
    assert list(first["issue_summary"]["counts_by_severity"].keys()) == sorted(
        first["issue_summary"]["counts_by_severity"].keys()
    )
    assert canonical_json(first) == canonical_json(second)

    for issue in first["issues"]:
        concept_refs = sorted(issue["concept_refs"])
        core_ir_refs = sorted(issue["core_ir_refs"])
        assert issue["concept_refs"] == concept_refs
        assert issue["core_ir_refs"] == core_ir_refs
        expected_issue_id = sha256_text(
            canonical_json(
                {
                    "issue_code": issue["issue_code"],
                    "concept_refs": concept_refs,
                    "core_ir_refs": core_ir_refs,
                    "evidence": issue["evidence"],
                }
            )
        )[:16]
        assert issue["issue_id"] == expected_issue_id

        if issue["evidence"]["kind"] == "topology":
            expected_relation_key = sha256_text(
                canonical_json(
                    {
                        "concept_relation_ref": issue["evidence"]["concept_relation_ref"],
                        "core_ir_relation_ref": issue["evidence"].get("core_ir_relation_ref") or "",
                    }
                )
            )[:16]
            assert issue["evidence"]["relation_key"] == expected_relation_key


def test_build_cross_ir_coherence_emits_claim_projection_gap_for_non_claimlike_mapping(
    tmp_path: Path,
) -> None:
    source_catalog_path = (
        _repo_root() / "apps" / "api" / "fixtures" / "cross_ir" / "vnext_plus20_catalog.json"
    )
    catalog_payload = json.loads(source_catalog_path.read_text(encoding="utf-8"))
    _absolutize_catalog_artifact_paths(payload=catalog_payload, catalog_path=source_catalog_path)

    concept_fixture_path = (
        _repo_root() / "apps" / "api" / "fixtures" / "cross_ir" / "concept_case_a_1.json"
    )
    concept_payload = json.loads(concept_fixture_path.read_text(encoding="utf-8"))
    concept_payload["claims"][0]["id"] = "q1"
    patched_concept_path = tmp_path / "concept_case_a_1_claim_gap.json"
    patched_concept_path.write_text(json.dumps(concept_payload), encoding="utf-8")

    for artifact_ref in catalog_payload["artifact_refs"]:
        if artifact_ref["artifact_ref_id"] == "concept.case_a_1":
            artifact_ref["path"] = str(patched_concept_path)

    patched_catalog_path = tmp_path / "vnext_plus20_catalog_claim_gap.json"
    patched_catalog_path.write_text(json.dumps(catalog_payload), encoding="utf-8")

    diagnostics = build_cross_ir_coherence_diagnostics_vnext_plus20(
        **_vnext_plus20_pair(),
        catalog_path=patched_catalog_path,
    )
    gaps = [
        issue
        for issue in diagnostics["issues"]
        if issue["issue_code"] == "CLAIM_PROJECTION_GAP"
    ]
    assert len(gaps) == 1
    gap = gaps[0]
    assert gap["severity"] == "error"
    assert gap["concept_refs"] == ["q1"]
    assert gap["core_ir_refs"] == ["q1"]
    assert gap["evidence"]["kind"] == "bridge_entry"


def test_build_cross_ir_coherence_emits_link_kind_drift_for_excepts_mapping(
    tmp_path: Path,
) -> None:
    source_text_hash = "b" * 64
    concept_artifact_id = "concept.link_drift"
    core_ir_artifact_id = "core_ir.link_drift"

    concept_payload = {
        "schema_version": "adeu.concepts.v0",
        "concept_id": concept_artifact_id,
        "context": {"doc_id": "doc.link_drift", "domain_tags": []},
        "terms": [],
        "senses": [],
        "claims": [],
        "links": [
            {
                "id": "edge:excepts:d_exception:d_norm",
                "kind": "commitment",
                "src_sense_id": "s1",
                "dst_sense_id": "s2",
            }
        ],
        "ambiguity": [],
        "bridges": [],
    }
    core_payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": source_text_hash,
        "source_text": "link drift fixture",
        "nodes": [
            {"id": "d_exception", "layer": "D", "kind": "Exception", "label": "x"},
            {"id": "d_norm", "layer": "D", "kind": "Norm", "label": "y"},
        ],
        "edges": [
            {"type": "excepts", "from": "d_exception", "to": "d_norm"},
        ],
    }
    concept_path = tmp_path / "concept_link_drift.json"
    core_path = tmp_path / "core_link_drift.json"
    concept_path.write_text(json.dumps(concept_payload), encoding="utf-8")
    core_path.write_text(json.dumps(core_payload), encoding="utf-8")

    catalog_payload = {
        "schema": "cross_ir.vnext_plus20_catalog@1",
        "artifact_refs": [
            {
                "artifact_ref_id": concept_artifact_id,
                "schema": "adeu.concepts.v0",
                "path": str(concept_path),
            },
            {
                "artifact_ref_id": core_ir_artifact_id,
                "schema": "adeu_core_ir@0.1",
                "path": str(core_path),
            },
        ],
        "entries": [
            {
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "bridge_mapping_version": "adeu_to_concepts.v1",
                "mapping_hash": "1" * 64,
                "intentional_concept_only_object_ids": [],
                "intentional_core_ir_only_object_ids": ["d_exception", "d_norm"],
            }
        ],
    }
    catalog_path = tmp_path / "vnext_plus20_catalog_link_drift.json"
    catalog_path.write_text(json.dumps(catalog_payload), encoding="utf-8")

    diagnostics = build_cross_ir_coherence_diagnostics_vnext_plus20(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        catalog_path=catalog_path,
    )
    codes = [issue["issue_code"] for issue in diagnostics["issues"]]
    assert "LINK_KIND_DRIFT" in codes
    link_issue = next(
        issue
        for issue in diagnostics["issues"]
        if issue["issue_code"] == "LINK_KIND_DRIFT"
    )
    assert link_issue["severity"] == "warn"
    assert link_issue["concept_refs"] == ["edge:excepts:d_exception:d_norm"]
    assert link_issue["core_ir_refs"] == ["edge:excepts:d_exception:d_norm"]
    assert link_issue["evidence"]["kind"] == "bridge_entry"


def test_build_cross_ir_quality_projection_matches_coherence_counts() -> None:
    coherence = build_cross_ir_coherence_diagnostics_vnext_plus20(**_vnext_plus20_pair())
    quality = build_cross_ir_quality_projection_vnext_plus20(**_vnext_plus20_pair())

    assert quality["schema"] == "cross_ir_quality_projection.vnext_plus20@1"
    assert quality["bridge_pair_count"] == 1
    assert quality["coherence_issue_count"] == coherence["issue_summary"]["total_issues"]
    assert quality["coherence_counts_by_code"] == coherence["issue_summary"]["counts_by_code"]
    assert quality["coherence_counts_by_severity"] == coherence["issue_summary"][
        "counts_by_severity"
    ]
