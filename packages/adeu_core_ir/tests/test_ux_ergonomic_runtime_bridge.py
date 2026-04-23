from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    UXErgonomicRuntimeMeasurementEvidence,
    canonicalize_computed_ux_ergonomic_runtime_bridge_report_payload,
    canonicalize_ux_ergonomic_runtime_bridge_report_payload,
    canonicalize_ux_ergonomic_runtime_measurement_evidence_payload,
    evaluate_ux_ergonomic_runtime_bridge,
)
from adeu_ir.repo import repo_root


def _ux_ergonomics_root(version: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_ergonomics" / version


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_v67c_reference_runtime_measurement_evidence_canonicalizes() -> None:
    payload = _load_json(
        _ux_ergonomics_root("vnext_plus187")
        / "ux_ergonomic_runtime_measurement_evidence_artifact_inspector_maximized_reference.json"
    )

    assert canonicalize_ux_ergonomic_runtime_measurement_evidence_payload(payload) == payload


def test_v67c_reference_bridge_report_matches_computed_fixture() -> None:
    payload = _load_json(
        _ux_ergonomics_root("vnext_plus187")
        / "ux_ergonomic_runtime_measurement_evidence_artifact_inspector_maximized_reference.json"
    )
    runtime_measurement_evidence = UXErgonomicRuntimeMeasurementEvidence.model_validate(payload)
    expected = _load_json(
        _ux_ergonomics_root("vnext_plus187")
        / "ux_ergonomic_runtime_bridge_report_artifact_inspector_maximized_computed_reference.json"
    )

    assert (
        canonicalize_computed_ux_ergonomic_runtime_bridge_report_payload(
            runtime_measurement_evidence=runtime_measurement_evidence
        )
        == expected
    )


def test_v67c_missing_required_measurement_yields_advisory_incomplete() -> None:
    payload = _load_json(
        _ux_ergonomics_root("vnext_plus187")
        / "ux_ergonomic_runtime_measurement_evidence_artifact_inspector_maximized_reference.json"
    )
    payload["measurement_rows"] = [
        row
        for row in payload["measurement_rows"]  # type: ignore[index]
        if row["component_ref"] != "action_cluster:commit-actions"
    ]
    runtime_measurement_evidence = UXErgonomicRuntimeMeasurementEvidence.model_validate(payload)

    report = evaluate_ux_ergonomic_runtime_bridge(
        runtime_measurement_evidence=runtime_measurement_evidence
    )

    assert report.bridge_status == "advisory_incomplete_missing_evidence"
    mismatch_families = {row.mismatch_family for row in report.mismatch_rows}
    assert "runtime_missing_measurement_for_required_obligation" in mismatch_families


def test_v67c_runtime_targetability_below_floor_yields_advisory_drift() -> None:
    payload = _load_json(
        _ux_ergonomics_root("vnext_plus187")
        / "ux_ergonomic_runtime_measurement_evidence_artifact_inspector_maximized_reference.json"
    )
    for row in payload["measurement_rows"]:  # type: ignore[index]
        if row["component_ref"] == "action_cluster:commit-actions":
            row["measured_bounding_box_css_px"]["width"] = 36
            row["measured_bounding_box_css_px"]["height"] = 36
            break
    runtime_measurement_evidence = UXErgonomicRuntimeMeasurementEvidence.model_validate(payload)

    report = evaluate_ux_ergonomic_runtime_bridge(
        runtime_measurement_evidence=runtime_measurement_evidence
    )

    assert report.bridge_status == "advisory_drift_detected"
    mismatch_families = {row.mismatch_family for row in report.mismatch_rows}
    assert "runtime_targetability_below_adjudicated_floor" in mismatch_families


def test_v67c_source_hash_mismatch_yields_invalid_basis_mismatch() -> None:
    payload = _load_json(
        _ux_ergonomics_root("vnext_plus187")
        / "ux_ergonomic_runtime_measurement_evidence_artifact_inspector_maximized_reference.json"
    )
    payload["source_artifact_hashes"][0]["artifact_hash"] = "0" * 64  # type: ignore[index]
    runtime_measurement_evidence = UXErgonomicRuntimeMeasurementEvidence.model_validate(payload)

    report = evaluate_ux_ergonomic_runtime_bridge(
        runtime_measurement_evidence=runtime_measurement_evidence
    )

    assert report.bridge_status == "invalid_basis_mismatch"
    assert [row.mismatch_family for row in report.mismatch_rows] == ["runtime_source_hash_mismatch"]


def test_v67c_reject_runtime_measurement_evidence_candidate_mismatch() -> None:
    payload = _load_json(
        _ux_ergonomics_root("vnext_plus187")
        / "reject_ux_ergonomic_runtime_measurement_evidence_candidate_mismatch.json"
    )

    with pytest.raises(ValueError, match="candidate_profile_id"):
        canonicalize_ux_ergonomic_runtime_measurement_evidence_payload(payload)


def test_v67c_reject_bridge_report_clean_with_mismatch_rows() -> None:
    payload = _load_json(
        _ux_ergonomics_root("vnext_plus187")
        / "reject_ux_ergonomic_runtime_bridge_report_clean_with_mismatch_rows.json"
    )

    with pytest.raises(ValueError, match="advisory_clean"):
        canonicalize_ux_ergonomic_runtime_bridge_report_payload(payload)
