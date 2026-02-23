from __future__ import annotations

import json
from contextlib import nullcontext
from pathlib import Path

import adeu_api.main as api_main
import adeu_api.semantics_v4_candidate_vnext_plus23 as semantics_v4
import pytest
from adeu_api.hashing import canonical_json
from fastapi import HTTPException, Response
from pydantic import BaseModel


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _pair() -> dict[str, str]:
    return {
        "source_text_hash": "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa",
        "core_ir_artifact_id": "core_ir.case_a_1",
        "concept_artifact_id": "concept.case_a_1",
    }


@pytest.fixture(autouse=True)
def _clear_semantics_v4_manifest_caches() -> None:
    semantics_v4._trust_packet_fixture_index_for_manifest.cache_clear()
    semantics_v4._semantics_fixture_index_for_manifest.cache_clear()
    yield
    semantics_v4._trust_packet_fixture_index_for_manifest.cache_clear()
    semantics_v4._semantics_fixture_index_for_manifest.cache_clear()


def _build_packet(**kwargs: str | Path) -> dict[str, object]:
    with semantics_v4.semantics_v4_candidate_non_enforcement_context():
        return semantics_v4.build_semantics_v4_candidate_packet_vnext_plus23(**kwargs)


def _build_projection(
    **kwargs: str | Path,
) -> semantics_v4.SemanticsV4CandidateProjectionVnextPlus23:
    with semantics_v4.semantics_v4_candidate_non_enforcement_context():
        return semantics_v4.build_semantics_v4_candidate_projection_vnext_plus23(**kwargs)


def test_build_semantics_v4_packet_requires_runtime_non_enforcement_context() -> None:
    with pytest.raises(semantics_v4.SemanticsV4CandidateVnextPlus23Error) as exc_info:
        semantics_v4.build_semantics_v4_candidate_packet_vnext_plus23(**_pair())

    assert exc_info.value.code == "URM_ADEU_SEMANTICS_V4_REQUEST_INVALID"
    assert (
        exc_info.value.reason
        == "semantics-v4 candidate runtime non-enforcement context is not active"
    )


def test_build_semantics_v4_projection_requires_runtime_non_enforcement_context() -> None:
    with pytest.raises(semantics_v4.SemanticsV4CandidateVnextPlus23Error) as exc_info:
        semantics_v4.build_semantics_v4_candidate_projection_vnext_plus23()

    assert exc_info.value.code == "URM_ADEU_SEMANTICS_V4_REQUEST_INVALID"
    assert (
        exc_info.value.reason
        == "semantics-v4 candidate runtime non-enforcement context is not active"
    )


def test_build_semantics_v4_packet_is_deterministic_and_schema_valid() -> None:
    first = _build_packet(**_pair())
    second = _build_packet(**_pair())

    assert first["schema"] == "adeu_semantics_v4_candidate_packet@0.1"
    assert canonical_json(first) == canonical_json(second)

    summary = first["comparison_summary"]
    assert summary["total_comparisons"] == 4
    assert summary["compatible_checks"] == 2
    assert summary["drift_checks"] == 2
    assert summary["counts_by_code"] == {
        "ASSURANCE_SET_CONTINUITY_REVIEW": 1,
        "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW": 1,
        "STATUS_SET_CONTINUITY_REVIEW": 1,
        "WITNESS_REF_STRUCTURE_REVIEW": 1,
    }

    items = {item["comparison_code"]: item for item in first["comparison_items"]}
    status_item = items["STATUS_SET_CONTINUITY_REVIEW"]
    assert status_item["status"] == "compatible"
    assert status_item["severity"] == "low"
    assert "expected_hash" not in status_item
    assert "observed_hash" not in status_item

    request_formula_item = items["REQUEST_FORMULA_HASH_CONTINUITY_REVIEW"]
    assert request_formula_item["status"] == "drift"
    assert request_formula_item["severity"] == "high"
    assert isinstance(request_formula_item["expected_hash"], str)
    assert isinstance(request_formula_item["observed_hash"], str)

    witness_item = items["WITNESS_REF_STRUCTURE_REVIEW"]
    assert witness_item["status"] == "drift"
    assert witness_item["severity"] == "medium"
    assert len(witness_item["justification_refs"]) == 3


def test_build_semantics_v4_projection_is_deterministic_and_schema_valid() -> None:
    first = _build_projection().model_dump(mode="json")
    second = _build_projection().model_dump(mode="json")

    assert first["schema"] == "semantics_v4_candidate_projection.vnext_plus23@1"
    assert canonical_json(first) == canonical_json(second)
    assert first["bridge_pair_count"] >= 1
    assert first["comparison_item_count"] == first["bridge_pair_count"] * 4
    assert first["comparison_counts_by_code"] == {
        "ASSURANCE_SET_CONTINUITY_REVIEW": first["bridge_pair_count"],
        "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW": first["bridge_pair_count"],
        "STATUS_SET_CONTINUITY_REVIEW": first["bridge_pair_count"],
        "WITNESS_REF_STRUCTURE_REVIEW": first["bridge_pair_count"],
    }
    assert sum(first["comparison_counts_by_status"].values()) == first["comparison_item_count"]
    assert sum(first["comparison_counts_by_severity"].values()) == first["comparison_item_count"]


def test_semantics_v4_pair_endpoint_returns_packet_and_cache_header() -> None:
    response = Response()
    payload = api_main.get_urm_semantics_v4_pair_endpoint(
        source_text_hash=_pair()["source_text_hash"],
        core_ir_artifact_id=_pair()["core_ir_artifact_id"],
        concept_artifact_id=_pair()["concept_artifact_id"],
        response=response,
    ).model_dump(mode="json")

    assert payload["schema"] == "adeu_semantics_v4_candidate_packet@0.1"
    assert payload["comparison_summary"]["total_comparisons"] == 4
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_semantics_v4_projection_endpoint_returns_projection_and_cache_header() -> None:
    response = Response()
    payload = api_main.get_urm_semantics_v4_projection_endpoint(response=response).model_dump(
        mode="json"
    )

    assert payload["schema"] == "semantics_v4_candidate_projection.vnext_plus23@1"
    assert payload["bridge_pair_count"] >= 1
    assert payload["comparison_item_count"] >= 4
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_semantics_v4_pair_endpoint_unknown_pair_returns_not_found() -> None:
    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_semantics_v4_pair_endpoint(
            source_text_hash="f" * 64,
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND"


def test_semantics_v4_projection_endpoint_missing_packet_artifact_returns_not_found(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest_path = tmp_path / "vnext_plus23_manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": "stop_gate.vnext_plus23_manifest@1",
                "semantics_v4_candidate_packet_fixtures": [],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(semantics_v4, "VNEXT_PLUS23_STOP_GATE_MANIFEST_PATH", manifest_path)
    semantics_v4._semantics_fixture_index_for_manifest.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_semantics_v4_projection_endpoint(response=Response())

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND"


def test_semantics_v4_pair_endpoint_missing_candidate_artifact_returns_not_found(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest_path = tmp_path / "vnext_plus23_manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": "stop_gate.vnext_plus23_manifest@1",
                "semantics_v4_candidate_packet_fixtures": [
                    {
                        "fixture_id": "semantics_v4_candidate.packet.case_a",
                        "surface_id": "adeu.semantics_v4_candidate.packet",
                        "source_text_hash": _pair()["source_text_hash"],
                        "core_ir_artifact_id": _pair()["core_ir_artifact_id"],
                        "concept_artifact_id": _pair()["concept_artifact_id"],
                        "semantics_v3_path": str(
                            _repo_root()
                            / "apps"
                            / "api"
                            / "fixtures"
                            / "stop_gate"
                            / "vnext_plus23"
                            / "semantics_diagnostics_v3_case_a.json"
                        ),
                        "semantics_v4_candidate_path": "missing_candidate_payload.json",
                        "semantics_v3_source_lane": "v3_default",
                        "semantics_v4_candidate_source_lane": "v4_candidate",
                        "runs": [
                            {
                                "semantics_v4_candidate_packet_path": "missing_packet_output.json",
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(semantics_v4, "VNEXT_PLUS23_STOP_GATE_MANIFEST_PATH", manifest_path)
    semantics_v4._semantics_fixture_index_for_manifest.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_semantics_v4_pair_endpoint(
            source_text_hash=_pair()["source_text_hash"],
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND"


def test_semantics_v4_endpoint_fails_closed_on_non_enforcement_context_violation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(api_main, "semantics_v4_candidate_non_enforcement_context", nullcontext)

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_semantics_v4_pair_endpoint(
            source_text_hash=_pair()["source_text_hash"],
            core_ir_artifact_id=_pair()["core_ir_artifact_id"],
            concept_artifact_id=_pair()["concept_artifact_id"],
            response=Response(),
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_SEMANTICS_V4_REQUEST_INVALID"


def test_semantics_v4_projection_endpoint_fails_closed_on_non_enforcement_context_violation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(api_main, "semantics_v4_candidate_non_enforcement_context", nullcontext)

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_semantics_v4_projection_endpoint(response=Response())

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_SEMANTICS_V4_REQUEST_INVALID"


def test_build_semantics_v4_projection_rejects_invalid_catalog_pair_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def _invalid_pairs(*, catalog_path: Path | None = None) -> list[dict[str, str]]:
        del catalog_path
        return [
            {
                "source_text_hash": "",
                "core_ir_artifact_id": _pair()["core_ir_artifact_id"],
                "concept_artifact_id": _pair()["concept_artifact_id"],
            }
        ]

    monkeypatch.setattr(
        semantics_v4,
        "list_cross_ir_catalog_pairs_vnext_plus20",
        _invalid_pairs,
    )
    with pytest.raises(semantics_v4.SemanticsV4CandidateVnextPlus23Error) as exc_info:
        _build_projection()

    assert exc_info.value.code == "URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID"
    assert (
        exc_info.value.reason
        == "catalog pair entry is invalid for semantics-v4 candidate projection"
    )


def test_build_semantics_v4_packet_wraps_packet_validation_errors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FailPacket:
        @staticmethod
        def model_validate(_payload: object) -> object:
            class _ProbeValidationModel(BaseModel):
                required_int: int

            _ProbeValidationModel.model_validate({"required_int": "not-an-int"})
            raise AssertionError("unreachable")

    monkeypatch.setattr(semantics_v4, "AdeuSemanticsV4CandidatePacket", _FailPacket)

    with pytest.raises(semantics_v4.SemanticsV4CandidateVnextPlus23Error) as exc_info:
        _build_packet(**_pair())

    assert exc_info.value.code == "URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID"
    assert exc_info.value.reason == "semantics-v4 candidate packet payload failed schema validation"
