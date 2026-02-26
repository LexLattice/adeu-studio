from __future__ import annotations

import json
from contextlib import nullcontext
from pathlib import Path

import adeu_api.extraction_fidelity_vnext_plus24 as extraction_fidelity
import adeu_api.main as api_main
import pytest
from adeu_api.hashing import canonical_json
from adeu_core_ir import build_projection_alignment_fidelity_id
from fastapi import HTTPException, Response


def _fixtures_root() -> Path:
    return Path(__file__).resolve().parents[1] / "fixtures" / "extraction_fidelity"


def _source_text_hash() -> str:
    return "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa"


def _catalog_payload() -> dict[str, object]:
    catalog_path = _fixtures_root() / "vnext_plus24_catalog.json"
    return json.loads(catalog_path.read_text(encoding="utf-8"))


@pytest.fixture(autouse=True)
def _clear_extraction_fidelity_catalog_cache() -> None:
    extraction_fidelity._catalog_index_for_path.cache_clear()
    yield
    extraction_fidelity._catalog_index_for_path.cache_clear()


def _build_packet(**kwargs: str | Path) -> dict[str, object]:
    with extraction_fidelity.extraction_fidelity_non_enforcement_context():
        return extraction_fidelity.build_extraction_fidelity_packet_vnext_plus24(**kwargs)


def test_build_extraction_fidelity_packet_requires_runtime_non_enforcement_context() -> None:
    with pytest.raises(extraction_fidelity.ExtractionFidelityVnextPlus24Error) as exc_info:
        extraction_fidelity.build_extraction_fidelity_packet_vnext_plus24(
            source_text_hash=_source_text_hash()
        )

    assert exc_info.value.code == "URM_ADEU_EXTRACTION_FIDELITY_REQUEST_INVALID"
    assert (
        exc_info.value.reason == "extraction-fidelity runtime non-enforcement context is not active"
    )


def test_build_extraction_fidelity_packet_is_deterministic_and_schema_valid() -> None:
    first = _build_packet(source_text_hash=_source_text_hash())
    second = _build_packet(source_text_hash=_source_text_hash())

    assert first["schema"] == "adeu_projection_alignment_fidelity@0.1"
    assert canonical_json(first) == canonical_json(second)

    assert first["fidelity_summary"] == {
        "total_checks": 3,
        "compatible_checks": 1,
        "drift_checks": 2,
        "counts_by_code": {
            "label_text_mismatch": 1,
            "score_mismatch": 1,
            "span_mismatch": 1,
        },
        "counts_by_status": {
            "compatible": 1,
            "drift": 2,
        },
        "counts_by_severity": {
            "high": 1,
            "low": 1,
            "medium": 1,
        },
    }

    expected_status_by_code = {
        "label_text_mismatch": "compatible",
        "score_mismatch": "drift",
        "span_mismatch": "drift",
    }
    expected_severity_by_code = {
        "label_text_mismatch": "low",
        "score_mismatch": "medium",
        "span_mismatch": "high",
    }

    for item in first["fidelity_items"]:
        code = item["fidelity_code"]
        assert item["status"] == expected_status_by_code[code]
        assert item["severity"] == expected_severity_by_code[code]
        assert item["justification_refs"] == [
            f"artifact:adeu_projection_alignment@0.1:{_source_text_hash()}",
            (f"artifact:adeu_projection_alignment_fidelity_input@0.1:{_source_text_hash()}"),
        ]
        expected_fidelity_id = build_projection_alignment_fidelity_id(
            fidelity_code=item["fidelity_code"],
            status=item["status"],
            severity=item["severity"],
            justification_refs=item["justification_refs"],
            expected_hash=item.get("expected_hash"),
            observed_hash=item.get("observed_hash"),
        )
        assert item["fidelity_id"] == expected_fidelity_id

    by_code = {item["fidelity_code"]: item for item in first["fidelity_items"]}
    assert "expected_hash" not in by_code["label_text_mismatch"]
    assert "observed_hash" not in by_code["label_text_mismatch"]
    assert len(by_code["score_mismatch"]["expected_hash"]) == 64
    assert len(by_code["score_mismatch"]["observed_hash"]) == 64
    assert len(by_code["span_mismatch"]["expected_hash"]) == 64
    assert len(by_code["span_mismatch"]["observed_hash"]) == 64


def test_extraction_fidelity_source_endpoint_returns_packet_and_cache_header() -> None:
    response = Response()
    payload = api_main.get_urm_extraction_fidelity_source_endpoint(
        source_text_hash=_source_text_hash(),
        response=response,
    ).model_dump(mode="json")

    assert payload["schema"] == "adeu_projection_alignment_fidelity@0.1"
    assert payload["fidelity_summary"]["total_checks"] == 3
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_extraction_fidelity_source_endpoint_unknown_source_returns_not_found() -> None:
    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash="f" * 64,
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND"


def test_extraction_fidelity_source_endpoint_missing_artifact_returns_not_found(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    catalog_path = tmp_path / "vnext_plus24_catalog.json"
    catalog_path.write_text(
        json.dumps(
            {
                "schema": "extraction_fidelity.vnext_plus24_catalog@1",
                "entries": [
                    {
                        "source_text_hash": _source_text_hash(),
                        "projection_alignment_path": "missing_alignment.json",
                        "projection_alignment_fidelity_input_path": ("missing_fidelity_input.json"),
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(extraction_fidelity, "VNEXT_PLUS24_CATALOG_PATH", catalog_path)
    extraction_fidelity._catalog_index_for_path.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash=_source_text_hash(),
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND"


def test_extraction_fidelity_source_endpoint_route_binding_mismatch_returns_payload_invalid(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    projection_alignment_payload = json.loads(
        (_fixtures_root() / "vnext_plus24" / "adeu_projection_alignment_case_a_1.json").read_text(
            encoding="utf-8"
        )
    )
    projection_alignment_payload["source_text_hash"] = "0" * 64
    projection_alignment_path = tmp_path / "projection_alignment.json"
    projection_alignment_path.write_text(
        json.dumps(projection_alignment_payload),
        encoding="utf-8",
    )

    fidelity_input_payload = json.loads(
        (
            _fixtures_root()
            / "vnext_plus24"
            / "adeu_projection_alignment_fidelity_input_case_a_1.json"
        ).read_text(encoding="utf-8")
    )
    fidelity_input_path = tmp_path / "fidelity_input.json"
    fidelity_input_path.write_text(json.dumps(fidelity_input_payload), encoding="utf-8")

    catalog_path = tmp_path / "vnext_plus24_catalog.json"
    catalog_path.write_text(
        json.dumps(
            {
                "schema": "extraction_fidelity.vnext_plus24_catalog@1",
                "entries": [
                    {
                        "source_text_hash": _source_text_hash(),
                        "projection_alignment_path": str(projection_alignment_path),
                        "projection_alignment_fidelity_input_path": str(fidelity_input_path),
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(extraction_fidelity, "VNEXT_PLUS24_CATALOG_PATH", catalog_path)
    extraction_fidelity._catalog_index_for_path.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash=_source_text_hash(),
            response=Response(),
        )

    assert exc_info.value.status_code == 500
    assert exc_info.value.detail["code"] == "URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID"


def test_extraction_fidelity_source_endpoint_volume_cap_exceeded_returns_payload_invalid(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    projection_alignment_payload = json.loads(
        (_fixtures_root() / "vnext_plus24" / "adeu_projection_alignment_case_a_1.json").read_text(
            encoding="utf-8"
        )
    )
    projection_alignment_path = tmp_path / "projection_alignment.json"
    projection_alignment_path.write_text(
        json.dumps(projection_alignment_payload),
        encoding="utf-8",
    )

    node = {
        "match_id": "match_0",
        "projection_label_text": "x",
        "extraction_label_text": "x",
        "projection_span": {"start": 0, "end": 1},
        "extraction_span": {"start": 0, "end": 1},
        "projection_score_milli": 100,
        "extraction_score_milli": 100,
    }
    fidelity_input_payload = {
        "schema": "adeu_projection_alignment_fidelity_input@0.1",
        "source_text_hash": _source_text_hash(),
        "matched_nodes": [
            {
                **node,
                "match_id": f"match_{idx}",
            }
            for idx in range(5001)
        ],
    }
    fidelity_input_path = tmp_path / "fidelity_input.json"
    fidelity_input_path.write_text(json.dumps(fidelity_input_payload), encoding="utf-8")

    catalog_path = tmp_path / "vnext_plus24_catalog.json"
    catalog_path.write_text(
        json.dumps(
            {
                "schema": "extraction_fidelity.vnext_plus24_catalog@1",
                "entries": [
                    {
                        "source_text_hash": _source_text_hash(),
                        "projection_alignment_path": str(projection_alignment_path),
                        "projection_alignment_fidelity_input_path": str(fidelity_input_path),
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(extraction_fidelity, "VNEXT_PLUS24_CATALOG_PATH", catalog_path)
    extraction_fidelity._catalog_index_for_path.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash=_source_text_hash(),
            response=Response(),
        )

    assert exc_info.value.status_code == 500
    assert exc_info.value.detail["code"] == "URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID"


def test_extraction_fidelity_source_endpoint_duplicate_catalog_entries_return_request_invalid(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    projection_alignment_path = (
        _fixtures_root() / "vnext_plus24" / "adeu_projection_alignment_case_a_1.json"
    )
    fidelity_input_path = (
        _fixtures_root() / "vnext_plus24" / "adeu_projection_alignment_fidelity_input_case_a_1.json"
    )

    catalog_path = tmp_path / "vnext_plus24_catalog.json"
    catalog_path.write_text(
        json.dumps(
            {
                "schema": "extraction_fidelity.vnext_plus24_catalog@1",
                "entries": [
                    {
                        "source_text_hash": _source_text_hash(),
                        "projection_alignment_path": str(projection_alignment_path),
                        "projection_alignment_fidelity_input_path": str(fidelity_input_path),
                    },
                    {
                        "source_text_hash": _source_text_hash(),
                        "projection_alignment_path": str(projection_alignment_path),
                        "projection_alignment_fidelity_input_path": str(fidelity_input_path),
                    },
                ],
            }
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(extraction_fidelity, "VNEXT_PLUS24_CATALOG_PATH", catalog_path)
    extraction_fidelity._catalog_index_for_path.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash=_source_text_hash(),
            response=Response(),
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_EXTRACTION_FIDELITY_REQUEST_INVALID"


def test_extraction_fidelity_endpoint_fails_closed_on_non_enforcement_context_violation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(api_main, "extraction_fidelity_non_enforcement_context", nullcontext)

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash=_source_text_hash(),
            response=Response(),
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_EXTRACTION_FIDELITY_REQUEST_INVALID"


def test_extraction_fidelity_fixture_catalog_file_is_schema_valid() -> None:
    catalog_payload = _catalog_payload()

    validated = extraction_fidelity.ExtractionFidelityCatalog.model_validate(catalog_payload)
    assert validated.schema == "extraction_fidelity.vnext_plus24_catalog@1"
    assert len(validated.entries) == 1
