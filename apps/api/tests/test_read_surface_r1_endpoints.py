from __future__ import annotations

import json
from pathlib import Path

import adeu_api.main as api_main
import pytest
from fastapi import HTTPException, Response


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.fixture(autouse=True)
def _clear_read_surface_catalog_cache() -> None:
    api_main._read_surface_catalog_index.cache_clear()
    yield
    api_main._read_surface_catalog_index.cache_clear()


def test_read_surface_core_ir_endpoint_returns_catalog_artifact_and_cache_header() -> None:
    response = Response()
    payload = api_main.get_urm_core_ir_artifact_endpoint(
        artifact_id="core_ir.case_a_1",
        response=response,
    )
    body = payload.model_dump(mode="json")

    assert body["artifact_id"] == "core_ir.case_a_1"
    assert body["schema"] == "adeu_core_ir@0.1"
    assert body["created_at"] == "2026-01-01T00:00:00Z"
    assert body["core_ir"]["schema"] == "adeu_core_ir@0.1"
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_read_surface_lane_projection_and_integrity_endpoints_return_catalog_artifacts() -> None:
    lane_projection_response = Response()
    lane_projection = api_main.get_urm_core_ir_lane_projection_endpoint(
        artifact_id="core_ir.case_a_1",
        response=lane_projection_response,
    ).model_dump(mode="json")

    integrity_response = Response()
    integrity = api_main.get_urm_core_ir_integrity_endpoint(
        artifact_id="core_ir.case_a_1",
        family="cycle_policy",
        response=integrity_response,
    ).model_dump(mode="json")

    assert lane_projection["schema"] == "adeu_lane_projection@0.1"
    assert lane_projection["lane_projection"]["schema"] == "adeu_lane_projection@0.1"
    assert lane_projection_response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL

    assert integrity["schema"] == "adeu_integrity_cycle_policy@0.1"
    assert integrity["integrity_artifact"]["schema"] == "adeu_integrity_cycle_policy@0.1"
    assert integrity_response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_read_surface_unknown_artifact_id_fails_not_found() -> None:
    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_core_ir_artifact_endpoint(
            artifact_id="core_ir.missing",
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_READ_SURFACE_ARTIFACT_NOT_FOUND"


def test_read_surface_integrity_family_invalid_fails_request_invalid() -> None:
    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_core_ir_integrity_endpoint(
            artifact_id="core_ir.case_a_1",
            family="not_a_family",
            response=Response(),
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_READ_SURFACE_REQUEST_INVALID"


def test_read_surface_lane_report_fallback_resolves_unique_match(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source_hash = "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa"
    core_payload = _load_json(_repo_root() / "examples/eval/stop_gate/adeu_core_ir_case_a_1.json")
    lane_report_payload = _load_json(
        _repo_root() / "apps/api/fixtures/read_surface/adeu_lane_report_case_a_1.json"
    )

    catalog_path = tmp_path / "vnext_plus19_catalog.json"
    (tmp_path / "core.json").write_text(json.dumps(core_payload), encoding="utf-8")
    (tmp_path / "lane_report.json").write_text(json.dumps(lane_report_payload), encoding="utf-8")
    catalog_path.write_text(
        json.dumps(
            {
                "schema": "read_surface.vnext_plus19_catalog@1",
                "artifact_refs": [
                    {
                        "artifact_ref_id": "core.ir",
                        "schema": "adeu_core_ir@0.1",
                        "path": "core.json",
                    },
                    {
                        "artifact_ref_id": "lane.report",
                        "schema": "adeu_lane_report@0.1",
                        "path": "lane_report.json",
                    },
                ],
                "entries": [
                    {
                        "core_ir_artifact_id": "core.ir",
                        "source_text_hash": source_hash,
                        "parent_links": {},
                        "created_at": "2026-01-02T00:00:00Z",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(api_main, "_READ_SURFACE_CATALOG_PATH", catalog_path)
    api_main._read_surface_catalog_index.cache_clear()

    response = Response()
    lane_report = api_main.get_urm_core_ir_lane_report_endpoint(
        artifact_id="core.ir",
        response=response,
    ).model_dump(mode="json")

    assert lane_report["schema"] == "adeu_lane_report@0.1"
    assert lane_report["lane_report"]["schema"] == "adeu_lane_report@0.1"
    assert lane_report["created_at"] == "2026-01-02T00:00:00Z"
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_read_surface_lane_report_fallback_ambiguous_match_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source_hash = "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa"
    core_payload = _load_json(_repo_root() / "examples/eval/stop_gate/adeu_core_ir_case_a_1.json")
    lane_report_payload = _load_json(
        _repo_root() / "apps/api/fixtures/read_surface/adeu_lane_report_case_a_1.json"
    )

    catalog_path = tmp_path / "vnext_plus19_catalog.json"
    (tmp_path / "core.json").write_text(json.dumps(core_payload), encoding="utf-8")
    (tmp_path / "lane_report_a.json").write_text(
        json.dumps(lane_report_payload), encoding="utf-8"
    )
    (tmp_path / "lane_report_b.json").write_text(
        json.dumps(lane_report_payload), encoding="utf-8"
    )
    catalog_path.write_text(
        json.dumps(
            {
                "schema": "read_surface.vnext_plus19_catalog@1",
                "artifact_refs": [
                    {
                        "artifact_ref_id": "core.ir",
                        "schema": "adeu_core_ir@0.1",
                        "path": "core.json",
                    },
                    {
                        "artifact_ref_id": "lane.report.a",
                        "schema": "adeu_lane_report@0.1",
                        "path": "lane_report_a.json",
                    },
                    {
                        "artifact_ref_id": "lane.report.b",
                        "schema": "adeu_lane_report@0.1",
                        "path": "lane_report_b.json",
                    },
                ],
                "entries": [
                    {
                        "core_ir_artifact_id": "core.ir",
                        "source_text_hash": source_hash,
                        "parent_links": {},
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(api_main, "_READ_SURFACE_CATALOG_PATH", catalog_path)
    api_main._read_surface_catalog_index.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_core_ir_lane_report_endpoint(
            artifact_id="core.ir",
            response=Response(),
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_READ_SURFACE_REQUEST_INVALID"
    assert exc_info.value.detail["context"]["candidate_ref_ids"] == [
        "lane.report.a",
        "lane.report.b",
    ]


def test_read_surface_parent_link_source_hash_mismatch_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source_hash = "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa"
    core_payload = _load_json(_repo_root() / "examples/eval/stop_gate/adeu_core_ir_case_a_1.json")
    lane_report_payload = _load_json(
        _repo_root() / "apps/api/fixtures/read_surface/adeu_lane_report_case_a_1.json"
    )
    lane_report_payload["source_text_hash"] = "hash-mismatch"

    catalog_path = tmp_path / "vnext_plus19_catalog.json"
    (tmp_path / "core.json").write_text(json.dumps(core_payload), encoding="utf-8")
    (tmp_path / "lane_report.json").write_text(json.dumps(lane_report_payload), encoding="utf-8")
    catalog_path.write_text(
        json.dumps(
            {
                "schema": "read_surface.vnext_plus19_catalog@1",
                "artifact_refs": [
                    {
                        "artifact_ref_id": "core.ir",
                        "schema": "adeu_core_ir@0.1",
                        "path": "core.json",
                    },
                    {
                        "artifact_ref_id": "lane.report",
                        "schema": "adeu_lane_report@0.1",
                        "path": "lane_report.json",
                    },
                ],
                "entries": [
                    {
                        "core_ir_artifact_id": "core.ir",
                        "source_text_hash": source_hash,
                        "parent_links": {
                            "adeu_lane_report@0.1": "lane.report",
                        },
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(api_main, "_READ_SURFACE_CATALOG_PATH", catalog_path)
    api_main._read_surface_catalog_index.cache_clear()

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_core_ir_artifact_endpoint(
            artifact_id="core.ir",
            response=Response(),
        )

    assert exc_info.value.status_code == 500
    assert exc_info.value.detail["code"] == "URM_ADEU_READ_SURFACE_FIXTURE_INVALID"
