from __future__ import annotations

from pathlib import Path

import adeu_api.main as api_main
import pytest
from fastapi import HTTPException, Response


@pytest.fixture(autouse=True)
def _clear_catalog_caches() -> None:
    api_main._read_surface_catalog_index.cache_clear()
    yield
    api_main._read_surface_catalog_index.cache_clear()


def _entry_sort_key(entry: api_main.EvidenceExplorerCatalogEntry) -> tuple[str, str, str, str]:
    return (
        entry.source_text_hash,
        entry.core_ir_artifact_id,
        entry.concept_artifact_id,
        entry.artifact_id or "",
    )


def test_evidence_explorer_catalog_endpoint_returns_sorted_family_index() -> None:
    response = Response()
    payload = api_main.get_urm_evidence_explorer_catalog_endpoint(response=response)
    body = payload.model_dump(mode="json")

    assert body["schema"] == "evidence_explorer.catalog@0.1"
    families = body["families"]
    assert [item["family"] for item in families] == sorted(
        [
            "read_surface",
            "normative_advice",
            "proof_trust",
            "semantics_v4_candidate",
            "extraction_fidelity",
        ]
    )
    for item in families:
        assert item["list_ref"] == {
            "kind": "endpoint",
            "path": "/urm/evidence-explorer/catalog/{family}",
        }
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_evidence_explorer_catalog_family_read_surface_contract_and_primary_ref() -> None:
    response = Response()
    payload = api_main.get_urm_evidence_explorer_catalog_family_endpoint(
        family="read_surface",
        response=response,
    )

    assert payload.schema == "evidence_explorer.catalog_family@0.1"
    assert payload.family == "read_surface"
    assert payload.identity_mode == "artifact_level"
    assert payload.truncated is False
    assert payload.max_entries_per_family is None
    assert payload.returned_entries is None
    assert payload.remaining_entries is None
    assert payload.entries

    first = payload.entries[0]
    assert first.family == "read_surface"
    assert first.artifact_id is not None
    assert first.core_ir_artifact_id == first.artifact_id
    assert first.concept_artifact_id == ""
    assert first.entry_id == f"artifact:{first.artifact_id}"
    assert first.ref.path == f"/urm/core-ir/artifacts/{first.artifact_id}"
    assert response.headers["Cache-Control"] == api_main._READ_SURFACE_CACHE_CONTROL


def test_evidence_explorer_catalog_family_pair_contract_and_ordering() -> None:
    payload = api_main.get_urm_evidence_explorer_catalog_family_endpoint(
        family="normative_advice",
        response=Response(),
    )

    assert payload.family == "normative_advice"
    assert payload.identity_mode == "pair_level"
    assert payload.truncated is False
    assert payload.entries
    assert all(item.artifact_id is None for item in payload.entries)
    assert all(item.entry_id.startswith("pair:") for item in payload.entries)
    assert all(item.ref.path.startswith("/urm/normative-advice/pairs/") for item in payload.entries)

    ordering = [_entry_sort_key(item) for item in payload.entries]
    assert ordering == sorted(ordering)


def test_evidence_explorer_catalog_family_non_empty_concept_prefix_excludes_read_surface() -> None:
    payload = api_main.get_urm_evidence_explorer_catalog_family_endpoint(
        family="read_surface",
        response=Response(),
        concept_artifact_id_prefix="concept.",
    )

    assert payload.total_entries == 0
    assert payload.entries == []
    assert payload.truncated is False


def test_evidence_explorer_catalog_family_unsupported_family_fails_closed() -> None:
    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_evidence_explorer_catalog_family_endpoint(
            family="unknown_family",
            response=Response(),
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_READ_SURFACE_REQUEST_INVALID"
    assert exc_info.value.detail["reason"] == "UNSUPPORTED_FAMILY"


def test_evidence_explorer_catalog_family_volume_cap_and_truncation_metadata(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    synthetic_entries = [
        api_main._EvidenceExplorerEntry(
            family="normative_advice",
            source_text_hash=f"source_{idx:04d}",
            core_ir_artifact_id=f"core_{idx:04d}",
            concept_artifact_id=f"concept_{idx:04d}",
            artifact_id=None,
            ref_path=(
                f"/urm/normative-advice/pairs/"
                f"source_{idx:04d}/core_{idx:04d}/concept_{idx:04d}"
            ),
        )
        for idx in range(1005)
    ][::-1]

    original_loader = api_main._evidence_explorer_entries_for_family_or_http

    def _fake_entries_for_family_or_http(
        *, family: api_main.EvidenceExplorerFamily
    ) -> list[api_main._EvidenceExplorerEntry]:
        if family == "normative_advice":
            return list(synthetic_entries)
        return original_loader(family=family)

    monkeypatch.setattr(
        api_main,
        "_evidence_explorer_entries_for_family_or_http",
        _fake_entries_for_family_or_http,
    )

    payload = api_main.get_urm_evidence_explorer_catalog_family_endpoint(
        family="normative_advice",
        response=Response(),
    )

    assert payload.truncated is True
    assert payload.total_entries == 1005
    assert payload.max_entries_per_family == 1000
    assert payload.returned_entries == 1000
    assert payload.remaining_entries == 5
    assert len(payload.entries) == 1000

    ordering = [_entry_sort_key(item) for item in payload.entries]
    assert ordering == sorted(ordering)


def test_evidence_explorer_extraction_fidelity_missing_catalog_maps_to_not_found(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    missing_catalog_path = tmp_path / "missing_catalog.json"
    monkeypatch.setattr(api_main, "VNEXT_PLUS24_CATALOG_PATH", missing_catalog_path)

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_evidence_explorer_catalog_family_endpoint(
            family="extraction_fidelity",
            response=Response(),
        )

    assert exc_info.value.status_code == 404
    assert exc_info.value.detail["code"] == "URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND"


def test_evidence_explorer_extraction_fidelity_payload_invalid_maps_to_bad_request(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    catalog_path = tmp_path / "vnext_plus24_catalog.json"
    catalog_path.write_text('{"schema":"wrong","entries":[]}', encoding="utf-8")
    monkeypatch.setattr(api_main, "VNEXT_PLUS24_CATALOG_PATH", catalog_path)

    with pytest.raises(HTTPException) as exc_info:
        api_main.get_urm_evidence_explorer_catalog_family_endpoint(
            family="extraction_fidelity",
            response=Response(),
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID"
