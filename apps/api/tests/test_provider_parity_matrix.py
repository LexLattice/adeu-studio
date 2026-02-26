from __future__ import annotations

import json
from importlib import resources as importlib_resources

import adeu_api.main as api_main
import pytest


@pytest.fixture(autouse=True)
def _clear_provider_parity_cache() -> None:
    api_main._provider_parity_supported_providers_by_surface.cache_clear()
    yield
    api_main._provider_parity_supported_providers_by_surface.cache_clear()


def _valid_matrix_payload() -> dict[str, object]:
    return {
        "schema": "provider_parity.vnext_plus25_matrix@1",
        "surfaces": [
            {
                "surface_id": "adeu.propose",
                "supported_providers": ["mock", "openai", "codex"],
            },
            {
                "surface_id": "adeu_core_ir.propose",
                "supported_providers": ["mock", "openai", "codex"],
            },
            {
                "surface_id": "concepts.propose",
                "supported_providers": ["mock", "openai", "codex"],
            },
            {
                "surface_id": "puzzles.propose",
                "supported_providers": ["mock", "openai", "codex"],
            },
            {
                "surface_id": "concepts.tournament.live_generation",
                "supported_providers": ["mock"],
            },
            {
                "surface_id": "concepts.tournament.replay_candidates",
                "supported_providers": ["mock", "openai", "codex"],
            },
        ],
    }


def test_provider_parity_matrix_loader_matches_frozen_surfaces() -> None:
    matrix = api_main._provider_parity_supported_providers_by_surface()

    assert set(matrix) == set(api_main._FROZEN_PROVIDER_PARITY_SURFACE_IDS)
    assert matrix["adeu.propose"] == ("mock", "openai", "codex")
    assert matrix["adeu_core_ir.propose"] == ("mock", "openai", "codex")
    assert matrix["concepts.tournament.live_generation"] == ("mock",)
    assert matrix["concepts.tournament.replay_candidates"] == ("mock", "openai", "codex")


def test_provider_parity_matrix_package_resource_matches_authoritative_fixture() -> None:
    source_payload = json.loads(api_main._PROVIDER_PARITY_MATRIX_PATH.read_text(encoding="utf-8"))
    package_payload = json.loads(
        importlib_resources.files("adeu_api")
        .joinpath(api_main._PROVIDER_PARITY_MATRIX_PACKAGE_RESOURCE)
        .read_text(encoding="utf-8")
    )

    assert package_payload == source_payload


def test_provider_parity_matrix_loader_falls_back_to_packaged_resource(
    tmp_path, monkeypatch: pytest.MonkeyPatch
) -> None:
    missing_path = tmp_path / "missing_provider_matrix.json"
    monkeypatch.setattr(api_main, "_PROVIDER_PARITY_MATRIX_PATH", missing_path)

    matrix = api_main._provider_parity_supported_providers_by_surface()
    assert set(matrix) == set(api_main._FROZEN_PROVIDER_PARITY_SURFACE_IDS)


def test_provider_parity_matrix_loader_rejects_invalid_schema(
    tmp_path, monkeypatch: pytest.MonkeyPatch
) -> None:
    payload = _valid_matrix_payload()
    payload["schema"] = "provider_parity.vnext_plus14_matrix@0"
    matrix_path = tmp_path / "provider_matrix_invalid_schema.json"
    matrix_path.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.setattr(api_main, "_PROVIDER_PARITY_MATRIX_PATH", matrix_path)

    with pytest.raises(api_main._ProviderParityMatrixError) as exc_info:
        api_main._provider_parity_supported_providers_by_surface()

    assert exc_info.value.code == "URM_PROVIDER_PARITY_ROUTE_MATRIX_INVALID"


def test_provider_parity_matrix_loader_rejects_surface_drift(
    tmp_path, monkeypatch: pytest.MonkeyPatch
) -> None:
    payload = _valid_matrix_payload()
    payload["surfaces"] = payload["surfaces"][:-1]
    matrix_path = tmp_path / "provider_matrix_surface_drift.json"
    matrix_path.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.setattr(api_main, "_PROVIDER_PARITY_MATRIX_PATH", matrix_path)

    with pytest.raises(api_main._ProviderParityMatrixError) as exc_info:
        api_main._provider_parity_supported_providers_by_surface()

    assert exc_info.value.code == "URM_PROVIDER_PARITY_SURFACE_MATRIX_DRIFT"
