from __future__ import annotations

import json
import socket
from pathlib import Path

import adeu_api.main as api_main
import adeu_api.openai_provider as openai_provider
import pytest
from adeu_api.hashing import sha256_canonical_json
from adeu_api.read_surface_runtime_guards import NoProviderCallsGuard
from fastapi import HTTPException, Response


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.fixture(autouse=True)
def _clear_read_surface_catalog_cache() -> None:
    api_main._read_surface_catalog_index.cache_clear()
    yield
    api_main._read_surface_catalog_index.cache_clear()


def _is_read_surface_not_found(exc: HTTPException) -> bool:
    detail = exc.detail if isinstance(exc.detail, dict) else {}
    return (
        exc.status_code == 404
        and detail.get("code") == "URM_ADEU_READ_SURFACE_ARTIFACT_NOT_FOUND"
    )


def _exercise_read_surface_endpoints() -> None:
    index = api_main._read_surface_catalog_index_or_http()
    artifact_ids = sorted(index.entries_by_core_ir_id.keys())
    integrity_families = sorted(api_main._READ_SURFACE_INTEGRITY_FAMILY_TO_SCHEMA.keys())

    for artifact_id in artifact_ids:
        api_main.get_urm_core_ir_artifact_endpoint(
            artifact_id=artifact_id,
            response=Response(),
        )
        api_main.get_urm_core_ir_lane_projection_endpoint(
            artifact_id=artifact_id,
            response=Response(),
        )
        api_main.get_urm_core_ir_lane_report_endpoint(
            artifact_id=artifact_id,
            response=Response(),
        )
        for family in integrity_families:
            try:
                api_main.get_urm_core_ir_integrity_endpoint(
                    artifact_id=artifact_id,
                    family=family,
                    response=Response(),
                )
            except HTTPException as exc:
                if _is_read_surface_not_found(exc):
                    continue
                raise


def _read_surface_mutable_surface_paths() -> list[Path]:
    catalog_path = api_main._READ_SURFACE_CATALOG_PATH.resolve()
    payload = _load_json(catalog_path)
    if payload.get("schema") != "read_surface.vnext_plus19_catalog@1":
        raise AssertionError("expected read_surface.vnext_plus19_catalog@1 schema")

    artifact_refs = payload.get("artifact_refs")
    if not isinstance(artifact_refs, list):
        raise AssertionError("catalog artifact_refs must be a list")

    paths: set[Path] = {catalog_path}
    for artifact_ref in artifact_refs:
        if not isinstance(artifact_ref, dict):
            raise AssertionError("catalog artifact_ref entries must be objects")
        raw_path = artifact_ref.get("path")
        if not isinstance(raw_path, str) or not raw_path:
            raise AssertionError("catalog artifact_ref path must be a non-empty string")
        artifact_path = (catalog_path.parent / Path(raw_path)).resolve()
        paths.add(artifact_path)

    return sorted(paths, key=lambda path: str(path))


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {
        str(path): sha256_canonical_json(_load_json(path))
        for path in _read_surface_mutable_surface_paths()
    }


def test_no_provider_calls_guard_fails_closed_on_provider_entrypoint() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(
            AssertionError,
            match="provider client entrypoint invoked",
        ):
            openai_provider.propose_openai()  # type: ignore[call-arg]


def test_no_provider_calls_guard_denies_outbound_network() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="outbound network call denied"):
            socket.create_connection(("example.com", 443), timeout=0.01)


def test_read_surface_r1_endpoints_are_provider_and_network_guarded() -> None:
    with NoProviderCallsGuard():
        _exercise_read_surface_endpoints()


def test_read_surface_r1_endpoints_do_not_mutate_vnext_plus19_fixture_surface() -> None:
    before_snapshot = _mutable_surface_snapshot_hashes()

    with NoProviderCallsGuard():
        _exercise_read_surface_endpoints()

    after_snapshot = _mutable_surface_snapshot_hashes()
    assert before_snapshot == after_snapshot
