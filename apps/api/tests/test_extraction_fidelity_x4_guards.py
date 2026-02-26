from __future__ import annotations

import json
import socket
from contextlib import ExitStack
from pathlib import Path
from typing import Any, Literal
from unittest.mock import patch

import adeu_api.extraction_fidelity_vnext_plus24 as extraction_fidelity
import adeu_api.main as api_main
import adeu_api.openai_provider as openai_provider
import pytest
from adeu_api.hashing import sha256_canonical_json
from adeu_api.read_surface_runtime_guards import NoProviderCallsGuard
from fastapi import Response
from pydantic import BaseModel

_MATERIALIZATION_FLOW_TARGETS: tuple[str, ...] = (
    "adeu_api.main.create_artifact",
    "adeu_api.main.create_concept_artifact",
    "adeu_api.main.create_document",
    "adeu_api.main.create_explain_artifact",
    "adeu_api.main.create_proof_artifact",
    "adeu_api.main.create_semantic_depth_report",
    "adeu_api.main.create_validator_run",
    "adeu_api.storage.create_artifact",
    "adeu_api.storage.create_concept_artifact",
    "adeu_api.storage.create_document",
    "adeu_api.storage.create_explain_artifact",
    "adeu_api.storage.create_proof_artifact",
    "adeu_api.storage.create_semantic_depth_report",
    "adeu_api.storage.create_validator_run",
)
_NON_ENFORCEMENT_FIELD_NAMES: frozenset[str] = frozenset(
    {"enforce", "block", "gate", "allow", "deny"}
)


class _ExtractionFidelityPacketRun(BaseModel):
    extraction_fidelity_packet_path: str


class _ExtractionFidelityPacketFixture(BaseModel):
    projection_alignment_path: str
    projection_alignment_fidelity_input_path: str
    runs: list[_ExtractionFidelityPacketRun]


class _ExtractionFidelityProjectionRun(BaseModel):
    extraction_fidelity_projection_path: str


class _ExtractionFidelityProjectionFixture(BaseModel):
    runs: list[_ExtractionFidelityProjectionRun]


class _VnextPlus24ManifestForX4(BaseModel):
    schema: Literal["stop_gate.vnext_plus24_manifest@1"]
    extraction_fidelity_packet_fixtures: list[_ExtractionFidelityPacketFixture]
    extraction_fidelity_projection_fixtures: list[_ExtractionFidelityProjectionFixture]


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.fixture(autouse=True)
def _clear_extraction_fidelity_catalog_cache() -> None:
    extraction_fidelity._catalog_index_for_path.cache_clear()
    yield
    extraction_fidelity._catalog_index_for_path.cache_clear()


def _catalog_path() -> Path:
    return extraction_fidelity.VNEXT_PLUS24_CATALOG_PATH.resolve()


def _manifest_path() -> Path:
    return (
        Path(__file__).resolve().parents[1]
        / "fixtures"
        / "stop_gate"
        / "vnext_plus24_manifest.json"
    ).resolve()


def _catalog_payload() -> extraction_fidelity.ExtractionFidelityCatalog:
    return extraction_fidelity.ExtractionFidelityCatalog.model_validate(_load_json(_catalog_path()))


def _resolve_relative_path(*, base_paths: tuple[Path, ...], raw_path: str) -> Path:
    payload_path = Path(raw_path)
    if payload_path.is_absolute():
        return payload_path.resolve()
    for base_path in base_paths:
        resolved = (base_path / payload_path).resolve()
        if resolved.exists():
            return resolved
    return (base_paths[0] / payload_path).resolve()


def _source_text_hashes() -> list[str]:
    return sorted(entry.source_text_hash for entry in _catalog_payload().entries)


def _raise_materialization_flow_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            "extraction-fidelity x4 fail-closed: materialization flow invoked: " f"{target}"
        )

    return _fail


def _exercise_extraction_fidelity_builders() -> None:
    source_text_hashes = _source_text_hashes()
    with extraction_fidelity.extraction_fidelity_non_enforcement_context():
        for source_text_hash in source_text_hashes:
            extraction_fidelity.build_extraction_fidelity_packet_vnext_plus24(
                source_text_hash=source_text_hash
            )
        extraction_fidelity.build_extraction_fidelity_projection_vnext_plus24()


def _exercise_extraction_fidelity_endpoints() -> None:
    for source_text_hash in _source_text_hashes():
        api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash=source_text_hash,
            response=Response(),
        )
    api_main.get_urm_extraction_fidelity_projection_endpoint(response=Response())


def _exercise_extraction_fidelity_paths_under_x4_guards() -> None:
    with NoProviderCallsGuard():
        with ExitStack() as stack:
            for target in _MATERIALIZATION_FLOW_TARGETS:
                stack.enter_context(
                    patch(target, new=_raise_materialization_flow_call(target=target))
                )
            _exercise_extraction_fidelity_builders()
            _exercise_extraction_fidelity_endpoints()


def _extraction_fidelity_mutable_surface_paths() -> list[Path]:
    catalog_path = _catalog_path()
    catalog = _catalog_payload()
    catalog_root = catalog_path.parent

    paths: set[Path] = {catalog_path}
    for entry in catalog.entries:
        paths.add(
            _resolve_relative_path(
                base_paths=(catalog_root,),
                raw_path=entry.projection_alignment_path,
            )
        )
        paths.add(
            _resolve_relative_path(
                base_paths=(catalog_root,),
                raw_path=entry.projection_alignment_fidelity_input_path,
            )
        )

    manifest_path = _manifest_path()
    manifest = _VnextPlus24ManifestForX4.model_validate(_load_json(manifest_path))
    manifest_root = manifest_path.parent
    paths.add(manifest_path)
    for fixture in manifest.extraction_fidelity_packet_fixtures:
        paths.add(
            _resolve_relative_path(
                base_paths=(catalog_root, manifest_root),
                raw_path=fixture.projection_alignment_path,
            )
        )
        paths.add(
            _resolve_relative_path(
                base_paths=(catalog_root, manifest_root),
                raw_path=fixture.projection_alignment_fidelity_input_path,
            )
        )
        for run in fixture.runs:
            paths.add(
                _resolve_relative_path(
                    base_paths=(manifest_root, catalog_root),
                    raw_path=run.extraction_fidelity_packet_path,
                )
            )

    for fixture in manifest.extraction_fidelity_projection_fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_relative_path(
                    base_paths=(manifest_root, catalog_root),
                    raw_path=run.extraction_fidelity_projection_path,
                )
            )

    return sorted(paths, key=lambda path: str(path))


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {
        str(path): sha256_canonical_json(_load_json(path))
        for path in _extraction_fidelity_mutable_surface_paths()
    }


def _assert_non_enforcement_payload(
    value: object,
    *,
    _path: tuple[str | int, ...] = (),
) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in _NON_ENFORCEMENT_FIELD_NAMES:
                key_path = "/".join(str(part) for part in (*_path, key)) or "<root>"
                raise AssertionError(
                    f"disallowed non-enforcement key '{key}' found at path '{key_path}'"
                )
            _assert_non_enforcement_payload(child, _path=(*_path, key))
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _assert_non_enforcement_payload(child, _path=(*_path, index))


def test_no_provider_calls_guard_fails_closed_on_provider_entrypoint_for_extraction_fidelity(
) -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="provider client entrypoint invoked"):
            openai_provider.propose_openai()  # type: ignore[call-arg]


def test_no_provider_calls_guard_denies_outbound_network_for_extraction_fidelity() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="outbound network call denied"):
            socket.create_connection(("example.com", 443), timeout=0.01)


def test_extraction_fidelity_paths_are_provider_network_and_materialization_guarded() -> None:
    _exercise_extraction_fidelity_paths_under_x4_guards()


def test_extraction_fidelity_paths_do_not_mutate_vnext_plus24_fixture_surface() -> None:
    before_snapshot = _mutable_surface_snapshot_hashes()

    _exercise_extraction_fidelity_paths_under_x4_guards()

    after_snapshot = _mutable_surface_snapshot_hashes()
    assert before_snapshot == after_snapshot


def test_extraction_fidelity_payloads_are_recommendation_only() -> None:
    with extraction_fidelity.extraction_fidelity_non_enforcement_context():
        projection = extraction_fidelity.build_extraction_fidelity_projection_vnext_plus24()
    _assert_non_enforcement_payload(projection.model_dump(mode="json"))

    projection_payload = api_main.get_urm_extraction_fidelity_projection_endpoint(
        response=Response()
    ).model_dump(mode="json")
    _assert_non_enforcement_payload(projection_payload)

    for source_text_hash in _source_text_hashes():
        packet_payload = api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash=source_text_hash,
            response=Response(),
        ).model_dump(mode="json")
        _assert_non_enforcement_payload(packet_payload)
