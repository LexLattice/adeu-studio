from __future__ import annotations

import json
import socket
from contextlib import ExitStack, nullcontext
from pathlib import Path
from typing import Any
from unittest.mock import patch

import adeu_api.main as api_main
import adeu_api.normative_advice_vnext_plus21 as normative_advice
import adeu_api.openai_provider as openai_provider
import pytest
from adeu_api.cross_ir_bridge_vnext_plus20 import CROSS_IR_CATALOG_PATH, CrossIRCatalog
from adeu_api.hashing import sha256_canonical_json
from adeu_api.read_surface_runtime_guards import NoProviderCallsGuard
from fastapi import HTTPException, Response

_MATERIALIZATION_FLOW_TARGETS: tuple[str, ...] = (
    "adeu_api.main.create_artifact",
    "adeu_api.main.create_concept_artifact",
    "adeu_api.main.create_explain_artifact",
    "adeu_api.main.create_semantic_depth_report",
    "adeu_api.storage.create_artifact",
    "adeu_api.storage.create_concept_artifact",
    "adeu_api.storage.create_explain_artifact",
    "adeu_api.storage.create_semantic_depth_report",
)
_NON_ENFORCEMENT_FIELD_NAMES: frozenset[str] = frozenset(
    {"enforce", "block", "gate", "allow", "deny"}
)


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.fixture(autouse=True)
def _clear_normative_advice_manifest_cache() -> None:
    normative_advice._coherence_fixture_index_for_manifest.cache_clear()
    yield
    normative_advice._coherence_fixture_index_for_manifest.cache_clear()


def _raise_materialization_flow_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            "normative advice n4 fail-closed: materialization flow invoked: " f"{target}"
        )

    return _fail


def _build_normative_advice_builders() -> None:
    pairs = normative_advice.list_cross_ir_catalog_pairs_vnext_plus20()
    with normative_advice.normative_advice_non_enforcement_context():
        for pair in pairs:
            normative_advice.build_normative_advice_packet_vnext_plus21(
                source_text_hash=pair["source_text_hash"],
                core_ir_artifact_id=pair["core_ir_artifact_id"],
                concept_artifact_id=pair["concept_artifact_id"],
            )
        normative_advice.build_normative_advice_projection_vnext_plus21()


def _exercise_normative_advice_endpoints() -> None:
    pairs = normative_advice.list_cross_ir_catalog_pairs_vnext_plus20()
    for pair in pairs:
        api_main.get_urm_normative_advice_pair_endpoint(
            source_text_hash=pair["source_text_hash"],
            core_ir_artifact_id=pair["core_ir_artifact_id"],
            concept_artifact_id=pair["concept_artifact_id"],
            response=Response(),
        )
    api_main.get_urm_normative_advice_projection_endpoint(response=Response())


def _exercise_normative_advice_paths_under_n4_guards() -> None:
    with NoProviderCallsGuard():
        with ExitStack() as stack:
            for target in _MATERIALIZATION_FLOW_TARGETS:
                stack.enter_context(
                    patch(target, new=_raise_materialization_flow_call(target=target))
                )
            _build_normative_advice_builders()
            _exercise_normative_advice_endpoints()


def _vnext_plus21_manifest_path() -> Path:
    return (
        Path(__file__).resolve().parents[1]
        / "fixtures"
        / "stop_gate"
        / "vnext_plus21_manifest.json"
    )


def _normative_advice_mutable_surface_paths() -> list[Path]:
    catalog_path = CROSS_IR_CATALOG_PATH.resolve()
    catalog = CrossIRCatalog.model_validate(_load_json(catalog_path))

    paths: set[Path] = {catalog_path}
    for artifact_ref in catalog.artifact_refs:
        artifact_path = Path(artifact_ref.path)
        if not artifact_path.is_absolute():
            artifact_path = catalog_path.parent / artifact_path
        paths.add(artifact_path.resolve())

    manifest_path = _vnext_plus21_manifest_path().resolve()
    manifest_payload = _load_json(manifest_path)
    if manifest_payload.get("schema") != "stop_gate.vnext_plus21_manifest@1":
        raise AssertionError("expected stop_gate.vnext_plus21_manifest@1 schema")
    paths.add(manifest_path)

    fixture_specs = (
        ("normative_advice_packet_fixtures", "normative_advice_packet_path"),
        ("normative_advice_projection_fixtures", "normative_advice_projection_path"),
    )
    for fixture_list_key, run_key in fixture_specs:
        fixture_list = manifest_payload.get(fixture_list_key)
        if not isinstance(fixture_list, list):
            raise AssertionError(f"{fixture_list_key} must be a list")
        for fixture in fixture_list:
            if not isinstance(fixture, dict):
                raise AssertionError(f"{fixture_list_key} entries must be objects")
            runs = fixture.get("runs")
            if not isinstance(runs, list) or not runs:
                raise AssertionError(f"{fixture_list_key} entries must include non-empty runs")
            for run in runs:
                if not isinstance(run, dict):
                    raise AssertionError("fixture run entries must be objects")
                raw_path = run.get(run_key)
                if not isinstance(raw_path, str) or not raw_path:
                    raise AssertionError(f"fixture run key {run_key} must be a non-empty string")
                payload_path = Path(raw_path)
                if not payload_path.is_absolute():
                    payload_path = manifest_path.parent / payload_path
                paths.add(payload_path.resolve())

    return sorted(paths, key=lambda path: str(path))


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {
        str(path): sha256_canonical_json(_load_json(path))
        for path in _normative_advice_mutable_surface_paths()
    }


def _assert_non_enforcement_payload(value: object) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            assert key not in _NON_ENFORCEMENT_FIELD_NAMES
            _assert_non_enforcement_payload(child)
        return
    if isinstance(value, list):
        for child in value:
            _assert_non_enforcement_payload(child)


def test_no_provider_calls_guard_fails_closed_on_provider_entrypoint_for_normative_advice() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="provider client entrypoint invoked"):
            openai_provider.propose_openai()  # type: ignore[call-arg]


def test_no_provider_calls_guard_denies_outbound_network_for_normative_advice() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="outbound network call denied"):
            socket.create_connection(("example.com", 443), timeout=0.01)


def test_normative_advice_paths_are_provider_network_and_materialization_guarded() -> None:
    _exercise_normative_advice_paths_under_n4_guards()


def test_normative_advice_paths_do_not_mutate_vnext_plus21_fixture_surface() -> None:
    before_snapshot = _mutable_surface_snapshot_hashes()

    _exercise_normative_advice_paths_under_n4_guards()

    after_snapshot = _mutable_surface_snapshot_hashes()
    assert before_snapshot == after_snapshot


def test_normative_advice_endpoints_fail_closed_on_non_enforcement_context_violation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pairs = normative_advice.list_cross_ir_catalog_pairs_vnext_plus20()
    pair = pairs[0]
    monkeypatch.setattr(api_main, "normative_advice_non_enforcement_context", nullcontext)

    with pytest.raises(HTTPException) as pair_exc_info:
        api_main.get_urm_normative_advice_pair_endpoint(
            source_text_hash=pair["source_text_hash"],
            core_ir_artifact_id=pair["core_ir_artifact_id"],
            concept_artifact_id=pair["concept_artifact_id"],
            response=Response(),
        )
    assert pair_exc_info.value.status_code == 400
    assert pair_exc_info.value.detail["code"] == "URM_ADEU_NORMATIVE_ADVICE_REQUEST_INVALID"

    with pytest.raises(HTTPException) as projection_exc_info:
        api_main.get_urm_normative_advice_projection_endpoint(response=Response())
    assert projection_exc_info.value.status_code == 400
    assert projection_exc_info.value.detail["code"] == "URM_ADEU_NORMATIVE_ADVICE_REQUEST_INVALID"


def test_normative_advice_payloads_are_recommendation_only() -> None:
    pairs = normative_advice.list_cross_ir_catalog_pairs_vnext_plus20()
    with normative_advice.normative_advice_non_enforcement_context():
        projection = normative_advice.build_normative_advice_projection_vnext_plus21()

    _assert_non_enforcement_payload(projection.model_dump(mode="json"))

    for pair in pairs:
        packet_payload = api_main.get_urm_normative_advice_pair_endpoint(
            source_text_hash=pair["source_text_hash"],
            core_ir_artifact_id=pair["core_ir_artifact_id"],
            concept_artifact_id=pair["concept_artifact_id"],
            response=Response(),
        ).model_dump(mode="json")
        _assert_non_enforcement_payload(packet_payload)
