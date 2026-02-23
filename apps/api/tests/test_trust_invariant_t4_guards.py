from __future__ import annotations

import json
import socket
from contextlib import ExitStack, nullcontext
from pathlib import Path
from typing import Any, Literal
from unittest.mock import patch

import adeu_api.main as api_main
import adeu_api.openai_provider as openai_provider
import adeu_api.trust_invariant_vnext_plus22 as trust_invariant
import pytest
from adeu_api.cross_ir_bridge_vnext_plus20 import CROSS_IR_CATALOG_PATH, CrossIRCatalog
from adeu_api.hashing import sha256_canonical_json
from adeu_api.read_surface_runtime_guards import NoProviderCallsGuard
from fastapi import HTTPException, Response
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


class _NormativeAdvicePacketRun(BaseModel):
    normative_advice_packet_path: str


class _NormativeAdvicePacketFixture(BaseModel):
    runs: list[_NormativeAdvicePacketRun]


class _NormativeAdviceProjectionRun(BaseModel):
    normative_advice_projection_path: str


class _NormativeAdviceProjectionFixture(BaseModel):
    runs: list[_NormativeAdviceProjectionRun]


class _VnextPlus21ManifestForT4(BaseModel):
    schema: Literal["stop_gate.vnext_plus21_manifest@1"]
    normative_advice_packet_fixtures: list[_NormativeAdvicePacketFixture]
    normative_advice_projection_fixtures: list[_NormativeAdviceProjectionFixture]


class _TrustInvariantPacketRun(BaseModel):
    trust_invariant_packet_path: str


class _TrustInvariantPacketFixture(BaseModel):
    runs: list[_TrustInvariantPacketRun]


class _TrustInvariantProjectionRun(BaseModel):
    trust_invariant_projection_path: str


class _TrustInvariantProjectionFixture(BaseModel):
    runs: list[_TrustInvariantProjectionRun]


class _VnextPlus22ManifestForT4(BaseModel):
    schema: Literal["stop_gate.vnext_plus22_manifest@1"]
    trust_invariant_packet_fixtures: list[_TrustInvariantPacketFixture]
    trust_invariant_projection_fixtures: list[_TrustInvariantProjectionFixture]


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.fixture(autouse=True)
def _clear_trust_invariant_manifest_caches() -> None:
    trust_invariant._coherence_fixture_index_for_manifest.cache_clear()
    trust_invariant._normative_advice_fixture_index_for_manifest.cache_clear()
    yield
    trust_invariant._coherence_fixture_index_for_manifest.cache_clear()
    trust_invariant._normative_advice_fixture_index_for_manifest.cache_clear()


def _raise_materialization_flow_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            "trust-invariant t4 fail-closed: materialization flow invoked: " f"{target}"
        )

    return _fail


def _exercise_trust_invariant_builders() -> None:
    pairs = trust_invariant.list_cross_ir_catalog_pairs_vnext_plus20()
    with trust_invariant.trust_invariant_non_enforcement_context():
        for pair in pairs:
            trust_invariant.build_trust_invariant_packet_vnext_plus22(
                source_text_hash=pair["source_text_hash"],
                core_ir_artifact_id=pair["core_ir_artifact_id"],
                concept_artifact_id=pair["concept_artifact_id"],
            )
        trust_invariant.build_trust_invariant_projection_vnext_plus22()


def _exercise_trust_invariant_endpoints() -> None:
    pairs = trust_invariant.list_cross_ir_catalog_pairs_vnext_plus20()
    for pair in pairs:
        api_main.get_urm_proof_trust_pair_endpoint(
            source_text_hash=pair["source_text_hash"],
            core_ir_artifact_id=pair["core_ir_artifact_id"],
            concept_artifact_id=pair["concept_artifact_id"],
            response=Response(),
        )
    api_main.get_urm_proof_trust_projection_endpoint(response=Response())


def _exercise_trust_invariant_paths_under_t4_guards() -> None:
    with NoProviderCallsGuard():
        with ExitStack() as stack:
            for target in _MATERIALIZATION_FLOW_TARGETS:
                stack.enter_context(
                    patch(target, new=_raise_materialization_flow_call(target=target))
                )
            _exercise_trust_invariant_builders()
            _exercise_trust_invariant_endpoints()


def _vnext_plus21_manifest_path() -> Path:
    return (
        Path(__file__).resolve().parents[1]
        / "fixtures"
        / "stop_gate"
        / "vnext_plus21_manifest.json"
    )


def _vnext_plus22_manifest_path() -> Path:
    return (
        Path(__file__).resolve().parents[1]
        / "fixtures"
        / "stop_gate"
        / "vnext_plus22_manifest.json"
    )


def _resolve_manifest_payload_path(*, manifest_path: Path, raw_path: str) -> Path:
    payload_path = Path(raw_path)
    if not payload_path.is_absolute():
        payload_path = manifest_path.parent / payload_path
    return payload_path.resolve()


def _trust_invariant_mutable_surface_paths() -> list[Path]:
    catalog_path = CROSS_IR_CATALOG_PATH.resolve()
    catalog = CrossIRCatalog.model_validate(_load_json(catalog_path))

    paths: set[Path] = {catalog_path}
    for artifact_ref in catalog.artifact_refs:
        artifact_path = Path(artifact_ref.path)
        if not artifact_path.is_absolute():
            artifact_path = catalog_path.parent / artifact_path
        paths.add(artifact_path.resolve())

    v21_manifest_path = _vnext_plus21_manifest_path().resolve()
    v21_manifest = _VnextPlus21ManifestForT4.model_validate(_load_json(v21_manifest_path))
    paths.add(v21_manifest_path)
    for fixture in v21_manifest.normative_advice_packet_fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=v21_manifest_path,
                    raw_path=run.normative_advice_packet_path,
                )
            )
    for fixture in v21_manifest.normative_advice_projection_fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=v21_manifest_path,
                    raw_path=run.normative_advice_projection_path,
                )
            )

    v22_manifest_path = _vnext_plus22_manifest_path().resolve()
    v22_manifest = _VnextPlus22ManifestForT4.model_validate(_load_json(v22_manifest_path))
    paths.add(v22_manifest_path)
    for fixture in v22_manifest.trust_invariant_packet_fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=v22_manifest_path,
                    raw_path=run.trust_invariant_packet_path,
                )
            )
    for fixture in v22_manifest.trust_invariant_projection_fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=v22_manifest_path,
                    raw_path=run.trust_invariant_projection_path,
                )
            )

    return sorted(paths, key=lambda path: str(path))


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {
        str(path): sha256_canonical_json(_load_json(path))
        for path in _trust_invariant_mutable_surface_paths()
    }


def _assert_non_enforcement_payload(
    value: object,
    *,
    _path: tuple[str | int, ...] = (),
) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in _NON_ENFORCEMENT_FIELD_NAMES:
                prefix = "/".join(str(part) for part in _path) or "<root>"
                raise AssertionError(
                    f"disallowed non-enforcement key '{key}' found at path '{prefix}'"
                )
            _assert_non_enforcement_payload(child, _path=(*_path, key))
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _assert_non_enforcement_payload(child, _path=(*_path, index))


def test_no_provider_calls_guard_fails_closed_on_provider_entrypoint_for_trust_invariant() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="provider client entrypoint invoked"):
            openai_provider.propose_openai()  # type: ignore[call-arg]


def test_no_provider_calls_guard_denies_outbound_network_for_trust_invariant() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="outbound network call denied"):
            socket.create_connection(("example.com", 443), timeout=0.01)


def test_trust_invariant_paths_are_provider_network_and_materialization_guarded() -> None:
    _exercise_trust_invariant_paths_under_t4_guards()


def test_trust_invariant_paths_do_not_mutate_vnext_plus22_fixture_surface() -> None:
    before_snapshot = _mutable_surface_snapshot_hashes()

    _exercise_trust_invariant_paths_under_t4_guards()

    after_snapshot = _mutable_surface_snapshot_hashes()
    assert before_snapshot == after_snapshot


def test_trust_invariant_endpoints_fail_closed_on_non_enforcement_context_violation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pairs = trust_invariant.list_cross_ir_catalog_pairs_vnext_plus20()
    pair = pairs[0]
    monkeypatch.setattr(api_main, "trust_invariant_non_enforcement_context", nullcontext)

    with pytest.raises(HTTPException) as pair_exc_info:
        api_main.get_urm_proof_trust_pair_endpoint(
            source_text_hash=pair["source_text_hash"],
            core_ir_artifact_id=pair["core_ir_artifact_id"],
            concept_artifact_id=pair["concept_artifact_id"],
            response=Response(),
        )
    assert pair_exc_info.value.status_code == 400
    assert pair_exc_info.value.detail["code"] == "URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID"

    with pytest.raises(HTTPException) as projection_exc_info:
        api_main.get_urm_proof_trust_projection_endpoint(response=Response())
    assert projection_exc_info.value.status_code == 400
    assert projection_exc_info.value.detail["code"] == "URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID"


def test_trust_invariant_payloads_are_recommendation_only() -> None:
    pairs = trust_invariant.list_cross_ir_catalog_pairs_vnext_plus20()
    with trust_invariant.trust_invariant_non_enforcement_context():
        projection = trust_invariant.build_trust_invariant_projection_vnext_plus22()

    _assert_non_enforcement_payload(projection.model_dump(mode="json"))

    for pair in pairs:
        packet_payload = api_main.get_urm_proof_trust_pair_endpoint(
            source_text_hash=pair["source_text_hash"],
            core_ir_artifact_id=pair["core_ir_artifact_id"],
            concept_artifact_id=pair["concept_artifact_id"],
            response=Response(),
        ).model_dump(mode="json")
        _assert_non_enforcement_payload(packet_payload)
