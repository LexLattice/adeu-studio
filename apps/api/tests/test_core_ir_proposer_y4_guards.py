from __future__ import annotations

import json
from contextlib import ExitStack
from pathlib import Path
from typing import Any, Literal
from unittest.mock import patch

import adeu_api.main as api_main
import pytest
from adeu_api.hashing import sha256_canonical_json
from adeu_api.main import CoreIRProposerRequest, urm_core_ir_propose_endpoint
from pydantic import BaseModel

_MATERIALIZATION_POLICY_FLOW_TARGETS: tuple[str, ...] = (
    "adeu_api.main.create_artifact",
    "adeu_api.main.create_concept_artifact",
    "adeu_api.main.create_document",
    "adeu_api.main.create_explain_artifact",
    "adeu_api.main.create_proof_artifact",
    "adeu_api.main.create_semantic_depth_report",
    "adeu_api.main.create_validator_run",
    "adeu_api.main.emit_governance_event",
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
_TRUST_LANE_FIELD_NAMES: frozenset[str] = frozenset(
    {"mapping_trust", "solver_trust", "proof_trust"}
)


class _CoreIRProposerRun(BaseModel):
    provider: str
    core_ir_proposer_request_path: str
    core_ir_proposer_response_path: str
    core_ir_proposal_packet_path: str


class _CoreIRProposerFixture(BaseModel):
    runs: list[_CoreIRProposerRun]


class _VnextPlus25ManifestForY4(BaseModel):
    schema: Literal["stop_gate.vnext_plus25_manifest@1"]
    core_ir_proposer_contract_valid_fixtures: list[_CoreIRProposerFixture]
    core_ir_proposer_provider_parity_fixtures: list[_CoreIRProposerFixture]


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _provider_matrix_fixture_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "provider_parity"
        / "vnext_plus25_provider_matrix.json"
    ).resolve()


def _provider_matrix_package_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "src"
        / "adeu_api"
        / "provider_parity"
        / "vnext_plus25_provider_matrix.json"
    ).resolve()


def _vnext_plus25_manifest_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus25_manifest.json"
    ).resolve()


def _resolve_manifest_payload_path(*, manifest_path: Path, raw_path: str) -> Path:
    payload_path = Path(raw_path)
    if not payload_path.is_absolute():
        payload_path = manifest_path.parent / payload_path
    return payload_path.resolve()


def _json_paths_under(path: Path) -> set[Path]:
    if not path.exists():
        return set()
    return {entry.resolve() for entry in path.rglob("*.json") if entry.is_file()}


def _vnext_plus25_manifest_referenced_paths() -> set[Path]:
    manifest_path = _vnext_plus25_manifest_path()
    manifest = _VnextPlus25ManifestForY4.model_validate(_load_json(manifest_path))

    paths: set[Path] = {manifest_path}
    fixtures = [
        *manifest.core_ir_proposer_contract_valid_fixtures,
        *manifest.core_ir_proposer_provider_parity_fixtures,
    ]
    for fixture in fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=manifest_path,
                    raw_path=run.core_ir_proposer_request_path,
                )
            )
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=manifest_path,
                    raw_path=run.core_ir_proposer_response_path,
                )
            )
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=manifest_path,
                    raw_path=run.core_ir_proposal_packet_path,
                )
            )
    return paths


def _y4_mutable_surface_paths() -> list[Path]:
    root = _repo_root()
    paths: set[Path] = {
        _provider_matrix_fixture_path(),
        _provider_matrix_package_path(),
        *_vnext_plus25_manifest_referenced_paths(),
    }

    # Canonical persisted fixture trees for continuity (concept/core-ir/lane/integrity,
    # cross-ir, normative-advice, trust-invariant, semantics-candidate).
    paths.update(_json_paths_under(root / "apps" / "api" / "fixtures" / "read_surface"))
    paths.update(_json_paths_under(root / "apps" / "api" / "fixtures" / "cross_ir"))
    paths.update(
        _json_paths_under(root / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus21")
    )
    paths.update(
        _json_paths_under(root / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus22")
    )
    paths.update(
        _json_paths_under(root / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus23")
    )

    return sorted(paths, key=lambda path: str(path))


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {
        str(path): sha256_canonical_json(_load_json(path))
        for path in _y4_mutable_surface_paths()
    }


def _raise_materialization_policy_flow_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            "core-ir proposer y4 fail-closed: materialization/policy flow invoked: "
            f"{target}"
        )

    return _fail


def _proposer_request(*, client_request_id: str) -> CoreIRProposerRequest:
    return CoreIRProposerRequest(
        schema="adeu_core_ir_proposer_request@0.1",
        client_request_id=client_request_id,
        provider="mock",
        source_text="The operator must log every override decision.",
    )


def _assert_payload_has_no_disallowed_fields(
    value: object,
    *,
    field_names: frozenset[str],
    _path: tuple[str | int, ...] = (),
) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in field_names:
                key_path = "/".join(str(part) for part in (*_path, key)) or "<root>"
                raise AssertionError(
                    f"disallowed field '{key}' found at path '{key_path}'"
                )
            _assert_payload_has_no_disallowed_fields(
                child,
                field_names=field_names,
                _path=(*_path, key),
            )
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _assert_payload_has_no_disallowed_fields(
                child,
                field_names=field_names,
                _path=(*_path, index),
            )


def _exercise_core_ir_proposer_endpoint_under_y4_guards(
    *,
    client_request_id: str,
) -> dict[str, Any]:
    with ExitStack() as stack:
        for target in _MATERIALIZATION_POLICY_FLOW_TARGETS:
            stack.enter_context(
                patch(target, new=_raise_materialization_policy_flow_call(target=target))
            )
        response = urm_core_ir_propose_endpoint(
            _proposer_request(client_request_id=client_request_id)
        )
    return response.model_dump(mode="json")


@pytest.fixture(autouse=True)
def _clear_core_ir_proposer_caches() -> None:
    api_main._provider_parity_supported_providers_by_surface.cache_clear()
    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()
    yield
    api_main._provider_parity_supported_providers_by_surface.cache_clear()
    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()


def test_core_ir_proposer_paths_are_materialization_and_policy_guarded() -> None:
    response_payload = _exercise_core_ir_proposer_endpoint_under_y4_guards(
        client_request_id="req-core-ir-proposer-y4-guard-1",
    )

    assert response_payload["schema"] == "adeu_core_ir_proposer_response@0.1"
    assert response_payload["surface_id"] == "adeu_core_ir.propose"


def test_core_ir_proposer_paths_do_not_mutate_vnext_plus25_fixture_surface() -> None:
    before_snapshot = _mutable_surface_snapshot_hashes()

    _exercise_core_ir_proposer_endpoint_under_y4_guards(
        client_request_id="req-core-ir-proposer-y4-snapshot-1",
    )

    after_snapshot = _mutable_surface_snapshot_hashes()
    assert before_snapshot == after_snapshot


def test_core_ir_proposer_payloads_remain_non_enforcing_and_trust_lane_stable() -> None:
    response_payload = _exercise_core_ir_proposer_endpoint_under_y4_guards(
        client_request_id="req-core-ir-proposer-y4-payload-1",
    )

    _assert_payload_has_no_disallowed_fields(
        response_payload,
        field_names=_NON_ENFORCEMENT_FIELD_NAMES,
    )
    _assert_payload_has_no_disallowed_fields(
        response_payload,
        field_names=_TRUST_LANE_FIELD_NAMES,
    )

    proposal_packet = response_payload["proposal_packet"]
    assert proposal_packet["schema"] == "adeu_core_ir_proposal@0.1"
    assert proposal_packet["surface_id"] == "adeu_core_ir.propose"
