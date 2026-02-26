from __future__ import annotations

import adeu_api.main as api_main
import pytest
from adeu_api.main import CoreIRProposerRequest, urm_core_ir_propose_endpoint
from fastapi import HTTPException


@pytest.fixture(autouse=True)
def _clear_caches() -> None:
    api_main._provider_parity_supported_providers_by_surface.cache_clear()
    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()
    yield
    api_main._provider_parity_supported_providers_by_surface.cache_clear()
    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()


def test_core_ir_proposer_endpoint_returns_schema_valid_response() -> None:
    response = urm_core_ir_propose_endpoint(
        CoreIRProposerRequest(
            schema="adeu_core_ir_proposer_request@0.1",
            client_request_id="req-core-ir-proposer-y2-1",
            provider="mock",
            source_text="The operator must log every override decision.",
        )
    ).model_dump(mode="json")

    assert response["schema"] == "adeu_core_ir_proposer_response@0.1"
    assert response["surface_id"] == "adeu_core_ir.propose"
    assert response["provider"]["kind"] == "mock"
    assert "candidates" in response
    assert response["proposal_packet"]["schema"] == "adeu_core_ir_proposal@0.1"
    assert response["proposal_packet"]["surface_id"] == "adeu_core_ir.propose"
    assert response["proposal_packet"]["summary"]["candidate_count"] == len(response["candidates"])


def test_core_ir_proposer_endpoint_idempotent_replay_is_byte_identical() -> None:
    request = CoreIRProposerRequest(
        schema="adeu_core_ir_proposer_request@0.1",
        client_request_id="req-core-ir-proposer-y2-idem-1",
        provider="mock",
        source_text="The operator must log every override decision.",
    )

    first = urm_core_ir_propose_endpoint(request).model_dump(mode="json")
    second = urm_core_ir_propose_endpoint(request).model_dump(mode="json")

    assert second == first


def test_core_ir_proposer_endpoint_idempotency_conflict_on_semantic_payload_change() -> None:
    first = CoreIRProposerRequest(
        schema="adeu_core_ir_proposer_request@0.1",
        client_request_id="req-core-ir-proposer-y2-conflict-1",
        provider="mock",
        source_text="The operator must log every override decision.",
    )
    second = CoreIRProposerRequest(
        schema="adeu_core_ir_proposer_request@0.1",
        client_request_id="req-core-ir-proposer-y2-conflict-1",
        provider="mock",
        source_text="The operator may skip override logs when idle.",
    )

    _ = urm_core_ir_propose_endpoint(first)
    with pytest.raises(HTTPException) as exc_info:
        urm_core_ir_propose_endpoint(second)

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_CORE_IR_PROPOSER_REQUEST_INVALID"
    assert "different semantic payload" in exc_info.value.detail["reason"]


def test_core_ir_proposer_endpoint_same_client_request_id_different_provider_fails_closed() -> None:
    first = CoreIRProposerRequest(
        schema="adeu_core_ir_proposer_request@0.1",
        client_request_id="req-core-ir-proposer-y2-provider-conflict-1",
        provider="mock",
        source_text="The operator must log every override decision.",
    )
    second = CoreIRProposerRequest(
        schema="adeu_core_ir_proposer_request@0.1",
        client_request_id="req-core-ir-proposer-y2-provider-conflict-1",
        provider="codex",
        source_text="The operator must log every override decision.",
    )

    _ = urm_core_ir_propose_endpoint(first)
    with pytest.raises(HTTPException) as exc_info:
        urm_core_ir_propose_endpoint(second)

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_CORE_IR_PROPOSER_REQUEST_INVALID"
    assert "different provider" in exc_info.value.detail["reason"]


def test_core_ir_proposer_surface_provider_unsupported_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        api_main,
        "_provider_parity_supported_providers_by_surface",
        lambda: {_api_main_surface_id(): ("mock",)},
    )

    with pytest.raises(HTTPException) as exc_info:
        urm_core_ir_propose_endpoint(
            CoreIRProposerRequest(
                schema="adeu_core_ir_proposer_request@0.1",
                client_request_id="req-core-ir-proposer-y2-unsupported-1",
                provider="codex",
                source_text="The operator must log every override decision.",
            )
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_ADEU_CORE_IR_PROPOSER_PROVIDER_UNSUPPORTED"
    assert exc_info.value.detail["urm_code"] == "URM_ADEU_CORE_IR_PROPOSER_PROVIDER_UNSUPPORTED"
    assert exc_info.value.detail["surface_id"] == "adeu_core_ir.propose"


def _api_main_surface_id() -> str:
    return api_main._CORE_IR_PROPOSER_SURFACE_ID
