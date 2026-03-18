from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_api.urm_routes import urm_reflex_compile_endpoint
from adeu_core_ir import AdeuBrokeredReflexivePayload
from fastapi import HTTPException


def _fixtures_root() -> Path:
    return (
        Path(__file__).resolve().parents[1]
        / "fixtures"
        / "brokered_reflexive_execution"
        / "vnext_plus71"
    )


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _payload() -> dict[str, object]:
    return _load_json(_fixtures_root() / "adeu_brokered_reflexive_payload.json")


def test_urm_reflex_compile_endpoint_returns_brokered_execution_plan() -> None:
    expected = _load_json(_fixtures_root() / "adeu_brokered_reflexive_execution_plan.json")
    response = urm_reflex_compile_endpoint(
        AdeuBrokeredReflexivePayload.model_validate(_payload()),
        provider="codex",
        role="copilot",
    )

    assert response.model_dump(mode="json", by_alias=True) == expected


def test_urm_reflex_compile_endpoint_denies_role_without_capability() -> None:
    with pytest.raises(HTTPException) as exc_info:
        urm_reflex_compile_endpoint(
            AdeuBrokeredReflexivePayload.model_validate(_payload()),
            provider="codex",
            role="pipeline_worker",
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_POLICY_DENIED"
