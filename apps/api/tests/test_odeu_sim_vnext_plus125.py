from __future__ import annotations

import asyncio
import json
from pathlib import Path
from typing import Any

import adeu_api.main as api_main
import adeu_api.odeu_sim as odeu_sim_module
from fastapi import FastAPI


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v51b" / name


def _asgi_post_json(*, app: FastAPI, path: str, payload: Any) -> tuple[int, Any]:
    body_bytes = json.dumps(payload).encode("utf-8")
    scope = {
        "type": "http",
        "asgi": {"version": "3.0", "spec_version": "2.3"},
        "http_version": "1.1",
        "method": "POST",
        "scheme": "http",
        "path": path,
        "raw_path": path.encode("ascii"),
        "query_string": b"",
        "headers": [
            (b"host", b"testserver"),
            (b"content-type", b"application/json"),
            (b"content-length", str(len(body_bytes)).encode("ascii")),
        ],
        "client": ("testclient", 50000),
        "server": ("testserver", 80),
    }
    events = [{"type": "http.request", "body": body_bytes, "more_body": False}]
    sent: list[dict[str, Any]] = []

    async def _receive() -> dict[str, Any]:
        if events:
            return events.pop(0)
        return {"type": "http.disconnect"}

    async def _send(message: dict[str, Any]) -> None:
        sent.append(message)

    async def _invoke() -> None:
        await app(scope, _receive, _send)

    asyncio.run(_invoke())
    start_message = next(message for message in sent if message["type"] == "http.response.start")
    body = b"".join(
        message.get("body", b"") for message in sent if message["type"] == "http.response.body"
    )
    return int(start_message["status"]), json.loads(body.decode("utf-8"))


def test_build_odeu_run_response_matches_healthy_baseline_fixture() -> None:
    response = odeu_sim_module.build_odeu_run_response(
        {
            "scenario_name": "healthy_baseline",
            "seed": 7,
            "steps": 25,
            "output_mode": "summary_only_json",
        }
    )
    fixture = json.loads(
        _fixture_path("reference_odeu_run_response_healthy_baseline.json").read_text()
    )
    assert response.model_dump(mode="json", by_alias=True) == fixture


def test_build_odeu_run_response_matches_weak_d_fixture() -> None:
    response = odeu_sim_module.build_odeu_run_response(
        {
            "scenario_name": "weak_d",
            "seed": 7,
            "steps": 25,
            "output_mode": "summary_only_json",
        }
    )
    fixture = json.loads(_fixture_path("reference_odeu_run_response_weak_d.json").read_text())
    assert response.model_dump(mode="json", by_alias=True) == fixture


def test_build_odeu_run_response_fails_closed_on_negative_seed() -> None:
    response = odeu_sim_module.build_odeu_run_response(
        {
            "scenario_name": "healthy_baseline",
            "seed": -1,
            "steps": 25,
            "output_mode": "summary_only_json",
        }
    )
    fixture = json.loads(
        _fixture_path("reference_odeu_run_response_invalid_negative_seed.json").read_text()
    )
    assert response.model_dump(mode="json", by_alias=True) == fixture


def test_build_odeu_run_response_fails_closed_on_kernel_projection_mismatch(
    monkeypatch,
) -> None:
    monkeypatch.setattr(
        odeu_sim_module,
        "summarize_lane_state",
        lambda _world: {"mean_legitimacy_belief": 0.1, "mean_resources": 1.0},
    )
    response = odeu_sim_module.build_odeu_run_response(
        {
            "scenario_name": "healthy_baseline",
            "seed": 7,
            "steps": 25,
            "output_mode": "summary_only_json",
        }
    )
    fixture = json.loads(
        _fixture_path("reference_odeu_run_response_kernel_mismatch.json").read_text()
    )
    assert response.model_dump(mode="json", by_alias=True) == fixture


def test_build_odeu_run_response_uses_released_stateless_kernel_helper(monkeypatch) -> None:
    calls: list[tuple[str, int, int]] = []
    original = odeu_sim_module.run_canonical_scenario

    def _spy(scenario_name: str, *, seed: int, steps: int):
        calls.append((scenario_name, seed, steps))
        return original(scenario_name, seed=seed, steps=steps)

    monkeypatch.setattr(odeu_sim_module, "run_canonical_scenario", _spy)
    response = odeu_sim_module.build_odeu_run_response(
        {
            "scenario_name": "healthy_baseline",
            "seed": 7,
            "steps": 25,
            "output_mode": "summary_only_json",
        }
    )
    assert response.request_status == "completed_clean"
    assert calls == [("healthy_baseline", 7, 25)]


def test_route_is_registered_on_main_app() -> None:
    paths = {route.path for route in api_main.app.routes}
    assert "/odeu-sim/run" in paths


def test_odeu_run_route_returns_typed_invalid_request_artifact() -> None:
    app = FastAPI()
    app.include_router(odeu_sim_module.router)
    status_code, payload = _asgi_post_json(
        app=app,
        path="/odeu-sim/run",
        payload={
            "scenario_name": "unsupported",
            "seed": 7,
            "steps": 25,
            "output_mode": "summary_only_json",
        },
    )
    assert status_code == 200
    assert payload["schema"] == "adeu_odeu_run_response@1"
    assert payload["request_status"] == "fail_closed_invalid_request"
    assert payload["failure_code"] == "ODEU_SIM_INVALID_REQUEST"
