from __future__ import annotations

from fastapi.testclient import TestClient

from odeu_sandbox.api import app


client = TestClient(app)


def test_root_serves_html() -> None:
    response = client.get("/")
    assert response.status_code == 200
    assert "ODEU Sandbox" in response.text


def test_reset_and_step_endpoints() -> None:
    reset = client.post(
        "/api/reset",
        json={
            "scenario": "healthy_baseline",
            "seed": 7,
            "overrides": {"misinformation": 0.2},
        },
    )
    assert reset.status_code == 200
    payload = reset.json()
    assert payload["meta"]["turn"] == 0
    assert payload["config"]["misinformation"] == 0.2
    assert "O" in payload["lane_summary"]

    stepped = client.post("/api/step", json={"steps": 3})
    assert stepped.status_code == 200
    payload = stepped.json()
    assert payload["meta"]["turn"] == 3
    assert len(payload["metrics_history"]) >= 4
    assert payload["recent_actions"]


def test_scenarios_endpoint_lists_presets() -> None:
    response = client.get("/api/scenarios")
    assert response.status_code == 200
    names = {item["name"] for item in response.json()}
    assert {
        "healthy_baseline",
        "weak_e",
        "weak_d",
        "weak_e_weak_d",
        "coercive_truth_poor_order",
        "ai_mediated_epistemics",
    }.issubset(names)
