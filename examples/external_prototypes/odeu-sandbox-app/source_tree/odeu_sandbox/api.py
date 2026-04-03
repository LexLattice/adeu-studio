from __future__ import annotations

from collections import Counter
from pathlib import Path
from typing import Any

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, Field

from .sim.engine import ODEUSimulation
from .sim.scenarios import DEFAULT_SCENARIO_NAME, list_scenarios

BASE_DIR = Path(__file__).resolve().parent
STATIC_DIR = BASE_DIR / "static"


class ResetRequest(BaseModel):
    scenario: str = DEFAULT_SCENARIO_NAME
    seed: int = 7
    overrides: dict[str, Any] = Field(default_factory=dict)


class StepRequest(BaseModel):
    steps: int = 1


app = FastAPI(title="ODEU Sandbox", version="0.1.0")
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)
app.mount("/static", StaticFiles(directory=STATIC_DIR), name="static")
app.state.sim = ODEUSimulation()


@app.get("/")
def root() -> FileResponse:
    return FileResponse(STATIC_DIR / "index.html")


@app.get("/api/scenarios")
def scenarios() -> list[dict[str, Any]]:
    return [scenario.model_dump(mode="json") for scenario in list_scenarios()]


@app.post("/api/reset")
def reset_simulation(request: ResetRequest) -> dict[str, Any]:
    app.state.sim.reset(request.scenario, seed=request.seed, overrides=request.overrides)
    return snapshot(app.state.sim.get_state())


@app.post("/api/step")
def step_simulation(request: StepRequest) -> dict[str, Any]:
    app.state.sim.step(request.steps)
    return snapshot(app.state.sim.get_state())


@app.get("/api/state")
def get_state() -> dict[str, Any]:
    return snapshot(app.state.sim.get_state())


def snapshot(world) -> dict[str, Any]:
    current_metric = world.metrics_history[-1]
    archetype_counts = Counter(agent.archetype.value for agent in world.agents)
    action_counts = Counter(action.action_type.value for action in world.planned_actions)
    edges = []
    for agent in world.agents:
        for neighbor, trust in agent.e_state.peer_trust.items():
            if agent.id < neighbor:
                edges.append({"source": agent.id, "target": neighbor, "weight": round(trust, 3)})

    return {
        "meta": {
            "turn": world.turn,
            "seed": world.seed,
            "scenario": world.scenario,
            "regime": current_metric.regime_label,
        },
        "config": world.config.model_dump(mode="json"),
        "lane_summary": world.last_run_summary,
        "institution": world.institution.model_dump(mode="json"),
        "current_metrics": current_metric.model_dump(mode="json"),
        "metrics_history": [metric.model_dump(mode="json") for metric in world.metrics_history],
        "agents": [
            {
                "id": agent.id,
                "archetype": agent.archetype.value,
                "resources": round(agent.o_state.resources, 3),
                "belief_commons": round(agent.e_state.belief_commons, 3),
                "uncertainty": round(agent.e_state.uncertainty, 3),
                "trust_institution": round(agent.e_state.trust_institution, 3),
                "trust_ai": round(agent.e_state.trust_ai, 3),
                "legitimacy_belief": round(agent.d_state.legitimacy_belief, 3),
                "fairness": round(agent.u_state.fairness, 3),
                "greed": round(agent.u_state.greed, 3),
                "last_action": agent.last_action,
                "neighbors": list(agent.e_state.peer_trust.keys()),
            }
            for agent in world.agents
        ],
        "network_edges": edges,
        "counts": {
            "archetypes": dict(archetype_counts),
            "actions": dict(action_counts),
            "pending_cases": len(world.pending_cases),
            "sanctions": len(world.sanction_events),
            "audits": len(world.audit_results),
            "claims": len(world.claims),
        },
        "recent_public_reports": [report.model_dump(mode="json") for report in world.public_reports[-8:]],
        "recent_claims": [claim.model_dump(mode="json") for claim in world.claims[-12:]],
        "recent_evidence": [evidence.model_dump(mode="json") for evidence in world.evidence_records[-12:]],
        "recent_actions": [action.model_dump(mode="json") for action in world.planned_actions[-20:]],
        "event_log": list(world.event_log[-40:]),
    }
