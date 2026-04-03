# ODEU Sandbox v0

A minimal browser-based simulation sandbox for ODEU dynamics.

It is intentionally small, but it still keeps the four lanes explicit in code:

- **O**: commons stock, agent resources, archive infrastructure, enforcement bottlenecks
- **E**: observations, evidence records, claims, public reports, trust, uncertainty, AI mediation
- **D**: norms, legitimacy, operativity, sanction consistency, appeal pathways, symbolic gap
- **U**: greed, fairness, long-term horizon, risk tolerance, sanction aversion

## What this version demonstrates

The included presets and controls can produce four main regime patterns:

- **Cooperative Legible Order** from the healthy baseline
- **Coercive Truth-Poor Order** from the coercive preset
- **Symbolic Institution Drift** from weak deontic capacity
- **Epistemic Capture Collapse** from sycophantic AI mediation or sufficiently weak epistemics

## Architecture

### Core modules

- `sim/models.py` — typed semantic objects
- `sim/actions.py` — action catalog with lane signatures
- `sim/scenarios.py` — preset configurations
- `sim/engine.py` — turn loop and O/E/D/U updates
- `sim/metrics.py` — observables
- `sim/regimes.py` — heuristic regime classifier
- `api.py` — FastAPI endpoints and static UI serving
- `static/` — no-build browser UI

### Cross-lane contracts implemented explicitly

- **O -> E trace contract**: material actions emit traces with probability based on observability, archive capacity, and public epistemics.
- **E -> D legitimacy contract**: audits, report truthfulness, and sanction fairness update legitimacy and sanction consistency.
- **D -> O allocation contract**: institutional budget, legitimacy, and operativity feed into archive and enforcement capacity.
- **U -> D pressure contract**: concentrated gains from weakly constrained opportunism increase capture pressure and erode operativity.

### Decision loop

Each agent action is selected through a visible four-stage gate:

1. `O` feasibility
2. `E` evaluation of belief and uncertainty
3. `D` evaluation of required/permitted/forbidden/contestable actions
4. `U` ranking among the surviving candidates

## Run locally

From the repo root:

```bash
python -m uvicorn odeu_sandbox.api:app --reload --port 8010
```

Then open:

```text
http://localhost:8010
```

## Run tests

```bash
pytest odeu_sandbox/tests -q
```

## Simplifications in v0

This is still a toy model.

What is simplified:

- one region only
- one commons resource only
- one institution only
- one public archive only
- one scalar hidden commons state instead of many hidden state families
- one action per agent per turn
- heuristic policies instead of richer learning or cultural evolution
- simple peer network and scalar trust updates
- heuristic regime classifier instead of learned phase detection

What remains essential:

- typed ontology objects
- stratified epistemic artifacts: observation, evidence, claim, public report
- real deontic kernel with obligation/prohibition/permission/role-duty, sanction path, appeal path, legitimacy, operativity
- symbolic-vs-operative institution diagnostic
- explicit lane-crossing contracts
- live metrics and scenario presets
