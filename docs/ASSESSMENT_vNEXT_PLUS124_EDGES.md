# Assessment vNext+124 Edges

Status: pre-lock edge assessment for `V51-A` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS124_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Prose-Soft Lane Collapse

- Risk:
  the kernel could reintroduce O/E/D/U semantics only through comments or heuristics
  rather than typed contracts.
- Planned Response:
  freeze the starter lane-crossing contracts as explicit typed kernel law and require
  them in live code, not just support docs.

### Edge 2: World-State Blob Laundering

- Risk:
  the key nested kernel objects could disappear into one broad `world_state` payload,
  leaving most of the actual ontology implicit in code.
- Planned Response:
  freeze the key lane-state, agent, institution, resource, norm, and evidence/event
  carriers as first-class typed models inside `models.py`.

### Edge 3: Determinism Drift

- Risk:
  ambient randomness or implicit initial-state variation could make replay unstable
  even with the same named scenario.
- Planned Response:
  freeze exact replay law over scenario + seed + initial state and reject unseeded
  randomness in `V51-A`.

### Edge 4: Event-Log Looseness

- Risk:
  replay diagnostics could rely only on a list of free-form strings, making later
  comparison and verification weaker than the rest of the typed kernel surface.
- Planned Response:
  replace string-only event logs with typed event-record carriers in the first slice.

### Edge 5: Regime-Classifier Overclaim

- Risk:
  heuristic regime outputs could be overread as control authority, optimization
  targets, or semantic ground truth.
- Planned Response:
  keep regime labels bounded as heuristic diagnostics only.

### Edge 6: Starter-Scenario Drift

- Risk:
  the first kernel slice could quietly widen from a bounded scenario set into a loose
  sandbox without explicit replay obligations.
- Planned Response:
  freeze exact starter scenarios in the first lock:
  `healthy_baseline` and `weak_d`.

### Edge 7: Tie-Break Drift

- Risk:
  deterministic replay claims could still drift if agent iteration order or
  action-selection tie-break behavior stays implicit.
- Planned Response:
  freeze deterministic agent-order and action tie-break law in the lock and require
  dedicated replay tests.

### Edge 8: Share-Validation Drift

- Risk:
  archetype-share validation could remain only a reject-fixture intuition rather than
  an explicit scenario-config contract.
- Planned Response:
  freeze exact share-allocation validation:
  each share between `0.0` and `1.0`, with total share sum equal to `1.0`.

### Edge 9: Consumer Prematurity

- Risk:
  FastAPI or browser UI surfaces could leak into the kernel slice and blur family
  ownership before the package contract is accepted.
- Planned Response:
  keep `V51-A` package-only and defer API/UI consumers to later family paths.

### Edge 10: Prototype App Precedent Laundering

- Risk:
  the imported sandbox app could be copied into live paths or treated as released
  authority rather than shaping evidence.
- Planned Response:
  keep the bundle support-only and re-author the live kernel in repo-native package
  form.

### Edge 11: Dependency Smuggling

- Risk:
  the first kernel slice could quietly make released `V49` or `V50` surfaces mandatory
  kernel dependencies without an explicit lock decision.
- Planned Response:
  keep those families adjacent context only in `V51-A` unless a later lock selects a
  stronger dependency.
