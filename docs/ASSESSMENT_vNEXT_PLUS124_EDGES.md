# Assessment vNext+124 Edges

Status: post-closeout edge assessment for `V51-A` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS124_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Prose-Soft Lane Collapse

- Risk:
  the kernel could reintroduce O/E/D/U semantics only through comments or heuristics
  rather than typed contracts.
- Response:
  keep the starter lane-crossing contracts as explicit typed kernel law in the live
  package, not just support-doc prose.
- Closeout Evidence:
  `LaneCrossingContractKind` and `LaneCrossingContract` in
  `packages/adeu_odeu_sim/src/adeu_odeu_sim/models.py`,
  `ACTION_LIBRARY` in `packages/adeu_odeu_sim/src/adeu_odeu_sim/actions.py`, and
  the deterministic engine tests in `packages/adeu_odeu_sim/tests/test_odeu_sim_engine.py`.

### Edge 2: World-State Blob Laundering

- Risk:
  the key nested kernel objects could disappear into one broad `world_state` payload,
  leaving most of the actual ontology implicit in code.
- Response:
  freeze the key lane-state, agent, institution, resource, norm, action,
  evidence/event, and world-state carriers as first-class typed models inside
  `models.py`.
- Closeout Evidence:
  `OState`, `EState`, `DState`, `UState`, `Agent`, `ResourcePool`, `Institution`,
  `Norm`, `Action`, `EventRecord`, and `WorldState` in
  `packages/adeu_odeu_sim/src/adeu_odeu_sim/models.py`.

### Edge 3: Determinism Drift

- Risk:
  ambient randomness or implicit initial-state variation could make replay unstable
  even with the same named scenario.
- Response:
  freeze exact replay law over scenario + seed + initial state, reject unseeded
  randomness, and keep canonical replay fixtures on the released slice.
- Closeout Evidence:
  `CANONICAL_REPLAY_SEED = 7`, `CANONICAL_REPLAY_HORIZON = 25`, and the exact replay
  tests plus committed `v51a` fixture summaries.

### Edge 4: Event-Log Looseness

- Risk:
  replay diagnostics could rely only on a list of free-form strings, making later
  comparison and verification weaker than the rest of the typed kernel surface.
- Response:
  keep typed event-record carriers in the first slice and record replay-relevant
  events through the engine.
- Closeout Evidence:
  `EventRecordKind`, `EventRecord`, `_record_event(...)`, and the deterministic event
  counts in the committed fixture summaries.

### Edge 5: Regime-Classifier Overclaim

- Risk:
  heuristic regime outputs could be overread as control authority, optimization
  targets, or semantic ground truth.
- Response:
  keep regime labels bounded as heuristic diagnostics only.
- Closeout Evidence:
  `packages/adeu_odeu_sim/src/adeu_odeu_sim/regimes.py`,
  `MetricPoint.regime_label`, and `test_regime_signatures_match_starter_scenarios`.

### Edge 6: Starter-Scenario Drift

- Risk:
  the first kernel slice could quietly widen from a bounded scenario set into a loose
  sandbox without explicit replay obligations.
- Response:
  freeze exact starter scenarios in the released slice:
  `healthy_baseline` and `weak_d`.
- Closeout Evidence:
  `SCENARIOS` in `packages/adeu_odeu_sim/src/adeu_odeu_sim/scenarios.py`,
  the scenario tests, and the committed replay fixtures.

### Edge 7: Tie-Break Drift

- Risk:
  deterministic replay claims could still drift if agent iteration order or
  action-selection tie-break behavior stays implicit.
- Response:
  freeze deterministic agent-order and action tie-break law and keep dedicated replay
  regressions in the released package.
- Closeout Evidence:
  `test_agent_iteration_order_is_frozen_by_agent_id` and
  `test_sanction_target_tiebreak_is_deterministic`.

### Edge 8: Share-Validation Drift

- Risk:
  archetype-share validation could remain only a reject-fixture intuition rather than
  an explicit scenario-config contract.
- Response:
  freeze exact share-allocation validation:
  each share between `0.0` and `1.0`, with total share sum equal to `1.0`.
- Closeout Evidence:
  `ScenarioConfig` validation in
  `packages/adeu_odeu_sim/src/adeu_odeu_sim/models.py`.

### Edge 9: Replay-State Bookkeeping Drift

- Risk:
  initialization and epistemic follow-on state could land on stale world objects or
  stay unset, weakening deterministic replay claims even if core metrics still pass.
- Response:
  keep replay-state bookkeeping explicit and regression-tested.
- Closeout Evidence:
  initialization-event attachment in `_build_world(...)`, `actor.last_action` updates
  in `_apply_action(...)`, and the corresponding regressions in
  `test_odeu_sim_engine.py`.

### Edge 10: Consumer Prematurity

- Risk:
  FastAPI or browser UI surfaces could leak into the kernel slice and blur family
  ownership before the package contract is accepted.
- Response:
  keep `V51-A` package-only and defer API/UI consumers to later family paths.
- Closeout Evidence:
  implementation footprint limited to `packages/adeu_odeu_sim`, tests, fixtures, the
  bootstrap `Makefile` edit, and closeout artifacts only.

### Edge 11: Prototype App Precedent Laundering

- Risk:
  the imported sandbox app could be copied into live paths or treated as released
  authority rather than shaping evidence.
- Response:
  keep the bundle support-only and re-author the live kernel in repo-native package
  form.
- Closeout Evidence:
  shipped code exists only under `packages/adeu_odeu_sim`, while the imported bundle
  remains under `examples/external_prototypes/odeu-sandbox-app`.

### Edge 12: Dependency Smuggling

- Risk:
  the first kernel slice could quietly make released `V49` or `V50` surfaces mandatory
  kernel dependencies without an explicit lock decision.
- Response:
  keep those families adjacent context only in `V51-A` unless a later lock selects a
  stronger dependency.
- Closeout Evidence:
  the released package is self-contained inside `packages/adeu_odeu_sim` and does not
  import `adeu_semantic_forms` or `adeu_symbol_audit` as kernel requirements.

## Current Judgment

- `V51-A` was the right first C-track move because it froze the kernel law before the
  repo accepted any API or browser surface.
- the shipped result is properly narrow: one repo-owned `adeu_odeu_sim` package, one
  bounded starter domain, exact `healthy_baseline` and `weak_d` scenario replay,
  canonical seed `7` and horizon `25`, first-class typed submodels, typed
  lane-crossing contracts, typed event records, heuristic regime diagnostics, and no
  API/UI or persistent storage.
- review hardening materially improved the release: replay-state bookkeeping is now
  explicit on reset/verify paths, and invalid empty-agent worlds fail closed instead
  of returning misleading aggregate values.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` should now be read with `V51-A` closed on
  `main` and the branch-local default next path advanced to `V51-B` / `vNext+125`.
