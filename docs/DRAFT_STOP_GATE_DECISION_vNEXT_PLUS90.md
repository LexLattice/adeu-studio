# Draft Stop-Gate Decision (Post vNext+90)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS90.md`

Status: draft decision note (post-hoc closeout capture, March 28, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS90.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v90_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+90` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS90.md`.
- This note captures `V42-B` closeout evidence only; it does not authorize
  action-proposal/rollout release, scorecard/replay authority, competition-mode
  integration, API/web operator routes, or benchmark-tournament widening beyond the
  bounded observation/hypothesis seam.
- Canonical `V42-B` release in v90 is carried by the `packages/adeu_arc_agi` and
  `packages/adeu_arc_solver` observation/hypothesis surfaces, deterministic fixture
  replay under `apps/api/fixtures/arc_agi/vnext_plus90/`, and the canonical
  `v42b_arc_observation_hypothesis_evidence@1` evidence input under
  `artifacts/agent_harness/v90/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `02e04ada5b572832bfc25e9c96cb18f3b83fa2d8`
- merged implementation PRs:
  - `#312` (`Implement v90 V42-B ARC observation+hypothesis baseline`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v90_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v90_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v90_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v90/evidence_inputs/metric_key_continuity_assertion_v90.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v90/evidence_inputs/runtime_observability_comparison_v90.json`
  - `V42-B` observation/hypothesis evidence input:
    `artifacts/agent_harness/v90/evidence_inputs/v42b_arc_observation_hypothesis_evidence_v90.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v90/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS90_EDGES.md`

## Exit-Criteria Check (vNext+90)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V42-B` merged with green CI | required | `pass` | PR `#312`, merge commit `02e04ada5b572832bfc25e9c96cb18f3b83fa2d8` |
| Canonical `adeu_arc_observation_frame@1` and `adeu_arc_hypothesis_frame@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_arc_agi/schema/adeu_arc_observation_frame.v1.json`, `packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json`, `spec/adeu_arc_observation_frame.schema.json`, `spec/adeu_arc_hypothesis_frame.schema.json` |
| Ontology decomposition is first-class and inspectable | required | `pass` | `ontology_register`, entity/relation/partition inventories, and ontology uncertainty in observation frame model + accepted v90 fixture |
| Derived observation/hypothesis separation is fail-closed | required | `pass` | rejected bleed fixture and validator rejection in `test_arc_observation_hypothesis_v42b.py` |
| Utility pressure and non-committing working-hypothesis posture are explicit | required | `pass` | `utility_pressure_register` and `working_hypothesis_posture` constraints in hypothesis frame model + tests |
| Deterministic replay and fail-closed posture retained | required | `pass` | accepted/rejected v90 fixtures plus replay/validation tests across `adeu_arc_agi` and `adeu_arc_solver` |
| Action/rollout/scorecard/competition leakage deferred | required | `pass` | bounded `V42-B` implementation and hard-constraint-preserving fixture/test surface |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v90_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v90/evidence_inputs/metric_key_continuity_assertion_v90.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v90/evidence_inputs/runtime_observability_comparison_v90.json` |

## Stop-Gate Summary

```json
{
  "schema": "v90_closeout_stop_gate_summary@1",
  "arc": "vNext+90",
  "target_path": "V42-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v89": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 90,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v89_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v90_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+89","baseline_elapsed_ms":90,"baseline_source":"artifacts/stop_gate/report_v89_closeout.md","current_arc":"vNext+90","current_elapsed_ms":90,"current_source":"artifacts/stop_gate/report_v90_closeout.md","delta_ms":0,"notes":"v90 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V42-B ARC observation/hypothesis baseline on main.","schema":"runtime_observability_comparison@1"}
```

## V42B Observation/Hypothesis Evidence

```json
{"schema":"v42b_arc_observation_hypothesis_evidence@1","evidence_input_path":"artifacts/agent_harness/v90/evidence_inputs/v42b_arc_observation_hypothesis_evidence_v90.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS90.md#v90-continuation-contract-machine-checkable","merged_pr":"#312","merge_commit":"02e04ada5b572832bfc25e9c96cb18f3b83fa2d8","observation_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_observation_frame.v1.json","hypothesis_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json","accepted_observation_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_observation_frame_v90_reference.json","accepted_hypothesis_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_hypothesis_frame_v90_reference.json","rejected_hypothesis_bleed_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_observation_frame_v90_reject_hypothesis_bleed.json"}
```

## Recommendation (Post v90)

- gate decision:
  - `V42B_OBSERVATION_HYPOTHESIS_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v90 closes the bounded `V42-B` baseline with first-class ontology decomposition
    inventory, denominator-bound decomposition coverage, explicit direct-vs-derived
    observation typing, explicit ambiguity and claim posture carry-through, explicit
    utility pressure posture, and fail-closed rejection of observation/hypothesis bleed
    and unsupported impossibility posture on `main`.
  - no action-proposal/rollout/scorecard/competition widening shipped in v90.
  - no stop-gate schema-family or metric-key regressions were introduced; runtime
    observability changed only informationally.
  - the next default seam now belongs to `V42-C` action/rollout widening rather than
    another `V42-B` continuation.
