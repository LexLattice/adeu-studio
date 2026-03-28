# Draft Stop-Gate Decision (Post vNext+91)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS91.md`

Status: draft decision note (post-hoc closeout capture, March 28, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS91.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v91_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+91` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS91.md`.
- This note captures `V42-C` closeout evidence only; it does not authorize
  scorecard/replay manifest release, competition-mode integration, benchmark-tournament
  widening, API/web operator routes, or leaderboard-readiness claims beyond the bounded
  action/rollout seam.
- Canonical `V42-C` release in v91 is carried by the `packages/adeu_arc_agi` and
  `packages/adeu_arc_solver` action/rollout surfaces, deterministic fixture replay under
  `apps/api/fixtures/arc_agi/vnext_plus91/`, and the canonical
  `v42c_arc_action_rollout_evidence@1` evidence input under
  `artifacts/agent_harness/v91/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `4269714a2bbcde983018ddeaea74b1dc908a5acd`
- merged implementation PRs:
  - `#313` (`Implement v91 V42-C ARC action proposal + rollout trace baseline`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v91_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v91_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v91_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v91/evidence_inputs/metric_key_continuity_assertion_v91.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v91/evidence_inputs/runtime_observability_comparison_v91.json`
  - `V42-C` action/rollout evidence input:
    `artifacts/agent_harness/v91/evidence_inputs/v42c_arc_action_rollout_evidence_v91.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v91/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS91_EDGES.md`

## Exit-Criteria Check (vNext+91)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V42-C` merged with green CI | required | `pass` | PR `#313`, merge commit `4269714a2bbcde983018ddeaea74b1dc908a5acd` |
| Canonical `adeu_arc_action_proposal@1` and `adeu_arc_rollout_trace@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_arc_agi/schema/adeu_arc_action_proposal.v1.json`, `packages/adeu_arc_agi/schema/adeu_arc_rollout_trace.v1.json`, `spec/adeu_arc_action_proposal.schema.json`, `spec/adeu_arc_rollout_trace.schema.json` |
| Action-proposal decision basis and utility posture are explicit and machine-checkable | required | `pass` | `proposal_status`, decision-basis fields, utility posture, and alternative-action register constraints in `test_arc_action_rollout_v42c.py` |
| Structured expectation surfaces and expectation identity are preserved into rollout | required | `pass` | `expectation_surface_hash` carry-through and rewrite-rejection checks in `test_arc_action_rollout_v42c.py` plus rejected v91 fixture |
| Rollout lineage remains deterministic with pre/post state refs and expectation-outcome comparison | required | `pass` | accepted v91 rollout fixture and solver/agi replay tests |
| Blocked/deferred posture is preserved without forced committed action | required | `pass` | `proposal_status` enum + fail-closed validator rules and rejected fixture coverage |
| Retroactive necessity laundering is rejected | required | `pass` | rejected `adeu_arc_rollout_trace_v91_reject_retroactive_necessity_laundering.json` fixture and validator rejection path |
| Scorecard/replay/competition leakage deferred | required | `pass` | bounded `V42-C` implementation and hard-constraint-preserving fixture/test surface |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v91_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v91/evidence_inputs/metric_key_continuity_assertion_v91.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v91/evidence_inputs/runtime_observability_comparison_v91.json` |

## Stop-Gate Summary

```json
{
  "schema": "v91_closeout_stop_gate_summary@1",
  "arc": "vNext+91",
  "target_path": "V42-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v90": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 90,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v90_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v91_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+90","baseline_elapsed_ms":90,"baseline_source":"artifacts/stop_gate/report_v90_closeout.md","current_arc":"vNext+91","current_elapsed_ms":90,"current_source":"artifacts/stop_gate/report_v91_closeout.md","delta_ms":0,"notes":"v91 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V42-C ARC action/rollout baseline on main.","schema":"runtime_observability_comparison@1"}
```

## V42C Action/Rollout Evidence

```json
{"schema":"v42c_arc_action_rollout_evidence@1","evidence_input_path":"artifacts/agent_harness/v91/evidence_inputs/v42c_arc_action_rollout_evidence_v91.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS91.md#v91-continuation-contract-machine-checkable","merged_pr":"#313","merge_commit":"4269714a2bbcde983018ddeaea74b1dc908a5acd","action_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_action_proposal.v1.json","rollout_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_rollout_trace.v1.json","accepted_action_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus91/adeu_arc_action_proposal_v91_reference.json","accepted_rollout_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus91/adeu_arc_rollout_trace_v91_reference.json"}
```

## Recommendation (Post v91)

- gate decision:
  - `V42C_ACTION_ROLLOUT_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v91 closes the bounded `V42-C` baseline with explicit action proposal
    decision-basis/utility posture, structured expectation surfaces, deterministic
    rollout lineage, expectation-to-outcome identity carry-through, and fail-closed
    rejection of hidden tactical laundering and post-hoc expectation rewrite on `main`.
  - no scorecard/replay/competition widening shipped in v91.
  - no stop-gate schema-family or metric-key regressions were introduced; runtime
    observability changed only informationally.
  - the next default seam now belongs to `V42-D` local benchmark/eval widening rather
    than another `V42-C` continuation.
