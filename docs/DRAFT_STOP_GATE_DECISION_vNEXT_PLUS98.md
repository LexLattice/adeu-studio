# Draft Stop-Gate Decision (Post vNext+98)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS98.md`

Status: draft decision note (post-hoc closeout capture, March 29, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS98.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v98_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+98` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS98.md`.
- This note captures `V42-G4` closeout evidence only; it does not authorize benchmark
  tournament execution, API/web operator routes, or generalized
  multi-agent/multi-benchmark orchestration.
- Canonical `V42-G4` release in v98 is carried by the
  `packages/adeu_arc_agi`/`packages/adeu_arc_solver` behavior-evidence bundle surfaces,
  deterministic fixture replay under `apps/api/fixtures/arc_agi/vnext_plus98/`, and
  the canonical `v42g4_arc_behavior_evidence_bundle_evidence@1` evidence input under
  `artifacts/agent_harness/v98/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `d11f6ddfadcb74cb50a6eb90c3e0dd11fe32590f`
- merged implementation PRs:
  - `#320` (`V42-G4: implement v98 behavior evidence bundle`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v98_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v98_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v98_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v98/evidence_inputs/metric_key_continuity_assertion_v98.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v98/evidence_inputs/runtime_observability_comparison_v98.json`
  - `V42-G4` behavior-evidence input:
    `artifacts/agent_harness/v98/evidence_inputs/v42g4_arc_behavior_evidence_bundle_evidence_v98.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v98/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS98_EDGES.md`

## Exit-Criteria Check (vNext+98)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V42-G4` merged with green CI | required | `pass` | PR `#320`, merge commit `d11f6ddfadcb74cb50a6eb90c3e0dd11fe32590f` |
| Canonical `adeu_arc_behavior_evidence_bundle@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_arc_agi/schema/adeu_arc_behavior_evidence_bundle.v1.json`, `spec/adeu_arc_behavior_evidence_bundle.schema.json` |
| Deterministic bundle replay over accepted fixture is stable | required | `pass` | replay checks in `packages/adeu_arc_agi/tests/test_arc_behavior_evidence_bundle_v42g4.py` and accepted fixture `apps/api/fixtures/arc_agi/vnext_plus98/adeu_arc_behavior_evidence_bundle_v98_reference.json` |
| Bundle materializes exactly three canonical per-puzzle behavior entries | required | `pass` | exact-length + canonical-index constraints in `packages/adeu_arc_agi/src/adeu_arc_agi/behavior_evidence_bundle.py` |
| Harness/order/anchor/claim/authority contradictions are rejected fail-closed | required | `pass` | rejected fixtures under `apps/api/fixtures/arc_agi/vnext_plus98/` and corresponding rejection assertions in `test_arc_behavior_evidence_bundle_v42g4.py` |
| Cross-puzzle synthesis remains support-bound and non-authoritative | required | `pass` | cross-pattern support/ref checks and authority-boundary checks in `behavior_evidence_bundle.py` |
| Deterministic replay overclaim (`deterministic_fresh_model_reexecution`) is rejected fail-closed | required | `pass` | forbidden-term validation in `behavior_evidence_bundle.py` and regression test `test_v98_rejects_forbidden_reexecution_term_in_replay_scope_note` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v98_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v98/evidence_inputs/metric_key_continuity_assertion_v98.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v98/evidence_inputs/runtime_observability_comparison_v98.json` |

## Stop-Gate Summary

```json
{
  "schema": "v98_closeout_stop_gate_summary@1",
  "arc": "vNext+98",
  "target_path": "V42-G4",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v97": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 83,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v97_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v98_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+97","baseline_elapsed_ms":83,"baseline_source":"artifacts/stop_gate/report_v97_closeout.md","current_arc":"vNext+98","current_elapsed_ms":83,"current_source":"artifacts/stop_gate/report_v98_closeout.md","delta_ms":0,"notes":"v98 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V42-G4 behavior-evidence baseline on main.","schema":"runtime_observability_comparison@1"}
```

## V42G4 Behavior-Evidence Bundle Evidence

```json
{"schema":"v42g4_arc_behavior_evidence_bundle_evidence@1","evidence_input_path":"artifacts/agent_harness/v98/evidence_inputs/v42g4_arc_behavior_evidence_bundle_evidence_v98.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS98.md#v98-continuation-contract-machine-checkable","merged_pr":"#320","merge_commit":"d11f6ddfadcb74cb50a6eb90c3e0dd11fe32590f","behavior_evidence_bundle_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_behavior_evidence_bundle.v1.json","behavior_evidence_bundle_mirror_schema_path":"spec/adeu_arc_behavior_evidence_bundle.schema.json","accepted_reference_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus98/adeu_arc_behavior_evidence_bundle_v98_reference.json"}
```

## Recommendation (Post v98)

- gate decision:
  - `V42G4_BEHAVIOR_EVIDENCE_BUNDLE_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v98 closes the bounded `V42-G4` behavior-mapping/evidence bundle seam on top of
    released `V42-G3` harness outputs, with support-bound cross-puzzle synthesis and
    fail-closed typed claim/authority posture on `main`.
  - no stop-gate schema-family or metric-key regressions were introduced; runtime
    observability changed only informationally.
  - with `V42-G1`..`V42-G4` now closed on `main`, the next default seam moves to
    post-`V42` family selection and is not selected by this decision note.
