# Draft Stop-Gate Decision (Post vNext+159)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS159.md`

Status: draft decision note (post-closeout capture, April 15, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS159.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v159_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+159` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS159.md`.
- This note captures bounded `V58-B` live restoration-state integration evidence only
  on `main`; it does not by itself authorize packet-law mutation, checkpoint-law
  mutation, ticket-law mutation, `local_write` widening, restoration-family widening,
  broader cleanup semantics, execute rollout, dispatch rollout, product/UI authority
  rollout, multi-agent widening, or hidden-cognition governance.
- Canonical `V58-B` shipment in `v159` is carried by reused
  `packages/adeu_agentic_de` and `packages/urm_runtime` package surfaces, thin
  `apps/api/scripts/run_agentic_de_live_harness_v58b.py` seam, authoritative and
  mirrored `agentic_de_*@1` schema export for the new restoration-state surfaces,
  deterministic `v58b` fixtures, and canonical
  `v58b_live_restoration_state_evidence@1` evidence input under
  `artifacts/agent_harness/v159/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- merged implementation PR:
  - `#386` (`Implement V58-B live restoration-state integration`)
- arc-completion merge commit:
  - `7e61cb36884877671747f4b212282df6d6948f1e`
- merged-at timestamp:
  - `2026-04-15T02:33:55+03:00`
- implementation commits integrated by the merge:
  - `054db3f5dadd166c26eeee8da05bc41baf70397f`
    (`Implement V58-B live restoration-state integration`)
  - `05a16a12c5a5e8a75ad620554de10ab267ed3f96`
    (`Fix V58-B default snapshot repo-root remap`)
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=159`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v159_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v159_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v159_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v159/evidence_inputs/metric_key_continuity_assertion_v159.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v159/evidence_inputs/runtime_observability_comparison_v159.json`
  - `V58-B` live restoration-state evidence input:
    `artifacts/agent_harness/v159/evidence_inputs/v58b_live_restoration_state_evidence_v159.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v159/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS159_EDGES.md`

## Exit-Criteria Check (vNext+159)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V58-B` merged on `main` | required | `pass` | PR `#386`, merge commit `7e61cb36884877671747f4b212282df6d6948f1e` |
| Existing package surfaces remained bounded to `adeu_agentic_de` + `urm_runtime` with one thin `v58b` script seam | required | `pass` | merged diff stayed in those package surfaces plus schema/fixture/test and one CLI runner |
| Existing URM copilot session path remained the only selected live harness path | required | `pass` | fixtures/tests and runner bind only URM copilot turn snapshot path |
| Exact live path remained `local_write/create_new` under the designated `V57` sandbox root and target | required | `pass` | lane fixtures/tests preserve `local_write` + `create_new` + designated sandbox root + target path |
| Outer harness capability remained necessary at most, never sufficient | required | `pass` | restoration-time lineage and entitlement checks keep `writes_allowed` / approval posture non-equivalent to ticket entitlement |
| Restoration remained a new live act, not ambient ongoing authority | required | `pass` | handoff/reintegration surfaces plus checker logic reject ambient authority posture |
| Original ticket stayed non-ambient authority and historical refs stayed lineage-only | required | `pass` | `action_ticket_ref` and prior reintegration refs are consumed as lineage inputs only |
| Restoration-time capability/approval posture was re-snapshotted and mismatch failed closed | required | `pass` | restoration-time continuation checks and regression tests enforce fail-closed behavior |
| Live restoration handoff remained explicit | required | `pass` | shipped `agentic_de_live_restoration_handoff_record@1` |
| Live restoration reintegration closed over current-turn restoration artifacts and declared witness basis | required | `pass` | shipped `agentic_de_live_restoration_reintegration_report@1` |
| Replay stayed bounded to the exact restoration event and proof stayed embedded in reintegration | required | `pass` | bounded replay-law proof summary and tests in `V58-B` runner/checker path |
| Transcript/event stream and prior fixtures stayed observability/drift-guard only | required | `pass` | runner/tests keep transcript/events non-witness and prior artifacts non-current-turn entitlement |
| No append-only restoration integration, broader write cleanup, hardening, execute, dispatch, or product/UI widening landed | required | `pass` | merged slice is restoration-state handoff/reintegration only over existing `V58-A`/`V57-B` path |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v159_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v159/evidence_inputs/metric_key_continuity_assertion_v159.json` records exact keyset equality versus `v158` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v159/evidence_inputs/runtime_observability_comparison_v159.json` records `103 ms` current elapsed, `103 ms` baseline elapsed, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v159_closeout_stop_gate_summary@1",
  "arc": "vNext+159",
  "target_path": "V58-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v158": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 103,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v158_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v159_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+158","current_arc":"vNext+159","baseline_source":"artifacts/stop_gate/report_v158_closeout.md","current_source":"artifacts/stop_gate/report_v159_closeout.md","baseline_elapsed_ms":103,"current_elapsed_ms":103,"delta_ms":0,"notes":"v159 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the bounded V58-B live restoration-state integration slice on main: one explicit live restoration handoff plus one explicit live restoration reintegration report were added over shipped V58-A live-turn lineage and shipped V57-B create_new compensating-restore lineage, with restoration treated as a new live act, ticket/prior-reintegration refs remaining historical lineage inputs only, restoration-time capability and approval posture re-snapshotted fail-closed, replay bounded to the exact restoration event, and no append-restore/broader-write/execute/dispatch/product/hidden-cognition widening."}
```

## V58B Live Restoration-State Evidence

```json
{"schema":"v58b_live_restoration_state_evidence@1","evidence_input_path":"artifacts/agent_harness/v159/evidence_inputs/v58b_live_restoration_state_evidence_v159.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS159.md#machine-checkable-contract","merged_pr":"#386","merge_commit":"7e61cb36884877671747f4b212282df6d6948f1e","implementation_commit":"054db3f5dadd166c26eeee8da05bc41baf70397f","review_hardening_commit":"05a16a12c5a5e8a75ad620554de10ab267ed3f96"}
```

## Recommendation (Post v159)

- gate decision:
  - `V58B_LIVE_RESTORATION_STATE_COMPLETE_ON_MAIN`
- rationale:
  - `v159` closes the bounded `V58-B` live restoration-state seam on `main`.
  - the shipped slice stayed properly bounded:
    - two existing repo-owned packages
    - one thin script seam
    - explicit lane-drift handoff enforcement
    - exact live restoration handoff/reintegration surfaces
    - same exact `local_write/create_new` path and designated sandbox root/target
    - restoration treated as a new live act
    - original ticket not ambient restoration authority
    - historical lineage refs preserved as lineage inputs only
    - restoration-time capability/approval resnapshot fail-closed
    - positive reintegration witness-basis posture preserved
    - replay bounded to the exact restoration event with embedded proof surface
    - transcript/event stream and prior artifacts remain non-native witness
    - no append-restore, broader cleanup, execute, dispatch, product, or
      hidden-cognition widening
  - stop-gate schema-family and metric-key continuity stayed intact.
  - runtime observability remained unchanged versus `v158`.
  - any next move should be new arc selection rather than widening `V58-B` in place.
