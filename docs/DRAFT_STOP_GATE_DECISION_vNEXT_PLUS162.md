# Draft Stop-Gate Decision (Post vNext+162)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS162.md`

Status: draft decision note (post-closeout capture, April 15, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS162.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v162_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+162` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS162.md`.
- This note captures bounded `V59-B` continuity-safe restoration evidence only on
  `main`; it does not by itself authorize checkpoint-law mutation, ticket-law
  mutation, broader `local_write` semantics, broader continuity-root law,
  append-only/overwrite/destructive continuity restoration, replay/resume widening,
  continuity hardening/migration, execute widening, dispatch widening, product/UI
  authority rollout, or hidden-cognition governance.
- Canonical `V59-B` shipment in `v162` is carried by reused
  `packages/adeu_agentic_de` and `packages/urm_runtime` package surfaces, thin
  `apps/api/scripts/run_agentic_de_workspace_continuity_v59b.py` seam, authoritative
  and mirrored continuity-restoration schema export, deterministic `v59b` fixtures,
  and canonical
  `v59b_workspace_continuity_restoration_evidence@1` evidence input under
  `artifacts/agent_harness/v162/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- merged implementation PR:
  - `#389` (`Implement V59-B continuity-safe restoration`)
- arc-completion merge commit:
  - `d7fe8f1c8a6959f81a3da948cfab21d3d5f30a18`
- merged-at timestamp:
  - `2026-04-15T07:59:11+03:00`
- implementation commits integrated by the merge:
  - `1016e08dd4987365035b952e564df96a70a6cec4`
    (`Implement V59-B continuity-safe restoration`)
  - `bb6268abad9d57c0c7700ed1263352504d37906e`
    (`Fix V59-B review follow-ups`)
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=162`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v162_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v162_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v162_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v162/evidence_inputs/metric_key_continuity_assertion_v162.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v162/evidence_inputs/runtime_observability_comparison_v162.json`
  - `V59-B` continuity-safe restoration evidence input:
    `artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v162/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS162_EDGES.md`

## Exit-Criteria Check (vNext+162)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V59-B` merged on `main` | required | `pass` | PR `#389`, merge commit `d7fe8f1c8a6959f81a3da948cfab21d3d5f30a18` |
| Existing package surfaces remained bounded to `adeu_agentic_de` + `urm_runtime` with one thin `v59b` script seam | required | `pass` | merged diff stayed in those package surfaces plus schema/fixture/test and one CLI runner |
| Existing URM copilot session path remained the only selected live harness path | required | `pass` | fixtures/tests and runner bind only URM copilot turn snapshot path |
| Declared continuity root remained the only selected persistent region | required | `pass` | `artifacts/agentic_de/v59/workspace_continuity/` remains the selected root in runner, fixtures, and tests |
| Exact live path remained `local_write/create_new` centered on `runtime/reference_patch_candidate.diff` | required | `pass` | lane fixtures/tests and runner preserve `local_write` + `create_new` + exact target path |
| Continuity-safe restoration remained a new live act, not standing continuity authority | required | `pass` | checker/runner enforce restoration authority as current-turn lineage-bound entitlement |
| Restoration-time capability / approval posture resnapshot remained required and mismatch failed closed | required | `pass` | `v59b` handoff semantics and tests require restoration-time resnapshot and fail-closed mismatch posture |
| Restoration-time continuation verdict remained typed, witness-bearing, and replayable | required | `pass` | shipped continuity restoration handoff/reintegration fixtures and tests assert typed continuation verdict semantics |
| Historical lineage refs stayed lineage-only and did not mint restoration entitlement by reference alone | required | `pass` | checker semantics keep lineage refs in derivation-only role; current-turn witness is still required |
| Prior governed-state baseline summary plus baseline-match verdict remained first-class | required | `pass` | `v59b` handoff schema and fixtures include explicit baseline summary and baseline-match verdict |
| Restoration-time target/region state summary plus bounded compensating-scope match remained first-class | required | `pass` | `v59b` handoff schema and fixtures include explicit restoration-time state summary and compensating-scope match |
| Positive continuity restoration reintegration required explicit witness basis or certificate ref | required | `pass` | `v59b` reintegration schema and fixtures require witness-basis/certificate support for positive reintegration |
| Replay remained bounded to recomputation/re-evaluation of the exact continuity-safe restoration event only | required | `pass` | `v59b` reintegration semantics keep replay-law proof narrow and lineage-bound |
| No append-only/overwrite/destructive cleanup widening, replay/resume widening, execute widening, dispatch widening, or product/UI widening landed | required | `pass` | merged slice is continuity-safe restoration handoff/reintegration only |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v162_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v162/evidence_inputs/metric_key_continuity_assertion_v162.json` records exact keyset equality versus `v161` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v162/evidence_inputs/runtime_observability_comparison_v162.json` records `90 ms` current elapsed, `77 ms` baseline elapsed, `+13 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v162_closeout_stop_gate_summary@1",
  "arc": "vNext+162",
  "target_path": "V59-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v161": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 90,
  "runtime_observability_delta_ms": 13
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v161_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v162_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+161","current_arc":"vNext+162","baseline_source":"artifacts/stop_gate/report_v161_closeout.md","current_source":"artifacts/stop_gate/report_v162_closeout.md","baseline_elapsed_ms":77,"current_elapsed_ms":90,"delta_ms":13,"notes":"v162 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the bounded V59-B continuity-safe restoration starter on main: one continuity restoration handoff record and one continuity restoration reintegration report over the shipped V59-A continuity region/admission/occupancy lineage and V57-B/V58-B restoration baseline, with restoration treated as a new live act, restoration-time resnapshot required, and no append-only/destructive/replay-widening/execute/dispatch/product/hidden-cognition widening."}
```

## V59B Workspace Continuity Restoration Evidence

```json
{"schema":"v59b_workspace_continuity_restoration_evidence@1","evidence_input_path":"artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS162.md#machine-checkable-contract","merged_pr":"#389","merge_commit":"d7fe8f1c8a6959f81a3da948cfab21d3d5f30a18","implementation_commit":"1016e08dd4987365035b952e564df96a70a6cec4","review_hardening_commit":"bb6268abad9d57c0c7700ed1263352504d37906e"}
```

## Recommendation (Post v162)

- gate decision:
  - `V59B_CONTINUITY_SAFE_RESTORATION_STARTER_COMPLETE_ON_MAIN`
- rationale:
  - `v162` closes the bounded `V59-B` continuity-safe restoration seam on `main`.
  - the shipped slice stayed properly bounded:
    - same URM live session path
    - same continuity root
    - same `local_write/create_new` target
    - restoration remains a new live act
    - restoration-time resnapshot and typed continuation verdict
    - baseline-match and compensating-scope-match required
    - witness-bearing continuity restoration reintegration
    - no append-only/destructive/restoration-family widening
    - no replay/resume widening, execute widening, dispatch widening, product
      widening, or hidden-cognition governance
  - stop-gate schema-family and metric-key continuity stayed intact.
  - runtime observability remains within bounded closeout posture.
  - any next move should be a new arc selection rather than widening `V59-B` in
    place.
