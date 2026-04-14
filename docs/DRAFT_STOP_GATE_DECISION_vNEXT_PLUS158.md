# Draft Stop-Gate Decision (Post vNext+158)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS158.md`

Status: draft decision note (post-closeout capture, April 15, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS158.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v158_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+158` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS158.md`.
- This note captures bounded `V58-A` live harness bind evidence only on `main`; it
  does not by itself authorize checkpoint-law mutation, ticket-law mutation,
  `local_write` widening, restoration-state integration, execute rollout, dispatch
  rollout, product/UI authority rollout, multi-agent widening, or hidden-cognition
  governance.
- Canonical `V58-A` shipment in `v158` is carried by the reused
  `packages/adeu_agentic_de` and `packages/urm_runtime` package surfaces, the thin
  `apps/api/scripts/run_agentic_de_live_harness_v58a.py` seam, authoritative and
  mirrored `agentic_de_*@1` schema export for the new live-turn surfaces,
  deterministic `v58a` fixtures, and the canonical
  `v58a_live_harness_bind_evidence@1` evidence input under
  `artifacts/agent_harness/v158/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- merged implementation PR:
  - `#385` (`Implement V58-A live harness bind starter`)
- arc-completion merge commit:
  - `5e1e97871de753a6e96d570f832bc1426701fb80`
- merged-at timestamp:
  - `2026-04-15T01:25:05+03:00`
- implementation commits integrated by the merge:
  - `f91040837171fdbb9cf5bd7994aab19ccbc63a70`
    (`Implement V58-A live harness bind starter`)
  - `5022d48fc25dd3fae635f23f08529b7436f3c617`
    (`Harden V58-A live turn fail-closed checks`)
- focused local verification actually run on the implementation branch and review
  hardening:
  - focused `ruff` on touched `V58-A` package/runtime/CLI/test files
  - focused `pytest` on `V58-A` package, runtime route, and CLI tests
- full local Python lane actually run before merge:
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=158`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v158_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v158_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v158_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v158/evidence_inputs/metric_key_continuity_assertion_v158.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v158/evidence_inputs/runtime_observability_comparison_v158.json`
  - `V58-A` live harness bind evidence input:
    `artifacts/agent_harness/v158/evidence_inputs/v58a_live_harness_bind_evidence_v158.json`
  - committed runtime event stream witness:
    `artifacts/agent_harness/v158/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS158_EDGES.md`

## Exit-Criteria Check (vNext+158)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V58-A` merged on `main` | required | `pass` | PR `#385`, merge commit `5e1e97871de753a6e96d570f832bc1426701fb80` |
| Existing package surfaces remained bounded to `adeu_agentic_de` + `urm_runtime` with one thin `v58a` script seam | required | `pass` | merged diff stayed in those package surfaces plus schema/fixture/test and one CLI runner |
| Existing URM copilot session path remained the only selected live harness path | required | `pass` | fixtures/tests and runner bind only URM copilot turn snapshot path |
| Exact live path remained `local_write/create_new` under the designated `V57` sandbox root | required | `pass` | lane fixtures and checker constraints preserve `local_write` + `create_new` + designated sandbox root |
| Outer harness capability remained necessary at most, never sufficient | required | `pass` | admission logic and tests keep `writes_allowed` / approval posture non-equivalent to ticket entitlement |
| Current-turn admission stayed explicit and typed | required | `pass` | shipped `agentic_de_live_turn_admission_record@1` with typed verdict/reason vocabulary |
| Ticket-to-effect handoff stayed explicit | required | `pass` | shipped `agentic_de_live_turn_handoff_record@1` with ticket lineage and target/scope fields |
| Reintegration closed over current-turn artifacts and declared witness basis | required | `pass` | shipped `agentic_de_live_turn_reintegration_report@1` with witness basis/certificate field and status/reason fields |
| Transcript/event stream and prior fixtures stayed observability/drift-guard only | required | `pass` | runner/tests keep transcript/events non-witness and prior artifacts non-current-turn entitlement |
| Root-origin dedup and origin/dependence tagging landed for handoff/reintegration support | required | `pass` | new live-turn surfaces include origin/dependence tags and root-origin dedup summary |
| No auto-restoration, broader write, execute, dispatch, product/UI, or hidden-bridge-state widening shipped | required | `pass` | merged slice is admission/handoff/reintegration only over existing `V56`/`V57` path |
| Review hardening stayed bounded and fail-closed | required | `pass` | `5022d48fc25dd3fae635f23f08529b7436f3c617` rejects explicit target with no visible turn and validates snapshot cwd against repo root directly |
| Focused tests plus full local Python gate passed | required | `pass` | focused `ruff`/`pytest` passed on branch; `make check` passed before merge |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v158_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v158/evidence_inputs/metric_key_continuity_assertion_v158.json` records exact keyset equality versus `v157` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v158/evidence_inputs/runtime_observability_comparison_v158.json` records `103 ms` current elapsed, `103 ms` baseline elapsed, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v158_closeout_stop_gate_summary@1",
  "arc": "vNext+158",
  "target_path": "V58-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v157": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 103,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v157_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v158_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+157","current_arc":"vNext+158","baseline_source":"artifacts/stop_gate/report_v157_closeout.md","current_source":"artifacts/stop_gate/report_v158_closeout.md","baseline_elapsed_ms":103,"current_elapsed_ms":103,"delta_ms":0,"notes":"v158 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the bounded V58-A live harness bind slice on main: one real URM copilot turn is bound through explicit current-turn admission, explicit ticket-to-effect handoff, and explicit reintegration reporting over the shipped V56-B local_write ticket and shipped V57-A create_new observed effect path, with outer harness capability remaining necessary at most and never sufficient, transcript/event stream remaining observability-only, and no restoration/execute/dispatch/product/hidden-bridge-state widening."}
```

## V58A Live Harness Bind Evidence

```json
{"schema":"v58a_live_harness_bind_evidence@1","evidence_input_path":"artifacts/agent_harness/v158/evidence_inputs/v58a_live_harness_bind_evidence_v158.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS158.md#machine-checkable-contract","merged_pr":"#385","merge_commit":"5e1e97871de753a6e96d570f832bc1426701fb80","implementation_commit":"f91040837171fdbb9cf5bd7994aab19ccbc63a70","review_hardening_commit":"5022d48fc25dd3fae635f23f08529b7436f3c617","implementation_packages":["adeu_agentic_de","urm_runtime"],"selected_record_shapes":["agentic_de_domain_packet@1","agentic_de_morph_ir@1","agentic_de_interaction_contract@1","agentic_de_action_proposal@1","agentic_de_membrane_checkpoint@1","agentic_de_morph_diagnostics@1","agentic_de_conformance_report@1","agentic_de_lane_drift_record@1","agentic_de_action_class_taxonomy@1","agentic_de_runtime_state@1","agentic_de_action_ticket@1","agentic_de_local_effect_observation_record@1","agentic_de_local_effect_conformance_report@1","agentic_de_live_turn_admission_record@1","agentic_de_live_turn_handoff_record@1","agentic_de_live_turn_reintegration_report@1"],"required_prior_lane_evidence_paths":["artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json","artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json","artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json","artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json","artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json","artifacts/agent_harness/v157/evidence_inputs/v57c_local_effect_hardening_evidence_v157.json"],"selected_live_session_surface_for_v58a":"urm_copilot_session_path_only","selected_live_action_class_for_v58a":"local_write","selected_local_write_kind_for_v58a":"create_new","designated_local_effect_sandbox_root":"artifacts/agentic_de/v57/local_effect/","selected_target_relative_path":"runtime/reference_patch_candidate.diff","outer_harness_capability_necessary_but_not_sufficient":true,"outer_writes_allowed_not_equivalent_to_v56_ticket":true,"approval_posture_not_ticket_equivalent":true,"transcript_and_event_stream_not_native_witness":true,"prior_fixtures_and_closeout_evidence_not_current_turn_witness":true,"admission_verdict_must_be_typed_not_boolean":true,"positive_reintegration_requires_witness_basis_or_certificate_ref":true,"handoff_and_reintegration_origin_tags_required":true,"root_origin_dedup_required_for_current_turn_support":true,"restoration_selected_in_v58a":false,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v158/evidence_inputs/metric_key_continuity_assertion_v158.json","runtime_observability_comparison_path":"artifacts/agent_harness/v158/evidence_inputs/runtime_observability_comparison_v158.json","runtime_event_stream_path":"artifacts/agent_harness/v158/runtime/evidence/local/urm_events.ndjson","notes":"v158 evidence pins the bounded V58-A live harness bind slice on main: shipped V56-B and V57-A surfaces are consumed by default, one real URM copilot turn is bound through explicit live-turn admission, explicit ticket-to-effect handoff, and explicit reintegration reporting, outer harness capability remains necessary at most and never sufficient, and review hardening added explicit fail-closed checks for unseen explicit target turns and mismatched snapshot cwd without widening class, restoration, execute, dispatch, product, or hidden-cognition authority."}
```

## Recommendation (Post v158)

- gate decision:
  - `V58A_LIVE_HARNESS_BIND_COMPLETE_ON_MAIN`
- rationale:
  - `v158` closes the bounded `V58-A` live harness bind seam on `main`.
  - the shipped slice stayed properly bounded:
    - two existing repo-owned packages
    - one thin script seam
    - explicit lane-drift handoff enforcement
    - exact live-turn admission/handoff/reintegration surfaces
    - exact `local_write/create_new` selected path
    - designated sandbox root preserved
    - outer harness capability non-equivalent to inner entitlement
    - typed admission verdict and reason codes
    - explicit reintegration witness basis posture
    - origin/dependence tags and root-origin dedup posture
    - transcript/event stream and prior artifacts remain non-native witness
    - no hidden bridge state
    - no auto-restoration
    - no broader write/execute/dispatch/product widening
    - no hidden-cognition governance claims
  - review hardening stayed bounded and materially improved fail-closed behavior:
    `5022d48fc25dd3fae635f23f08529b7436f3c617` tightened visible-turn and cwd
    admission checks without widening the slice.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained unchanged versus the `v157` baseline.
  - any next move should be new arc selection rather than `V58-A` widening in place.
