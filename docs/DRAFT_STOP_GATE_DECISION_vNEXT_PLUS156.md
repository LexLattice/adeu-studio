# Draft Stop-Gate Decision (Post vNext+156)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS156.md`

Status: draft decision note (post-closeout capture, April 14, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS156.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v156_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+156` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS156.md`.
- This note captures bounded `V57-B` restoration/replay evidence only on `main`; it
  does not by itself authorize any `local_write` widening, append-only restoration,
  broader destructive write authority, checkpoint/ticket-law mutation, hardening
  rollout, stronger execute rollout, delegated/external dispatch rollout, repo-source
  write authority, product/API rollout, multi-agent runtime widening, or
  hidden-cognition governance.
- Canonical `V57-B` shipment in `v156` is carried by the reused
  `packages/adeu_agentic_de` package surface, the thin
  `apps/api/scripts/restore_agentic_de_local_effect_v57b.py` seam, authoritative and
  mirrored `agentic_de_*@1` schema export for the new restoration surface,
  deterministic `v57b` fixtures, and the canonical
  `v57b_local_effect_restoration_evidence@1` evidence input under
  `artifacts/agent_harness/v156/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- merged implementation PR:
  - `#383` (`Implement V57-B local effect restoration`)
- arc-completion merge commit:
  - `5845f963e55cf199cedc2cbdf733482743b543b6`
- merged-at timestamp:
  - `2026-04-14T17:15:09+03:00`
- implementation commits integrated by the merge:
  - `5ae575a8b772047c9a21322e51ec22cfe4bae7c9`
    (`Implement V57-B local effect restoration slice`)
  - `a46804d2a59770f3de5adca242704bd9f90b271e`
    (`Harden V57-B restoration lineage checks`)
- focused local verification actually run on the implementation branch and review
  hardening:
  - focused `ruff` on touched `V57-B` package/helper/CLI files
  - focused `pytest` on `V57-B` package + CLI tests
- full local Python lane actually run before merge:
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=156`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v156_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v156_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v156_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v156/evidence_inputs/metric_key_continuity_assertion_v156.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v156/evidence_inputs/runtime_observability_comparison_v156.json`
  - `V57-B` restoration evidence input:
    `artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json`
  - committed runtime event stream witness:
    `artifacts/agent_harness/v156/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS156_EDGES.md`

## Exit-Criteria Check (vNext+156)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V57-B` merged on `main` | required | `pass` | PR `#383`, merge commit `5845f963e55cf199cedc2cbdf733482743b543b6` |
| Existing `adeu_agentic_de` package remained the only live implementation package for the slice | required | `pass` | merged diff stayed inside `packages/adeu_agentic_de` plus thin `v57b` script/test/schema/fixture surfaces |
| Shipped `V56-A`, `V56-B`, `V56-C`, and `V57-A` surfaces were consumed unchanged by default | required | `pass` | `run_agentic_de_local_effect_v57b` reuses shipped packet/checkpoint/ticket/harvest/observation surfaces and validates explicit `V57-B` lane drift before restoration emission |
| Explicit lane handoff remained mandatory before `V57-B` restoration | required | `pass` | committed `agentic_de_lane_drift_record@1` fixture plus checker enforcement reject missing or malformed handoff posture |
| Exact restoration surface landed | required | `pass` | committed `agentic_de_local_effect_restoration_record@1` authoritative + mirror schema and deterministic fixture |
| Replay remained narrowly bounded to recomputation/re-evaluation over prior observed lineage only | required | `pass` | shipped runner and model enforce bounded replay semantics and reject generalized replay posture |
| `local_write` operative interpretation remained frozen and restoration exemplar stayed create-new only | required | `pass` | checker/fixtures keep `compensating_restore_of_v57a_create_new_artifact_only`; append-only and broader destructive write kinds remain out of scope |
| One designated sandbox root plus anti-escape law remained enforced | required | `pass` | local-effect restoration path remains under `artifacts/agentic_de/v57/local_effect/` and tests preserve fail-closed anti-escape checks |
| Restoration entitlement remained lineage-bound and non-ambient | required | `pass` | restoration requires prior `bounded_effect_observed`, prior conformance/observation refs, and bounded compensating-scope match; original ticket is not ambient ongoing authority |
| Negative restoration outcomes remained explicit rather than silently normalized | required | `pass` | shipped vocabulary preserves `restoration_mismatched_effect_observed`, `restoration_out_of_scope_write_observed`, and `restoration_boundedness_verdict_failed` |
| Restoration outputs remained evidence-bearing only and did not mutate live behavior by default | required | `pass` | fixture sets `evidence_only = true` and `changes_live_behavior_by_default = false` |
| No hardening, stronger execute, delegated/external dispatch, repo-source authority, product, multi-agent, or hidden-cognition widening shipped | required | `pass` | merged `V57-B` adds one bounded restoration record only and introduces no widened live class or hidden-thought proxy inputs |
| Review hardening tightened lineage checks without widening the slice | required | `pass` | `a46804d2a59770f3de5adca242704bd9f90b271e` strengthened required handoff posture validation and conformance/ticket lineage checks |
| Focused tests plus full local Python gate passed | required | `pass` | focused `ruff`/`pytest` passed on the branch; `make check` passed before merge |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v156_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v156/evidence_inputs/metric_key_continuity_assertion_v156.json` records exact keyset equality versus `v155` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v156/evidence_inputs/runtime_observability_comparison_v156.json` records `103 ms` current elapsed, `73 ms` baseline elapsed, `+30 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v156_closeout_stop_gate_summary@1",
  "arc": "vNext+156",
  "target_path": "V57-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v155": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 103,
  "runtime_observability_delta_ms": 30
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v155_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v156_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+155","current_arc":"vNext+156","baseline_source":"artifacts/stop_gate/report_v155_closeout.md","current_source":"artifacts/stop_gate/report_v156_closeout.md","baseline_elapsed_ms":73,"current_elapsed_ms":103,"delta_ms":30,"notes":"v156 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the bounded V57-B local-effect restoration/replay slice on main: shipped V56 and V57-A packet/checkpoint/ticket/harvest/observation surfaces are consumed by default, one lineage-bound evidence-only restoration record is added over the designated sandbox root, replay remains bounded recomputation/re-evaluation over prior observed-effect lineage only, and review hardening tightened ticket/conformance lineage validation without widening class, repo, dispatch, product, or hidden-cognition authority."}
```

## V57B Local Effect Restoration Evidence

```json
{"schema":"v57b_local_effect_restoration_evidence@1","evidence_input_path":"artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS156.md#machine-checkable-contract","merged_pr":"#383","merge_commit":"5845f963e55cf199cedc2cbdf733482743b543b6","implementation_commit":"5ae575a8b772047c9a21322e51ec22cfe4bae7c9","review_hardening_commit":"a46804d2a59770f3de5adca242704bd9f90b271e","implementation_packages":["adeu_agentic_de"],"selected_record_shapes":["agentic_de_domain_packet@1","agentic_de_morph_ir@1","agentic_de_interaction_contract@1","agentic_de_action_proposal@1","agentic_de_membrane_checkpoint@1","agentic_de_morph_diagnostics@1","agentic_de_conformance_report@1","agentic_de_lane_drift_record@1","agentic_de_action_class_taxonomy@1","agentic_de_runtime_state@1","agentic_de_action_ticket@1","agentic_de_runtime_harvest_record@1","agentic_de_governance_calibration_register@1","agentic_de_migration_decision_register@1","agentic_de_local_effect_observation_record@1","agentic_de_local_effect_conformance_report@1","agentic_de_local_effect_restoration_record@1"],"required_prior_lane_evidence_paths":["artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json","artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json","artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json","artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json"],"selected_live_action_class_for_v57b":"local_write","selected_restoration_exemplar_for_v57b":"compensating_restore_of_v57a_create_new_artifact_only","append_only_restoration_selected_for_v57b":false,"restoration_outputs_change_live_behavior_by_default":false,"hardening_register_selected_for_v57b":false,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v156/evidence_inputs/metric_key_continuity_assertion_v156.json","runtime_observability_comparison_path":"artifacts/agent_harness/v156/evidence_inputs/runtime_observability_comparison_v156.json","runtime_event_stream_path":"artifacts/agent_harness/v156/runtime/evidence/local/urm_events.ndjson","notes":"v156 evidence pins the bounded V57-B local-effect restoration/replay slice on main: shipped V56 and V57-A surfaces are consumed by default, one lineage-bound evidence-only restoration record is added over the designated sandbox root, replay remains bounded recomputation/re-evaluation over prior observed-effect lineage only, and review hardening tightened ticket/conformance lineage validation without widening class, repo, dispatch, product, or hidden-cognition authority."}
```

## Recommendation (Post v156)

- gate decision:
  - `V57B_LOCAL_EFFECT_RESTORATION_COMPLETE_ON_MAIN`
- rationale:
  - `v156` closes the bounded `V57-B` restoration/replay seam on `main`.
  - the shipped slice stayed properly bounded:
    - one existing repo-owned package
    - one existing thin script seam
    - explicit lane-drift handoff enforcement
    - exact restoration record surface
    - narrow replay semantics only
    - one designated sandbox root only
    - one create-new restoration exemplar only
    - explicit lineage-bound entitlement checks
    - explicit negative restoration outcomes
    - evidence-bearing restoration only
    - no checkpoint or ticket mutation by default
    - no hardening rollout
    - no stronger execute rollout
    - no delegated/external dispatch rollout
    - no repo-source write authority
    - no product or multi-agent widening
    - no hidden-cognition governance claims
  - review hardening stayed bounded and materially improved correctness:
    `a46804d2a59770f3de5adca242704bd9f90b271e` tightened required handoff and
    lineage validation without widening the slice past the lock.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability increased by `30 ms` versus the `v155` baseline.
