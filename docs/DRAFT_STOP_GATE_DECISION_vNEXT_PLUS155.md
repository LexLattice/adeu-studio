# Draft Stop-Gate Decision (Post vNext+155)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS155.md`

Status: draft decision note (post-closeout capture, April 14, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS155.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v155_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+155` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS155.md`.
- This note captures bounded `V57-A` local-effect observation evidence only on
  `main`; it does not by itself authorize any ticket-law widening, broader
  `local_write` reinterpretation, restoration rollout, hardening-register rollout,
  stronger execute rollout, delegated or external dispatch rollout, repo-source
  write authority, product/API rollout, multi-agent runtime widening, or
  hidden-cognition governance.
- Canonical `V57-A` shipment in `v155` is carried by the reused
  `packages/adeu_agentic_de` package surface, the thin
  `apps/api/scripts/observe_agentic_de_local_effect_v57a.py` seam, authoritative and
  mirrored `agentic_de_*@1` schema export for the new observation surfaces,
  deterministic `v57a` fixtures, and the canonical
  `v57a_local_effect_observation_evidence@1` evidence input under
  `artifacts/agent_harness/v155/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- merged implementation PR:
  - `#382` (`Implement V57-A local effect observation`)
- arc-completion merge commit:
  - `30b38ff933f669c1289fb1de1f32774ee18707e2`
- merged-at timestamp:
  - `2026-04-14T12:06:37+03:00`
- implementation commits integrated by the merge:
  - `ab2af6be133616f2648022ef9ec0056c5c2e6010`
    (`Implement V57-A local effect observation`)
  - `844e2b378476f27cf5f4b219103fe01490086305`
    (`Harden V57-A local effect observation`)
- focused local verification actually run on the implementation branch and review
  hardening:
  - focused `ruff` on the touched `V57-A` package, helper, and CLI files
  - focused `pytest` on the `V57-A` package + CLI tests
- full local Python lane actually run before merge:
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=155`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v155_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v155_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v155_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v155/evidence_inputs/metric_key_continuity_assertion_v155.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v155/evidence_inputs/runtime_observability_comparison_v155.json`
  - `V57-A` local-effect observation evidence input:
    `artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json`
  - committed runtime event stream witness:
    `artifacts/agent_harness/v155/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS155_EDGES.md`

## Exit-Criteria Check (vNext+155)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V57-A` merged on `main` | required | `pass` | PR `#382`, merge commit `30b38ff933f669c1289fb1de1f32774ee18707e2` |
| Existing `adeu_agentic_de` package remained the only live implementation package for the slice | required | `pass` | merged diff stayed inside `packages/adeu_agentic_de` plus the thin `v57a` script/test/schema/fixture surfaces |
| Shipped `V56-A`, `V56-B`, and `V56-C` surfaces were consumed unchanged by default | required | `pass` | `run_agentic_de_local_effect_v57a` reuses the shipped packet / checkpoint / ticket / harvest family surfaces and validates explicit `V57-A` lane drift before observation emission |
| Explicit lane handoff remained mandatory before `V57-A` observation | required | `pass` | committed `agentic_de_lane_drift_record@1` fixture plus checker enforcement reject missing or malformed handoff posture |
| Exact local-effect observation and conformance surfaces landed | required | `pass` | committed `agentic_de_local_effect_observation_record@1` and `agentic_de_local_effect_conformance_report@1` schema families and fixtures |
| Actual effect stayed narrowed to the first safe `local_write` subset only | required | `pass` | shipped observation fixture records `selected_local_write_kind = create_new`; destructive, overwrite, rename, delete, and metadata-mutating writes stay fail-closed |
| One designated sandbox root plus anti-escape law remained enforced | required | `pass` | `local_effect.py` resolves only `artifacts/agentic_de/v57/local_effect/`, rejects symlink-component escape, parent traversal, and repo-root escape, and keeps observed writes inside the designated sandbox |
| Every observed write stayed attributable to one lawful ticket / proposal / checkpoint scope | required | `pass` | shipped observation/conformance fixtures keep explicit `ticket_ref`, `action_proposal_ref`, and `checkpoint_ref`, and checker validation rejects unbound or mismatched effect scope |
| Negative observation outcomes remained explicit rather than silently normalized | required | `pass` | shipped model and tests preserve explicit outcomes for bounded effect observed, no effect observed, out-of-scope write observed, mismatched effect observed, and boundedness verdict failed |
| Observation outputs remained evidence-bearing only and did not mutate live behavior by default | required | `pass` | shipped observation and conformance fixtures set `evidence_only = true` and `changes_live_behavior_by_default = false` |
| No restoration, hardening register, stronger execute, delegated/external dispatch, repo-source authority, product, multi-agent, or hidden-cognition widening shipped | required | `pass` | merged `V57-A` adds bounded sandbox observation only and introduces no restoration, no new live class, no repo-source write surface, and no hidden-thought proxy inputs |
| Review hardening tightened sandbox/file-handling correctness without widening the slice | required | `pass` | `844e2b378476f27cf5f4b219103fe01490086305` added bounded streaming hash/text guards, stronger symlink-component validation, zero-byte `create_new` observation, and exact expected-write-set divergence checks |
| Focused tests plus full local Python gate passed | required | `pass` | focused `ruff` and `pytest` passed on the branch and in review hardening; `make check` passed before merge |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v155_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v155/evidence_inputs/metric_key_continuity_assertion_v155.json` records exact keyset equality versus `v154` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v155/evidence_inputs/runtime_observability_comparison_v155.json` records `73 ms` current elapsed, `73 ms` baseline elapsed, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v155_closeout_stop_gate_summary@1",
  "arc": "vNext+155",
  "target_path": "V57-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v154": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 73,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v154_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v155_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+154","current_arc":"vNext+155","baseline_source":"artifacts/stop_gate/report_v154_closeout.md","current_source":"artifacts/stop_gate/report_v155_closeout.md","baseline_elapsed_ms":73,"current_elapsed_ms":73,"delta_ms":0,"notes":"v155 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the bounded V57-A local-effect observation slice on main: shipped V56 packet, checkpoint, ticket, and harvest surfaces are consumed by default, one designated sandbox-root observation and one bounded conformance surface are added, actual effect remains narrowed to the first safe local_write subset, observation outputs remain evidence-bearing only, and review hardening tightened sandbox/file-handling correctness without widening the slice."}
```

## V57A Local Effect Observation Evidence

```json
{"schema":"v57a_local_effect_observation_evidence@1","evidence_input_path":"artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS155.md#machine-checkable-contract","merged_pr":"#382","merge_commit":"30b38ff933f669c1289fb1de1f32774ee18707e2","implementation_commit":"ab2af6be133616f2648022ef9ec0056c5c2e6010","review_hardening_commit":"844e2b378476f27cf5f4b219103fe01490086305","implementation_packages":["adeu_agentic_de"],"selected_record_shapes":["agentic_de_domain_packet@1","agentic_de_morph_ir@1","agentic_de_interaction_contract@1","agentic_de_action_proposal@1","agentic_de_membrane_checkpoint@1","agentic_de_morph_diagnostics@1","agentic_de_conformance_report@1","agentic_de_lane_drift_record@1","agentic_de_action_class_taxonomy@1","agentic_de_runtime_state@1","agentic_de_action_ticket@1","agentic_de_runtime_harvest_record@1","agentic_de_governance_calibration_register@1","agentic_de_migration_decision_register@1","agentic_de_local_effect_observation_record@1","agentic_de_local_effect_conformance_report@1"],"required_prior_lane_evidence_paths":["artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json","artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json","artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json"],"selected_live_action_class_for_v57a":"local_write","selected_local_write_first_subset_for_v57a":["create_new","append_only"],"designated_local_effect_sandbox_root":"artifacts/agentic_de/v57/local_effect/","effect_outputs_evidence_only":true,"restoration_selected_for_v57a":false,"hardening_register_selected_for_v57a":false,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v155/evidence_inputs/metric_key_continuity_assertion_v155.json","runtime_observability_comparison_path":"artifacts/agent_harness/v155/evidence_inputs/runtime_observability_comparison_v155.json","runtime_event_stream_path":"artifacts/agent_harness/v155/runtime/evidence/local/urm_events.ndjson","notes":"v155 evidence pins the bounded V57-A local-effect observation slice on main: shipped V56 packet, checkpoint, ticket, and harvest surfaces are consumed by default, one designated sandbox-root local-effect observation record plus one bounded conformance report are added, actual effect remains narrowed to the first safe local_write subset only, observation outputs remain evidence-bearing only, and review hardening tightened sandbox/file-handling correctness without widening the slice."}
```

## Recommendation (Post v155)

- gate decision:
  - `V57A_LOCAL_EFFECT_OBSERVATION_COMPLETE_ON_MAIN`
- rationale:
  - `v155` closes the bounded `V57-A` local-effect observation seam on `main`.
  - the shipped slice stayed properly bounded:
    - one existing repo-owned package
    - one existing thin script seam
    - explicit lane-drift handoff enforcement
    - exact local-effect observation and conformance surfaces
    - one designated sandbox root only
    - one first safe `local_write` subset only
    - explicit ticket/proposal/checkpoint lineage binding
    - explicit negative observation outcomes
    - evidence-bearing observation only
    - no checkpoint or ticket mutation by default
    - no restoration or hardening rollout
    - no stronger execute rollout
    - no delegated or external dispatch rollout
    - no repo-source write authority
    - no product or multi-agent widening
    - no hidden-cognition governance claims
  - review hardening stayed bounded and materially improved correctness:
    `844e2b378476f27cf5f4b219103fe01490086305` tightened bounded
    streaming hash/text handling, symlink-component sandbox validation,
    zero-byte `create_new` observation handling, and exact expected-write-set
    divergence detection without widening the slice past the lock.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability was unchanged versus the `v154` baseline.
