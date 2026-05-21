# Draft Stop-Gate Decision vNext+274

Status: post-closeout decision for `HOB-0-C` and `HOB-0`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS274.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+274` / `HOB-0-C` only, with
  family closeout for the selected `HOB-0` arc.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS274.md`.
- It does not authorize semantic adjudication by the broker, closure
  recomputation outside released B records, ontology generation, catalog
  mutation by the broker, probe execution, command execution outside the
  implementation/test lane, worker dispatch, product behavior claims,
  ProgramBench integration, clean product truth claims, score-to-closure
  laundering, future-family selection, release authority, or recursive policy
  amendment.

## Evidence Source

- merged implementation PR:
  - `#502` (`Implement HOB-0-C broker closeout surfaces`)
- arc-completion merge commit:
  - `2d08def1a9b65b4973f08af2ff98afb29c1ed67d`
- merged-at timestamp:
  - `2026-05-21T15:05:55Z`
- implementation commits integrated by the merge:
  - `cf682f2b36e7e2789840aaced200d9a4c072ce68`
    (`Implement HOB-0-C broker closeout surfaces`)
  - `5561913b53e42c46e851f9a086cc0331b60d1042`
    (`Tighten HOB-0-C state validation`)
- implementation verification recorded before merge:
  - focused `HOB-0-C` pytest
  - full obligation-broker pytest
  - `make lint`
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=274`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v274_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v274_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v274_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v274/evidence_inputs/metric_key_continuity_assertion_v274.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v274/evidence_inputs/runtime_observability_comparison_v274.json`
  - `HOB-0-C` closeout evidence input:
    `artifacts/agent_harness/v274/evidence_inputs/hob_0c_closeout_evidence_v274.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v274/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS274_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `HOB-0-C` merged on `main` | required | `pass` | PR `#502`, merge commit `2d08def1a9b65b4973f08af2ff98afb29c1ed67d` |
| Implementation stayed in the obligation-broker lane | required | `pass` | merged implementation package is `adeu_obligation_broker` |
| Selected C surfaces shipped | required | `pass` | delta attribution ledger, stale-ledger invalidation report, integration handoff, and family closeout alignment schemas/models shipped |
| C consumes released A/B substrate | required | `pass` | C builders validate catalog identity and consume released B closure evidence rather than reopening A/B decisions |
| Delta attribution is pressure-only | required | `pass` | `delta_authority_posture = pressure_attribution_only_not_product_truth` |
| Per-row evidence boundary posture is required | required | `pass` | attribution and handoff rows require explicit evidence-boundary posture |
| Score movement cannot become macro closure without closure evidence | required | `pass` | macro closure attribution requires released closure evidence and local locked-probe boundary |
| Unknown node IDs are rejected | required | `pass` | delta attribution and handoff builders reject unknown catalog nodes |
| Stale catalog hash invalidates prior ledgers/probe plans | required | `pass` | catalog hash changes require invalidated refs and reason rows |
| Current catalog hash cannot invalidate current refs | required | `pass` | review hardening rejects invalidation refs when prior/current catalog hashes match |
| Integration handoff remains pressure-only and non-selecting | required | `pass` | no ProgramBench, semantic compiler, probe execution, implementation, or future-family authority posture can be granted |
| Handoff pressure kinds are internally consistent | required | `pass` | review hardening rejects mixed pressure kinds within a handoff |
| Family closeout accounts for exact A/B/C slices | required | `pass` | closeout alignment requires exact `HOB-0-A`, `HOB-0-B`, and `HOB-0-C` slice refs |
| Family closeout cannot hide blockers or deferred refs | required | `pass` | closed family rejects residual deferred refs/blockers; open-with-deferred rejects active blockers |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v274_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v274/evidence_inputs/metric_key_continuity_assertion_v274.json` records exact keyset equality versus `v273` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v274/evidence_inputs/runtime_observability_comparison_v274.json` records `121 ms` baseline, `78 ms` current, `-43 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v274_closeout_stop_gate_summary@1",
  "arc": "vNext+274",
  "target_path": "HOB-0-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v273": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 78,
  "runtime_observability_delta_ms": -43
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v273_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v274_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+273","baseline_elapsed_ms":121,"baseline_source":"artifacts/stop_gate/report_v273_closeout.md","current_arc":"vNext+274","current_elapsed_ms":78,"current_source":"artifacts/stop_gate/report_v274_closeout.md","delta_ms":-43,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+274","catalog_hash_continuity_required":true,"clean_product_truth_authority_granted":false,"closed_slice":"HOB-0-C","delta_attribution_authority_posture":"pressure_attribution_only_not_product_truth","evidence_boundary_posture_required_per_row":true,"family":"HOB-0","family_closeout_alignment_granted":true,"family_closeout_exact_slices_required":true,"future_family_selection_granted":false,"handoff_pressure_only_non_selecting":true,"implementation_authority_granted":false,"implementation_commits":["cf682f2b36e7e2789840aaced200d9a4c072ce68","5561913b53e42c46e851f9a086cc0331b60d1042"],"implementation_package":"packages/adeu_obligation_broker","merged_at":"2026-05-21T15:05:55Z","merge_commit":"2d08def1a9b65b4973f08af2ff98afb29c1ed67d","mixed_handoff_pressure_kind_rejected":true,"open_with_deferred_blockers_rejected":true,"product_truth_authority_granted":false,"pull_request":"https://github.com/LexLattice/adeu-studio/pull/502","reference_schema_root":"packages/adeu_obligation_broker/schema","released_a_refs_required":true,"released_b_refs_required":true,"runtime_event_stream_path":"artifacts/agent_harness/v274/runtime/evidence/local/urm_events.ndjson","runtime_observability_comparison_path":"artifacts/agent_harness/v274/evidence_inputs/runtime_observability_comparison_v274.json","schema":"hob_0c_closeout_evidence@1","score_to_closure_laundering_rejected":true,"selected_record_shapes":["repo_obligation_delta_attribution_ledger@1","repo_obligation_stale_ledger_invalidation_report@1","repo_obligation_broker_integration_handoff@1","repo_obligation_broker_family_closeout_alignment@1"],"semantic_judgment_authority_granted":false,"stale_catalog_hash_invalidation_required":true,"test_reference_path":"packages/adeu_obligation_broker/tests/test_hob_0c.py","unchanged_catalog_invalidation_rejected":true,"verification_commands":[".venv/bin/python -m pytest packages/adeu_obligation_broker/tests/test_hob_0c.py -q",".venv/bin/python -m pytest packages/adeu_obligation_broker/tests -q","make lint","make check","make arc-closeout-check ARC=274"],"worker_dispatch_authority_granted":false}
```

## Recommendation

- gate decision:
  - `HOB_0C_DELTA_ATTRIBUTION_AND_FAMILY_CLOSEOUT_COMPLETE_ON_MAIN`
- rationale:
  - `v274` closes the bounded `HOB-0-C` delta attribution, stale-ledger
    invalidation, integration handoff, and family closeout alignment seam on
    `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_obligation_broker`) only
    - four deterministic HOB-0-C record surfaces
    - released `HOB-0-A` and `HOB-0-B` substrate required before C attribution
    - delta attribution remains pressure-only and evidence-boundary typed
    - stale-ledger invalidation is hash-bound and rejects contradictory current
      catalog invalidation
    - integration handoffs are pressure-only, internally consistent, and
      non-selecting
    - family closeout accounts for exact A/B/C slices and rejects hidden
      blockers or deferred refs
    - no semantic adjudication, closure recomputation outside B, probe
      execution, worker dispatch, implementation authority, product truth,
      ProgramBench integration, score-to-closure laundering, or future-family
      selection shipped
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- family status:
  - `HOB-0` is closed.
