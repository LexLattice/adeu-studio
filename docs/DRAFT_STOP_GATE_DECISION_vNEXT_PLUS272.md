# Draft Stop-Gate Decision vNext+272

Status: post-closeout decision for `HOB-0-A`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS272.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+272` / `HOB-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS272.md`.
- It does not authorize closure aggregation, probe-matrix planning,
  implementation batch planning, delta attribution, stale-ledger invalidation,
  integration handoff, semantic adjudication by the broker, ontology generation,
  catalog mutation by the broker, probe execution, command execution outside the
  implementation/test lane, worker dispatch, code patch authority, product
  authority, semantic compiler integration, ProgramBench integration,
  future-family selection, release authority, or recursive policy amendment.

## Evidence Source

- merged implementation PR:
  - `#500` (`Implement HOB-0-A obligation broker`)
- merge commit:
  - `16d27c4e3458956ce96c1acaa72930ec6ecc2722`
- merged-at timestamp:
  - `2026-05-21T10:59:26Z`
- implementation commits integrated by the merge:
  - `724f69f1110540d86d6e244d912625dd02f27039`
    (`Implement HOB-0-A obligation broker`)
  - `142ea0de8dee8d3320e010eb70c53127f0c7bfb4`
    (`Address HOB-0-A review and web audit`)
- implementation verification recorded before merge:
  - focused `HOB-0-A` pytest
  - obligation-broker schema export pytest
  - `make lint`
  - web lint/build/audit checks after dependency hardening
  - GitHub CI
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=272`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v272_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v272_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v272_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v272/evidence_inputs/metric_key_continuity_assertion_v272.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v272/evidence_inputs/runtime_observability_comparison_v272.json`
  - `HOB-0-A` closeout evidence input:
    `artifacts/agent_harness/v272/evidence_inputs/hob_0a_closeout_evidence_v272.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v272/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS272_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `HOB-0-A` merged on `main` | required | `pass` | PR `#500`, merge commit `16d27c4e3458956ce96c1acaa72930ec6ecc2722` |
| Implementation stayed in the obligation-broker lane | required | `pass` | merged implementation package is `adeu_obligation_broker` |
| Selected A surfaces shipped | required | `pass` | catalog, activation assessment, inherited ledger, traversal validation report, and guardrail schemas/models shipped |
| Catalog id/version/hash authority is bound | required | `pass` | A models require catalog identity and catalog hash across catalog, activation, ledger, validation, and guardrail records |
| Model semantic judgment stays upstream-authored | required | `pass` | activation assessment validates supplied semantic posture without broker applicability decisions |
| Parent activation imports inherited children deterministically | required | `pass` | missing-child fixture fails closed; active parent fixtures expand catalog children |
| Structured proofs are required for proof-sensitive statuses | required | `pass` | proof rows are discriminated by proof kind/type and protected surfaces |
| `not_inherited` and deferral escape hatches are constrained | required | `pass` | invalid `not_inherited` and scoped-deferral-as-closure fixtures fail closed |
| Frontier rows are emitted for unresolved inherited obligations | required | `pass` | open/blocked child fixtures produce deterministic frontier rows |
| Canonical output hashing is stable | required | `pass` | shuffled input order fixture preserves canonical output/hash |
| A does not implement B/C surfaces | required | `pass` | closure aggregation, probe matrices, implementation batches, delta attribution, and integration handoff are absent |
| Non-authority guardrail denies semantic/tool/implementation authority | required | `pass` | guardrail rows deny semantic judgment, catalog mutation, probe execution, implementation, worker dispatch, product, and future-family authority |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v272_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v272/evidence_inputs/metric_key_continuity_assertion_v272.json` records exact keyset equality versus `v271` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v272/evidence_inputs/runtime_observability_comparison_v272.json` records `79 ms` baseline, `127 ms` current, `48 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v272_closeout_stop_gate_summary@1",
  "arc": "vNext+272",
  "target_path": "HOB-0-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v271": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 127,
  "runtime_observability_delta_ms": 48
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v271_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v272_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+271","baseline_elapsed_ms":79,"baseline_source":"artifacts/stop_gate/report_v271_closeout.md","current_arc":"vNext+272","current_elapsed_ms":127,"current_source":"artifacts/stop_gate/report_v272_closeout.md","delta_ms":48,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+272","broker_semantic_judgment_authority_granted":false,"catalog_identity_hash_bound":true,"catalog_mutation_authority_granted":false,"closed_slice":"HOB-0-A","closure_aggregation_authority_granted":false,"deterministic_frontier_emission_enforced":true,"family":"HOB-0","future_family_selection_granted":false,"implementation_authority_granted":false,"implementation_commits":["724f69f1110540d86d6e244d912625dd02f27039","142ea0de8dee8d3320e010eb70c53127f0c7bfb4"],"implementation_package":"packages/adeu_obligation_broker","missing_inherited_children_fail_closed":true,"model_activation_rows_remain_upstream_authored":true,"not_inherited_escape_hatch_constrained":true,"probe_execution_authority_granted":false,"probe_matrix_planning_authority_granted":false,"proof_sensitive_statuses_require_structured_proofs":true,"reference_schema_root":"packages/adeu_obligation_broker/schema","runtime_event_stream_path":"artifacts/agent_harness/v272/runtime/evidence/local/urm_events.ndjson","runtime_observability_comparison_path":"artifacts/agent_harness/v272/evidence_inputs/runtime_observability_comparison_v272.json","schema":"hob_0a_closeout_evidence@1","selected_record_shapes":["repo_hierarchical_obligation_catalog@1","repo_obligation_activation_assessment@1","repo_inherited_obligation_ledger@1","repo_obligation_traversal_validation_report@1","repo_obligation_broker_non_authority_guardrail@1"],"stale_catalog_reuse_rejected":true,"test_reference_path":"packages/adeu_obligation_broker/tests/test_hob_0a.py","traversal_validation_canonical_hash_stable":true,"verification_commands":[".venv/bin/python -m pytest packages/adeu_obligation_broker/tests -q","make lint","make arc-closeout-check ARC=272"],"worker_dispatch_authority_granted":false}
```

## Recommendation

- gate decision:
  - `HOB_0A_DETERMINISTIC_TRAVERSAL_BROKER_COMPLETE_ON_MAIN`
- rationale:
  - `v272` closes the bounded `HOB-0-A` catalog, activation assessment,
    inherited ledger, traversal validation, next-frontier, and guardrail seam on
    `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_obligation_broker`) only
    - five deterministic HOB-0-A record surfaces
    - catalog identity is hash-bound
    - activation remains upstream/model-authored semantic judgment
    - inherited child traversal is deterministic and fail-closed
    - proof-sensitive statuses require structured proof rows
    - unresolved children emit frontier rows
    - closure aggregation, probe-matrix plans, implementation batches, delta
      attribution, integration handoff, probe execution, implementation
      authority, worker dispatch, product authority, and future-family
      selection remain absent
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- family status:
  - `HOB-0` remains open; proceed to `HOB-0-B`.
