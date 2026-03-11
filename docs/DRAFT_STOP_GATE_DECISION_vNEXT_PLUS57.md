# Draft Stop-Gate Decision (Pre vNext+57)

This note records the pre-start stop-gate scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md`

Status: draft decision scaffold (pre-start, March 11, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS57.md",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "authoritative_scope": "v57_pre_start_stop_gate_scaffold",
  "required_in_closeout": true,
  "all_passed": null,
  "notes": "Scaffold only. Populate with post-closeout evidence and final decision values once v57 implementation and closeout complete."
}
```

## Decision Guardrail (Frozen)

- This draft is a pre-start scaffold only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md`.
- This note captures the planned `V35-B` single-builder delegation and reconciled-handoff
  closeout surface only; it does not authorize `V35-C` through `V35-E`, transcript
  visibility, topology UX, runtime enforcement promotion, closeout-hardening execution, or
  multi-writer release by itself.
- Canonical delegated role/scope/lease state, typed handoff emission, orchestrator
  reconciliation, and cumulative closeout evidence integration are the intended evidence
  surfaces for this arc.
- Runtime-observability comparison row remains required evidence and informational-only in
  this arc.

## Planned Evidence Source (Scaffold)

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `B1` `contracts: add v35b delegation and handoff baseline`
  - `B2` `tests: add v35b delegation evidence and guard suite`
- deterministic closeout artifacts (planned):
  - quality dashboard JSON: `artifacts/quality_dashboard_v57_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v57_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v57_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v57/evidence_inputs/runtime_observability_comparison_v57.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v57/evidence_inputs/metric_key_continuity_assertion_v57.json`
  - delegation/handoff evidence input:
    `artifacts/agent_harness/v57/evidence_inputs/v35b_delegation_handoff_evidence_v57.json`

## Planned Threshold Snapshot (Scaffold)

| Check | Required | Planned Result | Notes |
|---|---|---|---|
| `stop_gate_metrics@1` remains the only schema family | required | `pending` | No schema-family fork authorized |
| Metric keyset is exactly equal to `v56` | required | `pending` | Cardinality must remain `80` |
| Canonical delegation/handoff evidence emitted | required | `pending` | `v35b_delegation_handoff_evidence@1` |
| Builder role and delegated scope are recorded canonically | required | `pending` | Requested/granted role plus scope-kind required |
| Single-builder default remains enforced | required | `pending` | No multi-builder or multi-writer release |
| Support workers remain non-authoritative | required | `pending` | Advisory/scratch only unless explicitly re-roled |
| Handoff entries and reconciliation are required | required | `pending` | Completed claimed work must not rely on raw worker output alone |
| Worker direct user-boundary remains forbidden | required | `pending` | No worker authoritative chat surface |
| Runtime observability comparison captured | required | `pending` | Informational only |

## Metric-Key Continuity Assertion (Scaffold)

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v56_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v57_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (Scaffold)

```json
{
  "schema": "runtime_observability_comparison@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_arc": "vNext+56",
  "current_arc": "vNext+57",
  "baseline_source": "artifacts/stop_gate/report_v56_closeout.md",
  "current_source": "artifacts/stop_gate/report_v57_closeout.md",
  "baseline_elapsed_ms": null,
  "current_elapsed_ms": null,
  "delta_ms": null,
  "notes": "Populate on closeout. Runtime timing and byte observability remain informational-only under frozen stop-gate semantics."
}
```

## V35-B Delegation/Handoff Evidence (Scaffold)

```json
{
  "schema": "v35b_delegation_handoff_evidence@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md#v35b_delegation_handoff_contract@1",
  "evidence_input_path": "artifacts/agent_harness/v57/evidence_inputs/v35b_delegation_handoff_evidence_v57.json",
  "orchestration_state_snapshot_path": null,
  "orchestration_state_snapshot_hash": null,
  "write_lease_state_path": null,
  "write_lease_state_hash": null,
  "role_transition_record_path": null,
  "role_transition_record_hash": null,
  "role_handoff_envelope_path": null,
  "role_handoff_envelope_hash": null,
  "builder_role_materialized": null,
  "support_roles_materialized": null,
  "delegated_scope_kind_recorded": null,
  "single_builder_default_enforced": null,
  "support_workers_non_authoritative": null,
  "handoff_entry_materialized": null,
  "handoff_reconciliation_required": null,
  "unreconciled_worker_output_non_authoritative": null,
  "worker_direct_user_boundary_forbidden": null,
  "verification_passed": null,
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v56": null,
  "notes": "Populate on closeout. Completed delegated work must emit typed handoff entries and remain non-authoritative until explicit orchestrator reconciliation rather than relying on raw worker output alone."
}
```

## Exit Criteria (Scaffold)

- `B1` and `B2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- canonical delegated role/scope/lease and reconciled-handoff surfaces exist and are
  deterministic.
- completed delegated work emits typed handoff entries and explicit reconciliation
  requirement rather than omission.
- support workers remain non-authoritative and worker direct user-boundary release does not
  occur.
- v57 closeout evidence includes runtime-observability comparison row against v56 baseline,
  metric-key continuity assertion against v56 baseline, and
  `v35b_delegation_handoff_evidence@1`.

## Recommendation (Pre-Start)

- gate decision:
  - `GO_VNEXT_PLUS57_IMPLEMENTATION_DRAFT`
- rationale:
  - `v56` closes the `V35-A` state-materialization gap and makes the next safe step the
    narrow delegated-execution baseline rather than richer visibility or enforcement.
  - `V35-B` is the narrowest safe follow-on slice because it makes one-builder delegation
    and explicit reconciled handoffs real before transcript visibility, topology UX, or
    runtime promotion hardening.
