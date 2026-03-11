# Assessment vNext+56 Edges (Pre-Lock)

This document records the pre-lock edge assessment for `vNext+56` (`V35-A`
orchestration-state baseline).

Status: pre-lock assessment (March 11, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS56_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v56_pre_lock_edge_assessment",
  "required_in_decision": true,
  "notes": "This pre-lock edge set is superseded by post-closeout disposition once v56 closes."
}
```

## Scope

- In scope: thin `V35-A` baseline over canonical orchestration-state artifacts, session/
  event identity, write lease, role transition, handoff-state materialization, and closeout
  evidence integration.
- Out of scope: delegated implementation UX beyond state materialization, worker transcript
  visibility, topology/duty map UX, runtime enforcement promotion, multi-writer release,
  direct worker/user interaction, stop-gate schema-family fork, and metric-key expansion.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS55.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS55.md`
- `docs/ASSESSMENT_vNEXT_PLUS55_EDGES.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `packages/urm_runtime/src/urm_runtime/models.py`
- `packages/urm_runtime/src/urm_runtime/roles.py`
- `packages/urm_runtime/src/urm_runtime/child_dispatch.py`
- `packages/urm_runtime/src/urm_runtime/storage.py`
- `packages/urm_runtime/src/urm_runtime/events_tools.py`
- `packages/urm_runtime/src/urm_runtime/copilot.py`

## Current-State Assessment

- `urm_runtime` already contains real worker lifecycle, dispatch, persistence, and event
  foundations.
- The constitutional multi-role bundle already defines the intended authority, write-lease,
  role-transition, artifact-class, and handoff model.
- The missing surface is not “sub-agent primitives exist or not”; it is whether the current
  runtime materializes one canonical orchestration-state artifact family with sufficient
  identity, lease, transition, and reconciliation state for ADEU governance and later UX.

## Pre-Lock Edge Set (v56)

1. Canonical orchestration-state artifact absence: `open`.
   - no `orchestration_state_snapshot@1` exists on `main`.
2. Canonical execution-topology artifact absence: `open`.
   - no `execution_topology_state@1` exists on `main`.
3. Explicit write-lease-state artifact absence: `open`.
   - current dispatch tokens and worker-run rows exist, but no released `write_lease_state@1`
     exists on `main`.
4. Explicit role-transition record absence: `open`.
   - no released `role_transition_record@1` exists on `main`.
5. Canonical role-handoff envelope absence: `open`.
   - the multi-role draft defines `role_handoff_envelope@1`, but no released runtime
     artifact currently materializes it.
6. Session/event identity gap: `open`.
   - canonical state does not yet freeze `orchestrator_session_id`, `worker_session_id`,
     `parent_session_id`, `event_cursor`, and `last_reconciled_event` as one released
     artifact surface.
7. Compaction-lineage gap: `open`.
   - `continuation_bridge_ref` is now part of the planning family, but no released
     orchestration-state artifact binds pre/post-compaction continuity on `main`.
8. Scope-kind ambiguity risk: `open`.
   - current state does not freeze the scope-granularity enum in a released orchestration
     artifact surface.
9. Self-report reconciliation gap: `open`.
   - the draft constitution requires reconciliation of handoff claims, but no released
     orchestration artifact currently proves that state.
10. Worker direct user-boundary drift risk: `open`.
    - the planning family freezes this as forbidden, but no released orchestration-state
      evidence currently proves the boundary.
11. Runtime-event truth ambiguity risk: `open`.
    - `urm-events@1` exists, but no released orchestration-state contract yet marks events
      as source surfaces only rather than accepted truth.
12. Topology truth gap: `open`.
    - topology/duty visualization is explicitly out of scope for v56, so no canonical
      topology UX surface exists yet.
13. Evidence integration gap: `open`.
    - no released `v35a_orchestration_state_evidence@1` block exists on `main`.
14. Placement/accretion risk: `open`.
    - `adeu_agent_harness` is already dense; without explicit placement discipline, V35-A
      could wrongly accrete governance state into pipeline modules rather than building on
      `urm_runtime`.
15. Zero-occurrence and handoff-empty-value semantics ambiguity risk: `open`.
    - current repo state does not yet define whether no transition or no handoff should
      yield deterministic empty artifacts or omission, nor does it yet freeze canonical
      empty encodings for required but not-applicable handoff fields.
16. Worker identity scope ambiguity risk: `open`.
    - current repo state does not yet freeze whether `worker_session_id` is current-active
      state only or complete future multiworker lineage.
17. Continuation-bridge reference scope ambiguity risk: `open`.
    - current repo state does not yet freeze whether `continuation_bridge_ref` is
      current/latest state only or a future bridge graph.
18. Execution-topology state vs UX graph ambiguity risk: `open`.
    - current repo state does not yet distinguish canonical topology state from a future
      rendered topology UX surface.
19. Closeout evidence determinism explicitness gap: `open`.
    - current repo state does not yet release deterministic
      `v35a_orchestration_state_evidence@1` bytes because the artifact family does not yet
      exist.

## Guard and Sequencing Recommendation

- The next safe step is still `V35-A` only.
- `v56` should remain a state-materialization and evidence slice, not a visibility or
  enforcement slice.
- `A1` should establish canonical orchestration-state artifacts and identity fields.
- `A1` should treat `worker_session_id` and `continuation_bridge_ref` as current-state
  baseline fields only and should materialize deterministic empty transition/handoff
  artifacts rather than relying on omission.
- `A2` should prove them via evidence integration and guards.
- `A2` should keep `execution_topology_state@1` as a reconciliation/state artifact only,
  not a rendered topology UX surface, and should prove closeout evidence determinism.
- `V35-B` through `V35-E` should remain deferred until the state substrate is real.

## Stop-Gate Continuity Expectation

```json
{
  "schema": "v56_prelock_edge_summary@1",
  "arc": "vNext+56",
  "target_path": "V35-A",
  "prelock_edge_count": 19,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality_baseline": 80,
  "expected_metric_key_exact_set_equal_v55": true,
  "blocking_edges_before_lock": [
    "canonical_orchestration_state_artifact_absence",
    "session_event_identity_gap",
    "compaction_lineage_gap",
    "scope_kind_ambiguity_risk",
    "evidence_integration_gap",
    "zero_occurrence_and_handoff_empty_value_semantics_ambiguity_risk",
    "execution_topology_state_vs_ux_graph_ambiguity_risk"
  ]
}
```

## Recommendation

1. Proceed with a thin `V35-A` baseline only.
2. Treat `packages/urm_runtime` as the preferred orchestration foundation for the arc.
3. Keep worker transcript visibility, topology UX, and runtime enforcement out of scope for
   `v56`.
4. Require deterministic empty transition/handoff artifacts for zero-occurrence cases and
   frozen canonical empty-value encodings for required but not-applicable handoff fields.
5. Require canonical evidence integration and guard coverage before later `V35` paths are
   considered.
