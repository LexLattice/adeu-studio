# Assessment vNext+57 Edges (Pre-Lock)

This document records the pre-lock edge assessment for `vNext+57` (`V35-B`
single-builder delegation and reconciled handoffs).

Status: pre-lock assessment (March 11, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS57_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v57_pre_lock_edge_assessment",
  "required_in_decision": true,
  "notes": "This pre-lock edge set is superseded by post-closeout disposition once v57 closes."
}
```

## Scope

- In scope: thin `V35-B` baseline over delegated builder/support roles, canonical delegated
  scope recording, single-builder write-lease posture, typed handoff emission, explicit
  orchestrator reconciliation, and closeout evidence integration.
- Out of scope: worker transcript visibility, topology/duty map UX, runtime enforcement
  promotion, multi-builder release, direct worker/user interaction, stop-gate schema-family
  fork, metric-key expansion, and the separate `O1`/`O2`/`O3` closeout-hardening bundle.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS56.md`
- `docs/ASSESSMENT_vNEXT_PLUS56_EDGES.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `packages/urm_runtime/src/urm_runtime/models.py`
- `packages/urm_runtime/src/urm_runtime/roles.py`
- `packages/urm_runtime/src/urm_runtime/child_dispatch.py`
- `packages/urm_runtime/src/urm_runtime/child_workflow.py`
- `packages/urm_runtime/src/urm_runtime/child_recovery.py`
- `packages/urm_runtime/src/urm_runtime/storage.py`
- `packages/urm_runtime/src/urm_runtime/orchestration_state.py`
- `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py`
- `packages/urm_runtime/src/urm_runtime/copilot.py`

## Current-State Assessment

- `v56` now provides real canonical orchestration-state artifacts and closeout evidence, so
  `V35-B` no longer needs to solve the state-materialization problem first.
- `urm_runtime` already contains real child dispatch, workflow, recovery, budgeting,
  capability policy, event tracking, and persisted child-run foundations.
- The missing surface is not “delegation primitives exist or not”; it is whether the
  current runtime materializes one released delegated-builder and reconciled-handoff lane
  with explicit role, scope, lease, and reconciliation state suitable for ADEU governance
  and later visibility UX.

## Pre-Lock Edge Set (v57)

1. Released builder role absence: `open`.
   - no `builder_worker` role exists in `urm_runtime.roles.ROLE_REGISTRY`.
2. Released support-role enum absence: `open`.
   - no released `explorer` / `validator` / `docs_helper` runtime role set exists on
     `main`.
3. Delegation request role gap: `open`.
   - `AgentSpawnRequest` does not currently record requested role or granted role.
4. Delegation task-kind gap: `open`.
   - current child-run request state does not record a canonical delegation task kind.
5. Delegated scope descriptor gap: `open`.
   - current child-run request state does not record canonical scope kind or scoped values
     at the delegation boundary.
6. Builder write-lease transfer gap: `open`.
   - current runtime records only parent `writes_allowed` and generic dispatch leases, not
     an explicit authoritative builder write-lease transfer baseline.
7. Builder/support role distinction gap: `open`.
   - current runtime materializes all child runs as generic `support_worker` state in the
     canonical snapshot.
8. Typed completed-work handoff gap: `open`.
   - `role_handoff_envelope@1` exists, but no released runtime path currently emits
     non-empty typed handoff entries for completed delegated work.
9. Explicit orchestrator reconciliation gap: `open`.
   - current repo state does not yet record an explicit orchestrator reconciliation step
     before worker output is treated as evidence-bearing delegated work.
10. Unreconciled worker-output truth ambiguity risk: `open`.
    - current child workflow can complete generic delegated work, but no released runtime
      contract yet fail-closes on treating raw child output as accepted truth without
      reconciliation.
11. Single-builder default guard gap: `open`.
    - v56 proves single-writer default at orchestration-state level, but no released v57
      lane yet guards against multiple authoritative builders in delegated execution.
12. Support-worker authority drift risk: `open`.
    - current generic child workflow does not yet distinguish support-worker advisory output
      from authoritative builder output in released runtime policy/state.
13. Worker direct user-boundary drift risk under delegated execution: `open`.
    - v56 proves the current boundary posture, but no released `V35-B` evidence lane yet
      proves that delegated builder/support execution preserves it.
14. Evidence integration gap: `open`.
    - no released `v35b_delegation_handoff_evidence@1` block exists on `main`.
15. Placement/accretion risk: `open`.
    - `adeu_agent_harness` is already dense; without explicit placement discipline, V35-B
      could wrongly accrete delegation governance into pipeline modules rather than
      extending `urm_runtime`.
16. Guard coverage gap for role/scope/handoff failures: `open`.
    - current repo state does not yet release deterministic guard coverage for invalid
      requested roles, missing scope kind, missing handoff entries, unreconciled output
      acceptance, or support-worker authority drift.

## Guard and Sequencing Recommendation

- The next safe step is still `V35-B` only.
- `v57` should remain a delegated-execution and reconciled-handoff slice, not a visibility
  or enforcement slice.
- `B1` should establish released builder/support roles, delegated role/scope recording, and
  explicit single-builder lease posture.
- `B1` should keep worker outputs non-authoritative until explicit orchestrator
  reconciliation and should emit typed handoff entries when delegated work claims concrete
  outputs.
- `B2` should prove those invariants via closeout evidence integration and guards.
- `B2` should keep transcript visibility, topology UX, and runtime promotion hardening out
  of scope.
- `V35-C` through `V35-E` should remain deferred until the delegated builder/handoff
  substrate is real.

## Stop-Gate Continuity Expectation

```json
{
  "schema": "v57_prelock_edge_summary@1",
  "arc": "vNext+57",
  "target_path": "V35-B",
  "prelock_edge_count": 16,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality_baseline": 80,
  "expected_metric_key_exact_set_equal_v56": true,
  "blocking_edges_before_lock": [
    "released_builder_role_absence",
    "delegation_request_role_gap",
    "delegated_scope_descriptor_gap",
    "builder_write_lease_transfer_gap",
    "typed_completed_work_handoff_gap",
    "explicit_orchestrator_reconciliation_gap",
    "evidence_integration_gap",
    "guard_coverage_gap_for_role_scope_handoff_failures"
  ]
}
```

## Recommendation

1. Proceed with a thin `V35-B` baseline only.
2. Treat `packages/urm_runtime` as the preferred delegation/handoff foundation for the arc.
3. Keep transcript visibility, topology UX, runtime enforcement, and multi-builder release
   out of scope for `v57`.
4. Require explicit delegated role and scope recording, single-builder lease posture, typed
   handoff emission, and explicit orchestrator reconciliation before later `V35` paths are
   considered.
5. Require canonical evidence integration and deterministic guard coverage before richer
   visibility or enforcement slices are considered.
