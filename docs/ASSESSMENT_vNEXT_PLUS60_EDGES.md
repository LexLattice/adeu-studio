# Assessment vNext+60 Edges (Pre-Lock)

This document records pre-lock edge planning for `vNext+60` (`V35-E` bounded runtime
enforcement) before implementation.

Status: pre-lock assessment (March 12, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS60_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v60_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This pre-lock planning set is expected to be superseded by post-closeout edge disposition once v60 closes."
}
```

## Scope

- In scope: thin `V35-E` bounded runtime enforcement over the frozen v56/v57/v58/v59
  orchestration-state, delegation, visibility, and topology substrate; deterministic denial
  surfaces for narrow constitutional violations; and closeout evidence integration.
- Out of scope: multi-builder or multi-writer release, topology editing, direct
  worker/user interaction, acceptance/closeout automation, stop-gate schema-family fork,
  metric-key expansion, and the separate `O1`/`O2`/`O3` closeout-hardening bundle.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS59.md`
- `docs/ASSESSMENT_vNEXT_PLUS59_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `packages/urm_runtime/src/urm_runtime/capability_policy.py`
- `packages/urm_runtime/src/urm_runtime/copilot.py`
- `packages/urm_runtime/src/urm_runtime/child_dispatch.py`
- `packages/urm_runtime/src/urm_runtime/orchestration_state.py`
- `packages/urm_runtime/src/urm_runtime/worker_visibility.py`
- `packages/urm_runtime/src/urm_runtime/topology_duty_map.py`
- `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py`
- `apps/api/src/adeu_api/urm_routes.py`
- `apps/api/tests/test_urm_copilot_routes.py`
- `artifacts/quality_dashboard_v59_closeout.json`
- `artifacts/stop_gate/metrics_v59_closeout.json`
- `artifacts/agent_harness/v59/evidence_inputs/metric_key_continuity_assertion_v59.json`
- `artifacts/agent_harness/v59/evidence_inputs/runtime_observability_comparison_v59.json`
- `artifacts/agent_harness/v59/evidence_inputs/v35d_topology_duty_map_evidence_v59.json`
- `artifacts/agent_harness/v59/runtime/evidence/codex/`

## Pre-Lock Edge Set (v60 Planning)

1. Bounded runtime-enforcement surface absence: `open`.
   - no released `V35-E` runtime-enforcement lane exists on `main`.
2. Spawn-boundary constitutional enforcement gap: `open`.
   - released spawn validation is still partial and baseline-specific rather than a closed
     bounded-enforcement surface over the v35 constitution.
3. Single-builder default denial-surface gap: `open`.
   - no released runtime bundle explicitly proves that a single-builder default violation
     is denied deterministically under the frozen topology model.
4. Support-role proxy-authority enforcement gap: `open`.
   - no released runtime bundle explicitly denies support-role proxy write authority or
     equivalent authority-surface escalation attempts.
5. Claimed-work handoff required-field enforcement gap: `open`.
   - no released runtime bundle explicitly promotes the claimed-work handoff grammar into a
     bounded denial surface at orchestration/materialization boundaries.
6. Scope-kind enforcement gap: `open`.
   - scope-granularity kinds are frozen canonically, but no released runtime lane proves
     malformed or absent scope kinds are rejected at the bounded enforcement surface.
7. Deterministic denial-code surface gap: `open`.
   - no released `V35-E` lane freezes a stable denial-code/error-only contract for the
     bounded constitutional violations.
8. Observability non-authority preservation under enforcement gap: `open`.
   - no released runtime bundle proves topology/visibility surfaces stay read-only and
     non-authoritative after enforcement logic is added.
9. Acceptance/closeout authority preservation under enforcement gap: `open`.
   - no released runtime bundle proves enforcement additions do not leak acceptance or
     closeout authority beyond ADEU / `main_orchestrator`.
10. Worker direct user-boundary preservation under enforcement gap: `open`.
    - no released runtime bundle proves enforcement additions do not create or imply a
      direct worker/user boundary.
11. Placement/accretion risk: `open`.
    - runtime enforcement could sprawl into app or harness code instead of landing as a
      bounded canonical runtime surface.
12. Evidence integration gap: `open`.
    - canonical `v35e_runtime_enforcement_evidence@1` does not exist on `main`.
13. Guard coverage gap for enforcement failures: `open`.
    - no merged tests fail closed on accepted invalid role/task/scope combinations,
      accepted support-role proxy authority, accepted handoff required-field gaps, or
      denial-code drift.

## Guard Coverage Requirements

- planned `E2` coverage must fail closed on:
  - missing `V35-E` enforcement surface,
  - accepted invalid role/task/scope combinations,
  - accepted single-builder default violations,
  - accepted support-role proxy authority,
  - accepted claimed-work handoff required-field gaps,
  - accepted malformed or absent scope kinds,
  - observability surfaces promoted into authority surfaces,
  - acceptance/closeout authority drift,
  - worker direct user-boundary drift,
  - unstable or missing deterministic denial codes.
- planned enforcement proof shape must keep existing observability surfaces narrower:
  - topology and visibility remain read-only and non-authoritative,
  - enforcement consumes canonical state/visibility/topology/handoff inputs rather than
    replacing them.
- planned enforcement implementation should be exercised against both:
  - a valid builder/support delegation path that remains green,
  - invalid bounded-authority cases that are rejected deterministically.

## Stop-Gate Continuity Requirement

```json
{
  "schema": "v60_edge_planning_summary@1",
  "arc": "vNext+60",
  "target_path": "V35-E",
  "prelock_edge_count": 13,
  "resolved_edge_count": 0,
  "open_blocking_edges": 13,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v59_required": true,
  "all_passed": false,
  "blocking_issues": [
    "runtime_enforcement_surface_missing",
    "deterministic_denial_surface_missing",
    "support_role_proxy_authority_enforcement_missing",
    "claimed_work_handoff_enforcement_missing",
    "runtime_enforcement_evidence_missing"
  ]
}
```

## Residual Risks (Pre-Lock)

1. Runtime enforcement can easily overreach into authority promotion if the lane is not
   kept explicitly bounded.
2. Deterministic denial codes can drift into ad hoc behavior if the rejected-case surface
   is not frozen and tested directly.
3. Observability surfaces can be silently promoted into truth or authority if enforcement
   and read-only rendering are not kept separate.
4. Runtime enforcement remains intentionally narrower than acceptance/closeout governance;
   v60 should not smuggle automation into those lanes.
5. Closeout hardening remains a separate operational track; v60 should not widen into
   `O1`/`O2`/`O3`.

## Recommendation (Pre-Lock)

1. Treat the committed v59 runtime/evidence bundle as a frozen prerequisite input, not part
   of new v60 scope.
2. Keep v60 limited to bounded runtime enforcement and deterministic denial surfaces.
3. Require enforcement to land in `packages/urm_runtime` before any broader UX or
   operational widening.
4. Do not release enforcement without explicit denial-code stability, explicit
   observability non-authority preservation, and explicit authority-preservation guards.
5. Pair any `E1` enforcement release with `E2` evidence/guard coverage in the same arc so
   closeout can fail closed on accepted constitutional violations or authority drift.
