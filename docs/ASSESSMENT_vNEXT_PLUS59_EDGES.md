# Assessment vNext+59 Edges (Pre-Lock)

This document records pre-lock edge planning for `vNext+59` (`V35-D` dynamic topology and
duty-map observability) before implementation.

Status: pre-lock assessment (March 11, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS59_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v59_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This pre-lock planning set is expected to be superseded by post-closeout edge disposition once v59 closes."
}
```

## Scope

- In scope: thin `V35-D` read-only topology/duty map observability over the frozen v56/v57
  orchestration-state and v58 visibility substrate, explicit provenance markers, explicit
  duty and blocker rendering, continuation/compaction continuity visibility, and closeout
  evidence integration.
- Out of scope: runtime enforcement promotion, multi-builder or multi-writer release,
  direct worker/user interaction, stop-gate schema-family fork, metric-key expansion, and
  the separate `O1`/`O2`/`O3` closeout-hardening bundle.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS58.md`
- `docs/ASSESSMENT_vNEXT_PLUS58_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `packages/urm_runtime/src/urm_runtime/orchestration_state.py`
- `packages/urm_runtime/src/urm_runtime/worker_visibility.py`
- `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py`
- `packages/urm_runtime/src/urm_runtime/copilot.py`
- `apps/api/src/adeu_api/urm_routes.py`
- `apps/api/tests/test_urm_copilot_routes.py`
- `artifacts/quality_dashboard_v58_closeout.json`
- `artifacts/stop_gate/metrics_v58_closeout.json`
- `artifacts/agent_harness/v58/evidence_inputs/metric_key_continuity_assertion_v58.json`
- `artifacts/agent_harness/v58/evidence_inputs/runtime_observability_comparison_v58.json`
- `artifacts/agent_harness/v58/evidence_inputs/v35c_transcript_visibility_evidence_v58.json`
- `artifacts/agent_harness/v58/runtime/evidence/codex/`

## Pre-Lock Edge Set (v59 Planning)

1. Canonical topology/duty map artifact absence: `open`.
   - no released `topology_duty_map_state@1` artifact or equivalent runtime read model
     exists on `main`.
2. Read-only topology route/surface gap: `open`.
   - no released `urm.copilot` topology read surface exists on `main`.
3. Node provenance-marker gap: `open`.
   - no released topology UX surface materializes per-node `state_origin`,
     `reconciliation_status`, `last_updated_at`, and `last_reconciled_at`.
4. Edge provenance-marker gap: `open`.
   - no released topology UX surface materializes per-edge provenance/freshness markers or
     source refs.
5. Duty projection gap: `open`.
   - no released topology surface joins role, delegated scope, current duty, and current
     write posture into one canonical topology read model.
6. Write-lease holder emphasis gap: `open`.
   - no released topology UX surface explicitly highlights the current authoritative holder
     using canonical write-lease state.
7. Advisory blocker rendering gap: `open`.
   - no released topology UX surface distinguishes advisory support blockers from
     governance-equivalent blockers.
8. Provenance-linked drilldown gap: `open`.
   - no released topology surface links rendered node/edge state back to canonical
     orchestration, visibility, handoff, or event-stream drilldown targets while still
     keeping topology projection truth anchored in canonical artifacts.
9. Continuation-bridge and compaction visibility gap: `open`.
   - canonical state records bridge/seam data, but no released topology/duty surface
     renders that continuity explicitly.
10. Authority inflation risk: `open`.
    - topology rendering could accidentally imply governance authority, lease transfer, or
      accepted truth by presentation alone.
11. Invented-state risk: `open`.
    - topology rendering could be built from app-layer summaries or ad hoc graph state
      instead of canonical execution artifacts.
12. Placement/accretion risk: `open`.
    - topology logic could sprawl into app or harness code instead of landing as a canonical
      runtime read model.
13. Evidence integration gap: `open`.
    - canonical `v35d_topology_duty_map_evidence@1` does not exist on `main`.
14. Guard coverage gap for topology failures: `open`.
    - no merged tests fail closed on missing provenance markers, invented duty state,
      incorrect lease-holder rendering, advisory-blocker inflation, or topology continuity
      flattening.

## Guard Coverage Requirements

- planned `D2` coverage must fail closed on:
  - missing `topology_duty_map_state@1`,
  - missing node or edge provenance markers,
  - missing or unresolvable provenance refs,
  - invented topology node or edge state,
  - incorrect current write-lease holder rendering,
  - current duty rendered as an authority surface rather than explanatory state,
  - advisory blockers rendered as governance-equivalent blockers,
  - silent continuation-bridge or compaction flattening,
  - topology rendering treated as authoritative,
  - worker direct user-boundary drift in topology surfaces.
- planned topology proof shape must keep event streams in a narrower role:
  - event streams may be drilldown provenance targets,
  - topology projection truth must still come from canonical execution/visibility/lease and
    handoff artifacts.
- planned topology implementation should be exercised against both:
  - a delegated builder/support path where advisory and implementation duties coexist,
  - a continuation-bridge or compaction-seam path where topology continuity spans recovered
    sessions or streams.

## Stop-Gate Continuity Requirement

```json
{
  "schema": "v59_edge_planning_summary@1",
  "arc": "vNext+59",
  "target_path": "V35-D",
  "prelock_edge_count": 14,
  "resolved_edge_count": 0,
  "open_blocking_edges": 14,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v58_required": true,
  "all_passed": false,
  "blocking_issues": [
    "topology_duty_map_state_missing",
    "topology_route_missing",
    "provenance_marker_projection_missing",
    "advisory_blocker_rendering_missing",
    "topology_evidence_missing"
  ]
}
```

## Residual Risks (Pre-Lock)

1. Topology surfaces can easily look authoritative if provenance markers and authority
   boundaries are weak.
2. Advisory support blockers can easily be overstated if visual encoding does not separate
   urgency from authority.
3. Continuation/compaction continuity can be flattened incorrectly if the topology view is
   built from convenience summaries instead of canonical bridge/seam state.
4. Runtime enforcement remains intentionally deferred; v59 should not smuggle enforcement in
   through topology rendering.
5. Closeout hardening remains a separate operational track; v59 should not widen into
   `O1`/`O2`/`O3`.

## Recommendation (Pre-Lock)

1. Treat the committed v58 visibility/runtime/evidence bundle as a frozen prerequisite input,
   not part of new v59 scope.
2. Keep v59 limited to read-only topology/duty observability and explicit provenance-linked
   rendering.
3. Require one canonical runtime read model in `packages/urm_runtime` before adding any
   richer topology or UX shaping.
4. Do not release topology/duty rendering without explicit provenance markers, explicit
   advisory-vs-governance blocker posture, and explicit continuation/compaction continuity.
5. Pair any `D1` topology release with `D2` evidence/guard coverage in the same arc so
   closeout can fail closed on invented-state or authority-inflation drift.
