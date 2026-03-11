# Assessment vNext+58 Edges (Pre-Lock)

This document records pre-lock edge planning for `vNext+58` (`V35-C` worker transcript and
progress visibility) before implementation.

Status: pre-lock assessment (March 11, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS58_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "authoritative_scope": "v58_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This pre-lock planning set is expected to be superseded by post-closeout edge disposition once v58 closes."
}
```

## Scope

- In scope: thin `V35-C` read-only worker transcript/progress visibility over the frozen
  v56/v57 state and delegation substrate, explicit epistemic lane labeling, explicit
  lane-absence and divergence rendering, continuation/compaction continuity visibility,
  and closeout evidence integration.
- Out of scope: topology/duty map UX, runtime enforcement promotion, multi-builder or
  multi-writer release, direct worker/user interaction, stop-gate schema-family fork,
  metric-key expansion, and the separate `O1`/`O2`/`O3` closeout-hardening bundle.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS57.md`
- `docs/ASSESSMENT_vNEXT_PLUS57_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `packages/urm_runtime/src/urm_runtime/worker.py`
- `packages/urm_runtime/src/urm_runtime/models.py`
- `packages/urm_runtime/src/urm_runtime/roles.py`
- `packages/urm_runtime/src/urm_runtime/child_dispatch.py`
- `packages/urm_runtime/src/urm_runtime/orchestration_state.py`
- `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py`
- `packages/urm_runtime/src/urm_runtime/copilot.py`
- `packages/urm_runtime/src/urm_runtime/storage.py`
- `apps/api/src/adeu_api/urm_routes.py`
- `apps/api/tests/test_urm_copilot_routes.py`
- `artifacts/quality_dashboard_v57_closeout.json`
- `artifacts/stop_gate/metrics_v57_closeout.json`
- `artifacts/agent_harness/v57/evidence_inputs/metric_key_continuity_assertion_v57.json`
- `artifacts/agent_harness/v57/evidence_inputs/runtime_observability_comparison_v57.json`
- `artifacts/agent_harness/v57/evidence_inputs/v35b_delegation_handoff_evidence_v57.json`
- `artifacts/agent_harness/v57/runtime/evidence/codex/`

## Pre-Lock Edge Set (v58 Planning)

1. Canonical worker-visibility artifact absence: `open`.
   - no released `worker_visibility_state@1` artifact or equivalent runtime read model
     exists on `main`.
2. Raw transcript lane-label gap: `open`.
   - `codex_raw.ndjson` evidence exists, but no released visibility surface labels that
     content as explicit `raw_transcript`.
3. Worker self-report projection gap: `open`.
   - unreconciled handoff/self-report content is not currently surfaced as an explicit
     `worker_self_report` lane with observational-only semantics.
4. Reconciled handoff explicit-absence gap: `open`.
   - no released surface marks `reconciled_handoff` as explicitly absent, pending, or
     present; current omission would be ambiguous.
5. Orchestrator-judgment lane gap: `open`.
   - no released visibility surface separates explicit orchestrator judgment from worker
     self-report or absent state.
6. Divergence-state gap: `open`.
   - no released typed divergence state exists for `parsing_failure`,
     `reconciliation_aborted`, or other lane disagreements.
7. Progress read-model gap: `open`.
   - no released visibility surface joins worker status, last action, blocking state,
     delegated role, scope, and latest visible event into one canonical read model.
8. Continuation-bridge and compaction visibility gap: `open`.
   - v56/v57 state records bridge/seam data, but no transcript/progress surface renders
     that continuity explicitly.
9. Raw transcript authority-drift risk: `open`.
   - visibility could accidentally present raw transcript text as accepted truth or as an
     authoritative interaction surface.
10. Worker self-report authority-drift risk: `open`.
    - visibility could accidentally present unreconciled self-report or handoff content as
      reconciled/accepted output.
11. Redaction and scope-boundary determinism gap: `open`.
    - no released v58 policy yet defines deterministic transcript redaction or scope
      trimming if visibility exposes textual worker surfaces.
12. Direct worker/user boundary confusion risk: `open`.
    - visible transcript panes could be mistaken for an authorized direct worker/user
      interaction surface without explicit boundary markers.
13. Placement/accretion risk: `open`.
    - transcript/progress logic could sprawl into app or harness code instead of landing
      as a canonical runtime read model.
14. Evidence integration gap: `open`.
    - canonical `v35c_transcript_visibility_evidence@1` does not exist on `main`.
15. Guard coverage gap for visibility failures: `open`.
    - no merged tests fail closed on missing lane labels, silent absence omission,
      flattened compaction continuity, or transcript/self-report authority drift.

## Guard Coverage Requirements

- planned `C2` coverage must fail closed on:
  - missing `worker_visibility_state@1`,
  - missing lane labels,
  - missing explicit lane-status values for absent downstream lanes,
  - missing divergence state when lanes disagree,
  - silent continuation-bridge or compaction flattening,
  - ad hoc progress-summary bypass of canonical state/event inputs,
  - raw transcript truth promotion,
  - unreconciled self-report truth promotion,
  - worker direct user-boundary drift.
- planned visibility implementation should be exercised against both:
  - a delegated child path with unreconciled self-report content,
  - a continuation-bridge or compaction-seam path where transcript continuity is split
    across sessions or streams.

## Stop-Gate Continuity Requirement

```json
{
  "schema": "v58_edge_planning_summary@1",
  "arc": "vNext+58",
  "target_path": "V35-C",
  "prelock_edge_count": 15,
  "resolved_edge_count": 0,
  "open_blocking_edges": 15,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v57_required": true,
  "all_passed": false,
  "blocking_issues": [
    "worker_visibility_state_missing",
    "epistemic_lane_projection_missing",
    "divergence_state_missing",
    "continuity_visibility_missing",
    "authority_drift_guards_missing"
  ]
}
```

## Residual Risks (Pre-Lock)

1. Transcript visibility can easily look authoritative if lane labeling and boundary
   markers are weak.
2. Existing v57 handoff content is unreconciled by default, so v58 must distinguish
   visibility from acceptance precisely.
3. Continuation/compaction visibility is easy to flatten incorrectly if the read model is
   built from convenience summaries instead of canonical bridge/seam state.
4. Topology UX and runtime enforcement remain intentionally deferred; v58 should not try to
   solve those adjacent problems indirectly.
5. Closeout hardening remains a separate operational track; v58 should not widen into
   `O1`/`O2`/`O3`.

## Recommendation (Pre-Lock)

1. Treat the committed v57 builder/support runtime/evidence bundle as a frozen prerequisite
   input, not part of new v58 scope.
2. Keep v58 limited to read-only transcript/progress visibility and explicit epistemic
   rendering.
3. Require one canonical runtime read model in `packages/urm_runtime` before adding any
   broader route or UX shaping.
4. Do not release transcript visibility without explicit lane labels, lane-status values,
   divergence states, and continuation/compaction continuity rendering.
5. Pair any `C1` visibility release with `C2` evidence/guard coverage in the same arc so
   closeout can fail closed on truth-lane drift.
