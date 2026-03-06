# Assessment vNext+52 Edges (Pre-Lock)

This document records pre-lock edge planning for `vNext+52` (`V34-D`
rejection-diagnostic retry-context feeder baseline).

Status: pre-lock assessment (March 6, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": true,
  "authoritative_scope": "v52_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This document is authoritative for v52 pre-lock edge planning until superseded by post-closeout disposition."
}
```

## Scope

- In scope: thin `V34-D` baseline over structured runner rejection diagnostics, deterministic
  retry-context feeder artifacts, sanitization profile freezing, and closeout evidence/guard
  integration.
- Out of scope: automatic retry dispatch, verifier/package rejection-diagnostic aggregation,
  broader `V34-C` recomputation, `V34-E` through `V34-G`, stop-gate schema-family fork,
  metric-key expansion, and `L2` boundary release.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS51.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
- `packages/adeu_agent_harness/tests/test_taskpack_runner.py`
- `packages/adeu_agent_harness/tests/test_taskpack_verifier.py`
- `packages/adeu_agent_harness/tests/test_taskpack_packaging.py`
- `artifacts/quality_dashboard_v51_closeout.json`
- `artifacts/stop_gate/metrics_v51_closeout.json`
- `artifacts/agent_harness/v51/evidence_inputs/runtime_observability_comparison_v51.json`
- `artifacts/agent_harness/v51/evidence_inputs/metric_key_continuity_assertion_v51.json`
- `artifacts/agent_harness/v51/evidence_inputs/v34c_policy_recompute_evidence_v51.json`

## Current Repo Reality

1. Structured runner rejection diagnostics already exist on `main`.
   - `run_taskpack.py` emits `candidate_change_plan_rejection_diagnostic@1` with the current
     issue surface:
     `issue_code`, `reason`, `target_path`, `hunk_index`, `line_range`, `policy_source`.
2. Verifier and packaging also emit rejection diagnostics, but they are distinct downstream
   schemas and would widen authority if folded into a first retry-context baseline.
3. No released `retry_context_feeder_result@1` artifact exists on `main`.
4. No released `retry_context_sanitization_profile@1` contract exists on `main`.
5. No shared canonical retry-context feeder helper exists on `main`.
6. Closeout evidence currently records policy recompute, matrix, signing, and stop-gate
   continuity surfaces, but no retry-context feeder artifact.

## Pre-Lock Edge Set (Draft)

1. Ad hoc retry-context construction risk: `open`.
   - current repo state has structured rejection diagnostics, but no canonical feeder
     artifact; retry-context assembly would otherwise drift across callers.
2. Authority-surface ambiguity risk: `open`.
   - runner rejection diagnostics, verifier rejection diagnostics, and packaging rejection
     diagnostics are different schema families; a thin v52 slice should choose one frozen
     authority surface rather than aggregate all three.
3. Raw repo-content leakage risk: `open`.
   - `V34-D` explicitly forbids raw repository file-content inclusion, but current code has
     no dedicated retry-context surface enforcing that bound.
4. Sanitization-profile drift risk: `open`.
   - reflected diagnostic text is untrusted input, and no released
     `retry_context_sanitization_profile@1` exists yet to freeze bounds and escaping.
5. Excerpt-boundary and control-marker ambiguity risk: `open`.
   - without a frozen bounded-excerpt rule, one implementation could reflect oversized or
     control-marker-bearing diagnostic text while another truncates or escapes it
     differently.
6. Advisory-only versus policy-authority confusion risk: `open`.
   - a retry-context feeder that is not clearly fenced could be misused as a policy or
     verifier input rather than an advisory artifact.
7. Automatic retry dispatch overreach risk: `open`.
   - “retry-context feeder automation” can easily widen into prompt dispatch or model
     orchestration unless the baseline is explicitly kept artifact-only.
8. Closeout evidence integration gap: `open`.
   - current closeout surfaces have no canonical `v34d` evidence slot, so even a good
     feeder implementation would not yet be provable on `main`.
9. Stop-gate churn risk: `open`.
   - the feeder lane should not widen stop-gate metric families or cardinality.
10. Runner-result authority ambiguity risk: `open`.
   - current repo state preserves `taskpack_runner_result@1` alongside rejection diagnostics,
     but v52 needs an explicit fence so runner-result prose or extra fields cannot become
     feeder-content authority.
11. Duplicate issue-tuple byte-stability risk: `open`.
   - without an explicit duplicate-tuple fail-closed rule, one implementation could silently
     deduplicate repeated tuples while another preserves input order.
12. Success-path request ambiguity risk: `open`.
   - v52 must freeze whether an explicit generation request on a policy-success path with no
     runner rejection diagnostic fails closed or emits an empty artifact.
13. Bound-overflow determinism risk: `open`.
   - excerpt and total-output bounds need a frozen overflow rule or two implementations can
     diverge on large diagnostics.
14. Missing excerpt-source resolution risk: `open`.
   - if candidate-plan hunks or referenced excerpt ranges cannot be resolved from canonical
     artifacts, v52 must freeze whether generation fails closed or emits a typed missing
     excerpt marker.
15. `policy_source` surface drift risk: `open`.
   - v52 ordering and duplicate identity depend on `policy_source`, so that surface must
     remain a closed inherited runner-diagnostic contract.
16. Shared feeder-engine proof ambiguity risk: `open`.
   - `shared_feeder_engine_used` alone is weaker than a frozen engine identifier in closeout
     evidence and could allow near-duplicate helpers to satisfy the evidence loosely.

## Recommended Thin Slice

1. Treat `v52` as a feeder-artifact baseline only.
   - shared canonical feeder helper
   - deterministic `retry_context_feeder_result@1`
   - deterministic `retry_context_sanitization_profile@1`
2. Freeze authority to the current runner rejection-diagnostic surface plus canonical
   candidate-plan/taskpack references.
   - do not aggregate verifier or packaging rejection diagnostics in v52
   - preserve `taskpack_runner_result@1` as binding/continuity only, not feeder semantic
     authority
3. Make advisory-only posture explicit and test-backed.
   - no verifier/package consumption
   - no automatic retry prompt dispatch
   - no feeder artifact required on policy-success paths unless generation is explicitly
     requested
   - explicit request without runner rejection diagnostics still fails closed
4. Add canonical closeout evidence and guard suites in the same arc.
   - the lane is not real until closeout can prove it on `main`
   - closeout should also bind a frozen shared feeder-engine identifier
5. Restart PR slice naming at `A1`/`A2`.

## Pre-Lock Summary (Machine-Checkable)

```json
{
  "schema": "v52_prelock_edge_summary@1",
  "arc": "vNext+52",
  "target_path": "V34-D",
  "identified_edge_count": 16,
  "recommended_scope": "thin_v34d_baseline_only",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "blocking_themes": [
    "authority_surface_must_be_frozen",
    "sibling_artifact_non_authority_must_be_explicit",
    "sanitization_profile_must_be_frozen",
    "duplicate_issue_tuple_handling_must_fail_closed",
    "success_path_request_behavior_must_be_frozen",
    "overflow_handling_must_be_frozen",
    "missing_excerpt_resolution_must_be_frozen",
    "policy_source_surface_must_remain_closed",
    "shared_feeder_engine_proof_must_be_unambiguous",
    "advisory_only_boundary_must_be_explicit",
    "closeout_evidence_slot_must_be_added"
  ]
}
```

## Recommendation

1. Draft `v52` as a thin `V34-D` baseline over runner rejection diagnostics only.
2. Keep verifier/package diagnostic aggregation, prompt dispatch, and broader retry-loop
   orchestration deferred.
3. Require deterministic feeder and sanitization-profile artifacts plus canonical `v34d`
   evidence before treating the lane as closed.
4. Freeze duplicate tuple handling and the non-authoritative role of `taskpack_runner_result@1`
   before implementation starts.
5. Freeze success-path explicit-request behavior, overflow handling, missing excerpt
   resolution, and the shared feeder-engine identifier before implementation starts.
