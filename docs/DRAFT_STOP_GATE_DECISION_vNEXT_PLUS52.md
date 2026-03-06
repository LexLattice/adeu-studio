# Draft Stop-Gate Decision (Pre vNext+52)

This note records the pre-start scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md`

Status: draft decision scaffold (pre-start threshold scaffold, March 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS52.md",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "authoritative_scope": "v52_pre_start_threshold_scaffold",
  "required_in_closeout": true,
  "all_passed": null,
  "notes": "This scaffold is planning-only until v52 implementation and closeout evidence supersede it."
}
```

## Decision Guardrail (Frozen)

- This draft records v52 threshold scaffolding only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md`.
- This note captures planned `V34-D` retry-context feeder evidence only; it does not by
  itself authorize automatic retry dispatch, verifier/package authority consumption, or
  any `V34-E`..`V34-G` behavior release.
- Runtime-observability comparison row remains required evidence and informational-only in
  this arc.

## Planned Evidence Source

- expected implementation PRs:
  - `A1` (`contracts: add v34d retry-context feeder baseline`)
  - `A2` (`tests: add v34d retry-context evidence and advisory guards`)
- planned deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v52_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v52_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v52_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v52/evidence_inputs/runtime_observability_comparison_v52.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v52/evidence_inputs/metric_key_continuity_assertion_v52.json`
  - retry-context evidence input:
    `artifacts/agent_harness/v52/evidence_inputs/v34d_retry_context_evidence_v52.json`
  - retry-context feeder artifact:
    `artifacts/agent_harness/v52/retry_context/<taskpack_manifest_hash>_<candidate_change_plan_hash>.json`
  - sanitization profile artifact:
    `artifacts/agent_harness/v52/retry_context/retry_context_sanitization_profile.json`
- planned closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md`
- planned closeout commands:
  - `make closeout-lint`
  - canonical deterministic closeout generation commands: `pending_v52_implementation`

## Exit-Criteria Scaffold (vNext+52)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `A1` merged with green CI | required | `pending` | `pending_v52_implementation` |
| `A2` merged with green CI | required | `pending` | `pending_v52_implementation` |
| Stop-gate schema-family continuity retained | required | `pending` | `pending_v52_closeout` |
| Stop-gate metric-key continuity retained | required | `pending` | `pending_v52_closeout` |
| Deterministic cardinality continuity retained (`80`) | required | `pending` | `pending_v52_closeout` |
| `retry_context_feeder_result@1` emitted and schema-valid | required | `pending` | `pending_v52_closeout` |
| `retry_context_sanitization_profile@1` emitted and schema-valid | required | `pending` | `pending_v52_closeout` |
| Advisory-only posture retained | required | `pending` | `pending_v52_closeout` |
| Raw repo-content inclusion remains forbidden | required | `pending` | `pending_v52_closeout` |
| Automatic retry dispatch remains out of scope | required | `pending` | `pending_v52_closeout` |
| Canonical `v34d` evidence block emitted and hash-bound | required | `pending` | `pending_v52_closeout` |
| No boundary-release expansion introduced | required | `pending` | `pending_v52_closeout` |

## Metric-Key Continuity Assertion (Scaffold)

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v51_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v52_closeout.json",
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
  "baseline_arc": "vNext+51",
  "current_arc": "vNext+52",
  "baseline_source": "artifacts/stop_gate/report_v51_closeout.md",
  "current_source": "artifacts/stop_gate/report_v52_closeout.md",
  "baseline_elapsed_ms": null,
  "current_elapsed_ms": null,
  "delta_ms": null,
  "notes": "v52 closeout remains informational-only for runtime timing/byte observability under frozen stop-gate semantics."
}
```

## V34-D Retry-Context Evidence (Scaffold)

```json
{
  "schema": "v34d_retry_context_evidence@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md#v34d_retry_context_contract@1",
  "feeder_entrypoint": null,
  "shared_feeder_engine_used": null,
  "shared_feeder_engine_identifier": null,
  "retry_context_feeder_result_path": "artifacts/agent_harness/v52/retry_context/<taskpack_manifest_hash>_<candidate_change_plan_hash>.json",
  "retry_context_feeder_result_hash": null,
  "sanitization_profile_path": "artifacts/agent_harness/v52/retry_context/retry_context_sanitization_profile.json",
  "sanitization_profile_hash": null,
  "source_rejection_diagnostic_schema": "candidate_change_plan_rejection_diagnostic@1",
  "policy_source_closed_inherited_surface": null,
  "runner_result_semantic_input_forbidden": null,
  "advisory_only_non_authoritative": null,
  "automatic_retry_dispatch_forbidden": null,
  "downstream_diagnostic_aggregation_forbidden": null,
  "policy_success_explicit_request_without_diagnostic_fails_closed": null,
  "raw_repo_file_content_forbidden": null,
  "duplicate_issue_tuples_forbidden": null,
  "excerpt_bounds_enforced": null,
  "overflow_policy": "deterministic_truncation_under_frozen_profile",
  "missing_excerpt_source_policy": "unresolvable_candidate_plan_excerpt_emits_null_typed_excerpt_and_no_repo_fallback",
  "total_output_bound_enforced": null,
  "control_marker_neutralization_enforced": null,
  "deterministic_issue_order_enforced": null,
  "verification_passed": null,
  "verification_passed_policy": "feeder_generation_guards_and_closeout_validation_only_not_policy_verification_packaging_validation_or_model_success",
  "success_path_absence_without_request_allowed": null,
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v51": null,
  "notes": "Materialize this block as deterministic JSON evidence input in v52 closeout."
}
```

## Recommendation (Pre v52)

- gate decision:
  - `GO_VNEXT_PLUS52_IMPLEMENTATION`
- rationale:
  - `v51` closed the verifier-lane `V34-C` baseline cleanly on `main`, so the next useful
    thin slice is the advisory `V34-D` feeder artifact baseline.
  - this scaffold preserves stop-gate continuity while leaving all implementation proofs to
    `A1`/`A2` and closeout regeneration.
