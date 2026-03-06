# Draft Stop-Gate Decision (Pre-Start vNext+51)

This note reserves the pre-start threshold scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md`

Status: draft decision scaffold (pre-start only, March 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS51.md",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "authoritative_scope": "v51_prestart_threshold_scaffold_only",
  "required_in_closeout": true,
  "all_passed": null,
  "notes": "This is a pre-start scaffold only. Planned evidence slots below are not closeout proof."
}
```

## Decision Guardrail (Frozen)

- This scaffold reserves v51 closeout slots only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md`.
- This note is non-authoritative until v51 closes on `main`.
- `V34-A` downstream signing completion and `V34-B` matrix baseline remain authoritative
  prerequisites while v51 is still planning.
- Runtime-observability comparison evidence remains required and informational-only in this
  arc.

## Planned Evidence Source Shape

- expected CI workflow:
  - `ci` on `main`
- expected implementation PRs:
  - `Z1` shared canonical policy recompute engine + deterministic result baseline
  - `Z2` verifier mismatch enforcement + canonical recompute evidence/guard suite
- expected deterministic closeout artifacts:
  - `artifacts/quality_dashboard_v51_closeout.json`
  - `artifacts/stop_gate/metrics_v51_closeout.json`
  - `artifacts/stop_gate/report_v51_closeout.md`
- expected deterministic evidence input artifacts:
  - `artifacts/agent_harness/v51/evidence_inputs/runtime_observability_comparison_v51.json`
  - `artifacts/agent_harness/v51/evidence_inputs/metric_key_continuity_assertion_v51.json`
  - `artifacts/agent_harness/v51/evidence_inputs/v34c_policy_recompute_evidence_v51.json`
- expected deterministic recompute artifacts:
  - `artifacts/agent_harness/v51/policy_recompute/`

## Planned Exit-Criteria Check (vNext+51)

| Criterion | Threshold | Planned Result Slot | Evidence Slot |
|---|---|---|---|
| `Z1` merged with green CI | required | `pending` | merge commit + CI run |
| `Z2` merged with green CI | required | `pending` | merge commit + CI run |
| Stop-gate schema-family continuity retained | required | `pending` | `metrics_v51_closeout.json` |
| Stop-gate metric-key continuity retained | required | `pending` | `metric_key_continuity_assertion_v51.json` |
| Deterministic cardinality continuity retained (`80`) | required | `pending` | `metrics_v51_closeout.json` |
| `policy_recompute_result@1` emitted and schema-valid | required | `pending` | `artifacts/agent_harness/v51/policy_recompute/` |
| Exact-match subject remains frozen to passed/issues/exit_status | required | `pending` | `v34c_policy_recompute_evidence_v51.json` |
| Runner reason and line-range fields remain non-authoritative | required | `pending` | `v34c_policy_recompute_evidence_v51.json` |
| Allowed issue-code set remains frozen and exact | required | `pending` | `v34c_policy_recompute_evidence_v51.json` |
| Duplicate issue tuples are rejected fail closed | required | `pending` | merged guard suites |
| Recompute mismatch fails closed in verifier lane | required | `pending` | merged guard suites |
| Recompute artifact still emits on mismatch paths | required | `pending` | merged guard suites |
| No success-class verification result survives recompute mismatch | required | `pending` | merged guard suites |
| No boundary-release expansion introduced | required | `pending` | lock-scope audit |

Summary slot (to be completed only at closeout):

- `schema = "stop_gate_metrics@1"`
- `valid = null`
- `all_passed = null`
- `issues = []`
- `derived_cardinality = null`

## Planned Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v50_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v51_closeout.json",
  "expected_relation": "exact_keyset_equality",
  "expected_cardinality": 80,
  "metric_key_exact_set_equal_v50": null,
  "metric_key_cardinality": null
}
```

## Planned Runtime Observability Comparison (v50 Baseline vs v51 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_arc": "vNext+50",
  "current_arc": "vNext+51",
  "baseline_source": "artifacts/stop_gate/report_v50_closeout.md",
  "current_source": "artifacts/stop_gate/report_v51_closeout.md",
  "baseline_elapsed_ms": null,
  "current_elapsed_ms": null,
  "delta_ms": null,
  "notes": "Populate only at v51 closeout; runtime timing remains informational-only."
}
```

## Planned V34-C Policy Recompute Evidence

```json
{
  "schema": "v34c_policy_recompute_evidence@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md#v34c_policy_recompute_contract@1",
  "recompute_entrypoint": "packages/adeu_agent_harness.policy_recompute.recompute_policy_validation",
  "shared_recompute_engine_used": null,
  "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
  "policy_recompute_result_path": null,
  "policy_recompute_result_hash": null,
  "comparison_subject_fields": [
    "passed",
    "issues",
    "exit_status"
  ],
  "exit_status_subject_policy": "runner_policy_verdict_status_under_frozen_validator_scope_not_verifier_process_exit_code",
  "issue_tuple_fields": [
    "issue_code",
    "target_path",
    "hunk_index"
  ],
  "issue_tuple_order_policy": "lexicographic_over_issue_code_target_path_hunk_index",
  "issues_representation_policy": "lexicographically_sorted_unique_issue_tuple_list_with_repo_relative_posix_target_paths",
  "duplicate_issue_tuples_forbidden": true,
  "allowed_issue_codes": [
    "allowlist_violation",
    "forbidden_path_violation",
    "forbidden_operation_kind",
    "model_suggested_command_execution_detected",
    "dry_run_subprocess_execution_detected"
  ],
  "allowed_issue_codes_closed_exact": true,
  "candidate_change_plan_binding_policy": "recompute_binds_to_runner_recorded_canonical_candidate_change_plan_hash_runner_result_dry_run_supplies_execution_mode_only",
  "runner_policy_failure_input_materialization_required": true,
  "runner_reason_line_range_non_authoritative": true,
  "mismatch_fail_closed": null,
  "exact_match_requires_empty_deltas": null,
  "policy_recompute_result_emitted": null,
  "typed_diff_summary_emitted": null,
  "success_class_verification_result_forbidden_on_mismatch": null,
  "verification_passed": null,
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v50": null,
  "notes": "Populate only at v51 closeout after Z1/Z2 merge and recompute artifact generation."
}
```

## Pre-Start Failure Conditions (Scaffold)

- fail closed if baseline and current metrics artifact paths are identical.
- fail closed if planned v51 closeout attempts to claim a new stop-gate metric key without
  explicit lock release.
- fail closed if planned recompute source widens beyond canonical taskpack policy components,
  canonical candidate change plan, and runner dry-run input.
- fail closed if planned v51 recompute emits any issue code outside the frozen allowed set.
- fail closed if planned v51 recompute emits duplicate `(issue_code, target_path, hunk_index)`
  tuples before canonicalization.
- fail closed if planned exact-match subject depends on runner reason text, line ranges, or
  policy-source prose.
- fail closed if planned verifier mismatch path omits deterministic
  `policy_recompute_result@1`.
- fail closed if planned verifier mismatch path still emits a success-class verification
  result artifact.
- fail closed if planned v51 closeout claims packaging-equivalence recomputation, matrix
  expansion, or remote/enclave release beyond the frozen v51 scope.

## Recommendation (Pre-Start)

- gate decision:
  - `PENDING_VNEXT_PLUS51_EXECUTION`
- rationale:
  - v50 is closed and unblocks explicit `V34-C` evaluation,
  - current implementation supports an honest thin verifier-lane recompute baseline,
  - closeout proof must wait for actual Z1/Z2 implementation and evidence generation.
