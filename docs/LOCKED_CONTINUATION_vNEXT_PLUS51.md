# Locked Continuation vNext+51 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS50.md`
- `docs/ASSESSMENT_vNEXT_PLUS50_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 6, 2026 UTC).

## Decision Basis

- `vNext+50` (`V34-B`, `Y1`/`Y2`) is merged on `main` with green CI checks.
- `vNext+50` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS50.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS50_EDGES.md` marks the released-surface `V34-B` matrix baseline
  as closed and restores eligibility for explicit `V34-C` evaluation.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` names `V34-C` as the next deferred family candidate
  after `V34-B`.
- current harness reality is narrower than a full zero-trust verifier lane:
  - runner-local policy validation is real and deterministic in
    `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`,
  - verifier currently rechecks hashes and runner self-consistency in
    `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`,
  - no released `policy_recompute_result@1` artifact exists on `main`,
  - no shared canonical policy-recompute helper exists on `main`.
- `vNext+51` therefore selects one thin `V34-C` baseline slice only:
  - shared canonical recompute subject over the current frozen runner policy scope,
  - deterministic `policy_recompute_result@1` emission in verifier lane,
  - mismatch fail-closed enforcement plus canonical closeout evidence integration,
  - no packaging-equivalence recompute expansion in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v51,
  - v51 keyset must be exactly equal to v50 keyset,
  - baseline derived cardinality at v51 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v51 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- `V34-A` signing and downstream-handoff completion remain frozen prerequisites:
  - signing subject remains `taskpack_bundle_hash`,
  - downstream runner/verifier/packaging consumption remains required and unchanged,
  - `v34a_handoff_completion_evidence@1` remains part of the canonical closeout surface.
- `V34-B` matrix baseline remains a frozen prerequisite:
  - declared matrix-lane registry/report contracts remain unchanged,
  - current released matrix parity evidence remains unchanged,
  - no adapter-kind or multi-runtime expansion is authorized in this arc.
- `V34-C` release-shape lock for v51 is frozen:
  - this arc is a verifier-lane policy-recompute and evidence slice only,
  - recompute scope must remain limited to the current runner policy validator surface,
  - no packaging or matrix parity semantics may be redefined in this arc,
  - no retry-context feeder, remote attestation, or standalone self-verification release is
    authorized in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `Z1` Shared canonical policy-recompute engine + deterministic result baseline (`V34-C`)
2. `Z2` Verifier mismatch enforcement + canonical recompute evidence/guard suite (`V34-C`)

Out-of-scope note:

- packaging-equivalence recomputation outside verifier lane in this arc,
- rejection-diagnostic retry-context feeder automation (`V34-D`) in this arc,
- remote/enclave attested verifier execution (`V34-E`) in this arc,
- standalone integrity self-verification (`V34-F`) in this arc,
- `remote_enclave` deployment mode expansion (`V34-G`) in this arc,
- multi-runtime matrix expansion in this arc,
- adapter-kind expansion beyond current passthrough support in this arc,
- multi-signer/quorum policy in this arc,
- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v51)

- v52+ rejection-diagnostic retry-context feeder automation (`V34-D`) under explicit lock
  text.
- v53+ remote/enclave attested verifier execution (`V34-E`) under explicit `L2` lock text.
- v54+ standalone bundle integrity self-verification utility (`V34-F`) under explicit lock
  text.
- v55+ optional `remote_enclave` deployment mode (`V34-G`) under explicit lock text.
- future `V34-B` follow-on expansion only after v50 closure:
  - multi-runtime lane expansion,
  - adapter-kind expansion beyond `candidate_plan_passthrough`,
  - matrix parity beyond current released adapter/mode sets.
- future `V34-C` follow-on expansion only after v51 closure:
  - broader policy scope beyond the current runner validator,
  - packaging-surface recomputation beyond verifier-lane comparison,
  - alternative verifier toolchains beyond the frozen current harness path.

## V50 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md",
  "target": "V34-C-baseline",
  "required_continuity_guards": [
    "V34_B_Y1_MATRIX_REGISTRY_GREEN",
    "V34_B_Y2_MATRIX_GUARDS_GREEN"
  ],
  "expected_relation": "v50_matrix_baseline_and_closeout_contracts_remain_frozen_while_v34c_policy_recompute_baseline_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v51.
- this narrowed machine-checkable consumption block is v50-local only and does not weaken the
  global continuity locks declared above; v36-v50 baseline continuity remains in force for
  the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V34-C Policy Recompute Contract (Machine-Checkable)

```json
{
  "schema": "v34c_policy_recompute_contract@1",
  "target_arc": "vNext+51",
  "target_path": "V34-C",
  "preserved_authority_inputs": {
    "taskpack_manifest_hash": "required",
    "candidate_change_plan_hash": "required",
    "taskpack_allowlist_schema": "taskpack/allowlist@1",
    "taskpack_forbidden_schema": "taskpack/forbidden@1",
    "taskpack_commands_schema": "taskpack/commands@1",
    "candidate_change_plan_schema": "candidate_change_plan@1",
    "runner_result_schema": "taskpack_runner_result@1",
    "runner_provenance_schema": "binding_and_consistency_input_only_not_recompute_semantic_source",
    "rejection_diagnostic_schema": "binding_and_consistency_input_only_not_recompute_semantic_source",
    "verified_result_schema": "continuity_and_sibling_output_contract_only_not_recompute_semantic_input",
    "v34a_handoff_completion_contract": "required_frozen_precondition",
    "v34b_matrix_baseline_contract": "required_frozen_precondition"
  },
  "recompute_scope_requirements": {
    "policy_recompute_result_schema": "policy_recompute_result@1",
    "shared_recompute_engine_required": true,
    "recompute_source_policy": "taskpack_allowlist_forbidden_commands_candidate_change_plan_and_runner_dry_run_only_no_logs_repo_state_or_packaging_projection",
    "policy_scope_frozen_to_current_runner_validator": [
      "allowlist_paths",
      "forbidden_paths",
      "forbidden_operation_kinds",
      "command_authority",
      "dry_run_subprocess_execution"
    ],
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
    "duplicate_issue_tuple_policy": "duplicate_issue_tuples_before_canonicalization_forbidden_fail_closed",
    "runner_reason_line_range_policy": "non_authoritative_for_exact_match",
    "runner_provenance_input_policy": "binding_and_consistency_input_only_not_recompute_semantic_source",
    "runner_rejection_diagnostic_policy": "consistency_input_only_not_exact_match_subject",
    "dry_run_input_source": "runner_result.dry_run",
    "candidate_change_plan_binding_policy": "recompute_binds_to_runner_recorded_canonical_candidate_change_plan_hash_runner_result_dry_run_supplies_execution_mode_only",
    "runner_policy_failure_input_materialization_required": true,
    "allowed_issue_codes": [
      "allowlist_violation",
      "forbidden_path_violation",
      "forbidden_operation_kind",
      "model_suggested_command_execution_detected",
      "dry_run_subprocess_execution_detected"
    ],
    "allowed_issue_codes_policy": "closed_exact_set_for_v51",
    "typed_diff_summary_required": true,
    "typed_diff_summary_fields": [
      "exact_match",
      "mismatch_fields",
      "runner_only_issues",
      "recompute_only_issues"
    ],
    "typed_diff_summary_exact_match_policy": "exact_match_true_requires_empty_mismatch_fields_runner_only_issues_and_recompute_only_issues",
    "recompute_result_emitted_on_match_and_mismatch": true,
    "verifier_success_artifact_policy": "recompute_mismatch_forbids_success_class_verification_result_artifact"
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v34c_policy_recompute_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "recompute_entrypoint",
      "shared_recompute_engine_used",
      "verifier_entrypoint",
      "policy_recompute_result_path",
      "policy_recompute_result_hash",
      "comparison_subject_fields",
      "exit_status_subject_policy",
      "issue_tuple_fields",
      "issue_tuple_order_policy",
      "issues_representation_policy",
      "duplicate_issue_tuples_forbidden",
      "allowed_issue_codes",
      "allowed_issue_codes_closed_exact",
      "candidate_change_plan_binding_policy",
      "runner_policy_failure_input_materialization_required",
      "runner_reason_line_range_non_authoritative",
      "mismatch_fail_closed",
      "exact_match_requires_empty_deltas",
      "policy_recompute_result_emitted",
      "typed_diff_summary_emitted",
      "success_class_verification_result_forbidden_on_mismatch",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v50",
      "notes"
    ]
  },
  "test_requirements": {
    "policy_recompute_result_emitted_on_match": true,
    "policy_recompute_result_emitted_on_mismatch": true,
    "policy_recompute_result_emitted_on_runner_policy_failure": true,
    "verifier_mismatch_fail_closed": true,
    "non_authoritative_recompute_source_forbidden": true
  },
  "fail_closed_conditions": [
    "runner_policy_outcome_trusted_without_independent_recompute",
    "policy_recompute_result_missing_from_verifier_path",
    "policy_recompute_result_not_emitted_on_mismatch",
    "policy_recompute_mismatch_accepted",
    "non_authoritative_recompute_source_accepted",
    "runner_reason_or_line_range_used_as_authoritative_exact_match_subject",
    "policy_scope_expansion_beyond_frozen_current_runner_validator",
    "unexpected_issue_code_emitted_by_recompute",
    "duplicate_issue_tuple_emitted_by_recompute",
    "issue_tuple_order_drift_accepted",
    "dry_run_input_not_bound_to_runner_result",
    "runner_policy_failure_path_missing_canonical_runner_result_inputs_for_recompute",
    "success_class_verification_result_emitted_after_recompute_mismatch"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## Z1) Shared Canonical Policy-Recompute Engine + Deterministic Result Baseline (`V34-C`)

### Goal

Make `V34-C` real as a shared canonical recompute contract over the current runner policy
surface rather than a verifier-side trust-by-consistency check only.

### Scope

- extract or define a shared canonical policy-recompute engine for runner/verifier use over
  the current frozen policy scope;
- emit deterministic `policy_recompute_result@1` containing:
  - runner outcome,
  - recompute outcome,
  - typed diff summary over the frozen comparison subject;
- freeze the exact-match subject to:
  - `passed`,
  - ordered issue tuples `(issue_code, target_path, hunk_index)`,
  - `exit_status`;
- treat runner rejection-diagnostic reason text, line ranges, and policy-source prose as
  non-authoritative for exact-match comparison.

### Locks

- v51 must not widen policy scope beyond the current runner validator surface.
- recompute input authority must derive only from:
  - canonical taskpack policy components,
  - canonical candidate change plan,
  - runner result dry-run flag.
- `taskpack_verification_result@1` is preserved here as a continuity and sibling-output
  contract only; it is not a semantic input to policy recomputation.
- `exit_status` in the frozen comparison subject means the runner policy verdict status under
  the frozen validator scope, not a verifier process exit code.
- logs, live repo state, packaging parity projections, and ad hoc post-analysis are
  non-authoritative recompute sources in this arc.
- `issues` in the frozen comparison subject means the lexicographically sorted list of unique
  tuples `(issue_code, target_path, hunk_index)` after canonical normalization of
  `target_path` to repo-relative posix form.
- duplicate `(issue_code, target_path, hunk_index)` tuples in recompute output are invalid
  and fail closed; they are not silently deduplicated.
- runner provenance and rejection diagnostics are binding and consistency inputs only; they do
  not contribute semantic policy authority to recompute.
- recompute must bind to the same canonical candidate change plan hash already recorded in
  runner artifacts; `runner_result.dry_run` supplies execution mode and does not authorize an
  alternate semantic source.
- runner policy-failure paths must still materialize the canonical `taskpack_runner_result@1`
  inputs required for recompute binding.
- allowed issue codes remain exactly the current runner issue-code set listed in the frozen
  contract; issue-code expansion is out of scope for this arc.
- issue tuples must sort lexicographically over `(issue_code, target_path, hunk_index)`.
- `policy_recompute_result@1` must be emitted deterministically on both exact-match and
  mismatch paths.
- no new stop-gate metric keys are authorized in this path unless explicitly released in the
  corresponding lock doc.

### Acceptance

- identical inputs produce deterministic `policy_recompute_result@1` bytes across reruns;
- exact-match cases produce empty typed diff deltas under the frozen subject;
- mismatch cases still emit deterministic `policy_recompute_result@1` with typed diff
  summary;
- runner reason text and line ranges do not affect exact-match outcome.

## Z2) Verifier Mismatch Enforcement + Canonical Recompute Evidence/Guard Suite (`V34-C`)

### Goal

Use the recompute result as an actual verifier-lane authority check and close the remaining
runner-trust gap without widening into packaging or matrix redefinition.

### Scope

- make verifier flow consume `policy_recompute_result@1` and fail closed on mismatch against
  the frozen runner comparison subject;
- require deterministic recompute artifact emission before final verifier mismatch failure;
- add canonical closeout evidence for the v34c recompute lane;
- add deterministic guard coverage for:
  - mismatch failure,
  - recompute artifact emission on mismatch,
  - recompute artifact emission on runner policy failure,
  - non-authoritative recompute-source rejection.

### Locks

- mismatch is error-only and fail-closed.
- verifier-lane recompute must not redefine or widen packaging, matrix, or taskpack
  semantics.
- if recompute mismatch is detected, verifier must still emit `policy_recompute_result@1` but
  must not emit a success-class verification result artifact.
- closeout proof must distinguish between:
  - `policy_recompute_result@1`,
  - verifier success/failure outcome,
  - docs-side `v34c_policy_recompute_evidence@1`.
- closeout evidence must bind to the deterministic recompute artifact by hash and retain the
  frozen comparison-subject definition.
- runtime-observability evidence remains required and informational-only.

### Acceptance

- verifier fails closed when recompute outcome mismatches runner provenance under the frozen
  subject;
- verifier still emits deterministic recompute artifact on mismatch paths;
- closeout path emits the required `v34c_policy_recompute_evidence@1` block;
- deterministic guard suites remain green under frozen environment requirements.

## Stop-Gate Impact (v51)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v51 closeout must include runtime-observability comparison row against v50 baseline.
- v51 closeout must include metric-key continuity assertion against v50 baseline.
- v51 closeout must include policy-recompute evidence block:
  - block schema is docs-only `v34c_policy_recompute_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a deterministic
    JSON evidence input artifact, included in the canonical closeout path, and treated as
    closeout-authoritative only after implementation,
  - required keys are:
    - `schema`
    - `contract_source`
    - `recompute_entrypoint`
    - `shared_recompute_engine_used`
    - `verifier_entrypoint`
    - `policy_recompute_result_path`
    - `policy_recompute_result_hash`
    - `comparison_subject_fields`
    - `exit_status_subject_policy`
    - `issue_tuple_fields`
    - `issue_tuple_order_policy`
    - `issues_representation_policy`
    - `duplicate_issue_tuples_forbidden`
    - `allowed_issue_codes`
    - `allowed_issue_codes_closed_exact`
    - `candidate_change_plan_binding_policy`
    - `runner_policy_failure_input_materialization_required`
    - `runner_reason_line_range_non_authoritative`
    - `mismatch_fail_closed`
    - `exact_match_requires_empty_deltas`
    - `policy_recompute_result_emitted`
    - `typed_diff_summary_emitted`
    - `success_class_verification_result_forbidden_on_mismatch`
    - `verification_passed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v50`
    - `notes`

## Error/Exit Policy (v51)

- No new URM runtime error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v51 introduces new recompute-specific harness diagnostics, they must be constrained to an
  authoritative `AHK51xx` registry and remain error-only with non-zero exit behavior.
- If v51 introduces new recompute diagnostics, deterministic issue ordering must sort by
  `(issue_code, artifact_path, comparison_field, target_path, hunk_index)`.
- for recompute exact-match subjects, issue tuples serialize in the frozen field order
  `(issue_code, target_path, hunk_index)` and mismatch fields remain lexicographically
  sorted.
- for recompute diagnostic ordering, `comparison_field` serializes only from the frozen set
  `{passed, issues, exit_status}`.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v34c policy recompute result baseline`
2. `tests: add v34c verifier mismatch and evidence guards`

## Intermediate Preconditions (for v51 start)

1. v50 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v50 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS50.md`
3. Existing v50 matrix baseline remains available at v51 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/matrix_parity.py`
   - `artifacts/agent_harness/v50/evidence_inputs/v34b_matrix_parity_evidence_v50.json`
4. Existing runner/verifier surfaces remain available at v51 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
5. Existing v50 closeout artifacts remain available at v51 start:
   - `artifacts/quality_dashboard_v50_closeout.json`
   - `artifacts/stop_gate/metrics_v50_closeout.json`
   - `artifacts/stop_gate/report_v50_closeout.md`
   - `artifacts/agent_harness/v50/evidence_inputs/runtime_observability_comparison_v50.json`
   - `artifacts/agent_harness/v50/evidence_inputs/metric_key_continuity_assertion_v50.json`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. No additional `L2` boundary release beyond v50 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `Z1` and `Z2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V34-C` policy recompute baseline closes the verifier-lane runner-trust gap without
  widening policy scope beyond the current runner validator.
- v51 closeout evidence includes runtime-observability comparison row against v50 baseline,
  metric-key continuity assertion against v50 baseline, and
  `v34c_policy_recompute_evidence@1`.
- `policy_recompute_result@1` is deterministic and emitted on both exact-match and mismatch
  paths.
- verifier mismatch enforcement fails closed on policy recompute drift.
- v36-v50 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
