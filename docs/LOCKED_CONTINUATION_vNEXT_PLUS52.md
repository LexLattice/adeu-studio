# Locked Continuation vNext+52 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS51.md`
- `docs/ASSESSMENT_vNEXT_PLUS51_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 6, 2026 UTC).

## Decision Basis

- `vNext+51` (`V34-C`, `Z1`/`Z2`) is merged on `main` with green CI checks.
- `vNext+51` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS51.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS51_EDGES.md` marks the verifier-lane `V34-C` policy-recompute
  baseline as closed and restores eligibility for explicit `V34-D` evaluation.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` names `V34-D` as the next deferred family candidate
  after the current trust-baseline lanes.
- current harness reality is narrower than a full retry orchestration lane:
  - runner-local structured rejection diagnostics are real and deterministic in
    `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`,
  - verifier and packaging rejection diagnostics are real, but they are downstream
    component-local families with different issue surfaces,
  - no released `retry_context_feeder_result@1` artifact exists on `main`,
  - no released `retry_context_sanitization_profile@1` contract exists on `main`,
  - no shared canonical retry-context feeder helper exists on `main`.
- `vNext+52` therefore selects one thin `V34-D` baseline slice only:
  - shared canonical advisory retry-context feeder over the current runner rejection
    diagnostic surface,
  - deterministic `retry_context_feeder_result@1` and frozen
    `retry_context_sanitization_profile@1`,
  - canonical closeout evidence integration plus guard coverage,
  - no automatic retry dispatch or downstream policy-authority consumption in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v52,
  - v52 keyset must be exactly equal to v51 keyset,
  - baseline derived cardinality at v52 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v52 is frozen:
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
- `V34-C` verifier-lane policy-recompute baseline remains a frozen prerequisite:
  - recompute comparison subject and fail-closed verifier behavior remain unchanged,
  - `policy_recompute_result@1` and `v34c_policy_recompute_evidence@1` remain part of the
    canonical closeout surface,
  - no broader policy recomputation beyond the frozen current runner validator is authorized
    in this arc.
- `V34-D` release-shape lock for v52 is frozen:
  - this arc is an advisory retry-context feeder and evidence slice only,
  - feeder scope must remain limited to the current runner rejection-diagnostic surface plus
    canonical candidate-plan/taskpack references,
  - no automatic retry prompt dispatch or model execution release is authorized in this arc,
  - no verifier/package diagnostic aggregation is authorized in this arc,
  - no packaging, matrix, or policy semantics may be redefined in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `A1` Shared canonical retry-context feeder + deterministic sanitization-profile baseline (`V34-D`)
2. `A2` Canonical retry-context evidence + guard suite and advisory-only integration (`V34-D`)

Out-of-scope note:

- automatic retry prompt dispatch or model invocation in this arc,
- verifier and packaging rejection-diagnostic aggregation in this arc,
- broader policy recomputation beyond the current runner validator in this arc,
- packaging-equivalence recomputation outside verifier lane in this arc,
- rejection-diagnostic retry loop execution policy in this arc,
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

## Deferred Follow-on Candidates (Non-v52)

- v53+ remote/enclave attested verifier execution (`V34-E`) under explicit `L2` lock text.
- v54+ standalone bundle integrity self-verification utility (`V34-F`) under explicit lock
  text.
- v55+ optional `remote_enclave` deployment mode (`V34-G`) under explicit lock text.
- future `V34-C` follow-on expansion only after v51 closure:
  - broader policy scope beyond the current runner validator,
  - packaging-surface recomputation beyond verifier-lane comparison,
  - alternative verifier toolchains beyond the frozen current harness path.
- future `V34-D` follow-on expansion only after v52 closure:
  - verifier/package rejection-diagnostic aggregation beyond the current runner surface,
  - automatic retry prompt assembly or execution orchestration,
  - richer excerpt families beyond rejection diagnostics and canonical candidate-plan hunks.
- future `V34-B` follow-on expansion only after v50 closure:
  - multi-runtime lane expansion,
  - adapter-kind expansion beyond `candidate_plan_passthrough`,
  - matrix parity beyond current released adapter/mode sets.

## V51 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md",
  "target": "V34-D-baseline",
  "required_continuity_guards": [
    "V34_C_Z1_POLICY_RECOMPUTE_BASELINE_GREEN",
    "V34_C_Z2_MISMATCH_GUARDS_GREEN"
  ],
  "expected_relation": "v51_policy_recompute_baseline_and_closeout_contracts_remain_frozen_while_v34d_retry_context_feeder_baseline_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v52.
- this narrowed machine-checkable consumption block is v51-local only and does not weaken the
  global continuity locks declared above; v36-v51 baseline continuity remains in force for
  the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V34-D Retry-Context Contract (Machine-Checkable)

```json
{
  "schema": "v34d_retry_context_contract@1",
  "target_arc": "vNext+52",
  "target_path": "V34-D",
  "preserved_authority_inputs": {
    "taskpack_manifest_hash": "required",
    "candidate_change_plan_hash": "required",
    "candidate_change_plan_schema": "candidate_change_plan@1",
    "runner_result_schema": "binding_and_continuity_sibling_artifact_only_not_feeder_semantic_input",
    "runner_rejection_diagnostic_schema": "candidate_change_plan_rejection_diagnostic@1",
    "v34a_handoff_completion_contract": "required_frozen_precondition",
    "v34b_matrix_baseline_contract": "required_frozen_precondition",
    "v34c_policy_recompute_contract": "required_frozen_precondition"
  },
  "feeder_scope_requirements": {
    "retry_context_feeder_result_schema": "retry_context_feeder_result@1",
    "retry_context_sanitization_profile_schema": "retry_context_sanitization_profile@1",
    "shared_feeder_engine_required": true,
    "feeder_authority_source_policy": "candidate_change_plan_rejection_diagnostic_plus_canonical_candidate_change_plan_and_taskpack_manifest_references_only_no_repo_reads_live_workspace_state_or_downstream_component_rejection_diagnostics",
    "feeder_scope_frozen_to_current_runner_rejection_surface": [
      "issue_code",
      "reason",
      "target_path",
      "hunk_index",
      "line_range",
      "policy_source"
    ],
    "policy_source_policy": "closed_inherited_surface_from_candidate_change_plan_rejection_diagnostic_contract_no_v52_expansion",
    "runner_result_input_policy": "binding_and_continuity_sibling_artifact_only_not_feeder_semantic_source",
    "advisory_only_policy": "retry_context_feeder_result_is_non_authoritative_and_must_not_be_consumed_as_policy_verification_or_packaging_input",
    "automatic_retry_dispatch_forbidden": true,
    "downstream_diagnostic_aggregation_forbidden": true,
    "emission_policy": "explicit_rejection_diagnostic_driven_generation_only_not_required_on_policy_success_paths",
    "policy_success_absence_policy": "no_retry_context_feeder_result_expected_on_policy_success_paths_unless_generation_was_explicitly_requested",
    "policy_success_explicit_request_policy": "explicit_generation_request_without_runner_rejection_diagnostic_fails_closed",
    "excerpt_source_policy": "bounded_reason_text_and_candidate_change_plan_hunk_content_already_present_in_canonical_artifacts_only",
    "missing_excerpt_source_policy": "unresolvable_candidate_plan_excerpt_emits_null_typed_excerpt_and_no_repo_fallback",
    "raw_repo_file_content_policy": "forbidden",
    "target_path_normalization_policy": "repo_relative_posix",
    "duplicate_issue_tuple_policy": "duplicate_issue_tuples_after_target_path_normalization_and_before_feeder_serialization_forbidden_fail_closed",
    "excerpt_bounds_required": true,
    "sanitization_profile_required_fields": [
      "max_issue_count",
      "max_reason_chars",
      "max_excerpt_lines_per_issue",
      "max_excerpt_chars_per_issue",
      "max_total_output_chars",
      "control_marker_neutralization",
      "escaping_policy",
      "whitespace_policy"
    ],
    "overflow_policy": "deterministic_truncation_under_frozen_profile",
    "control_marker_policy": "prompt_and_fence_like_control_markers_must_be_neutralized",
    "escaping_policy": "deterministic_json_safe_text_encoding",
    "typed_excerpt_fields": [
      "issue_reference",
      "sanitized_reason_excerpt",
      "sanitized_candidate_plan_excerpt"
    ],
    "deterministic_issue_order_policy": "lexicographic_over_issue_code_target_path_hunk_index_policy_source"
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v34d_retry_context_evidence@1",
    "canonical_closeout_evidence_required": true,
    "verification_passed_policy": "true_means_feeder_generation_guards_and_closeout_validation_passed_not_policy_validation_packaging_validation_or_model_success",
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "feeder_entrypoint",
      "shared_feeder_engine_used",
      "shared_feeder_engine_identifier",
      "retry_context_feeder_result_path",
      "retry_context_feeder_result_hash",
      "sanitization_profile_path",
      "sanitization_profile_hash",
      "source_rejection_diagnostic_schema",
      "policy_source_closed_inherited_surface",
      "runner_result_semantic_input_forbidden",
      "advisory_only_non_authoritative",
      "automatic_retry_dispatch_forbidden",
      "downstream_diagnostic_aggregation_forbidden",
      "policy_success_explicit_request_without_diagnostic_fails_closed",
      "raw_repo_file_content_forbidden",
      "duplicate_issue_tuples_forbidden",
      "excerpt_bounds_enforced",
      "overflow_policy",
      "missing_excerpt_source_policy",
      "total_output_bound_enforced",
      "control_marker_neutralization_enforced",
      "deterministic_issue_order_enforced",
      "verification_passed",
      "verification_passed_policy",
      "success_path_absence_without_request_allowed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v51",
      "notes"
    ]
  },
  "test_requirements": {
    "retry_context_feeder_result_deterministic_for_identical_inputs": true,
    "retry_context_feeder_result_emitted_from_runner_rejection_diagnostic": true,
    "retry_context_feeder_result_forbidden_without_rejection_diagnostic": true,
    "duplicate_issue_tuple_rejected": true,
    "policy_success_path_allows_absence_without_request": true,
    "explicit_request_without_rejection_diagnostic_fails_closed": true,
    "overflow_handling_deterministic": true,
    "missing_excerpt_source_policy_enforced": true,
    "policy_source_surface_closed_inherited": true,
    "raw_repo_file_content_forbidden": true,
    "control_marker_neutralization_enforced": true
  },
  "fail_closed_conditions": [
    "retry_context_generated_without_runner_rejection_diagnostic",
    "unsanitized_reflected_text_accepted",
    "raw_repo_file_content_included_in_retry_context",
    "downstream_component_rejection_diagnostic_used_as_v52_authority_input",
    "runner_result_semantic_content_used_as_feeder_authority",
    "duplicate_issue_tuple_emitted_by_feeder",
    "policy_source_expansion_beyond_frozen_runner_rejection_surface",
    "retry_context_sanitization_profile_missing",
    "retry_context_feeder_result_missing_after_valid_generation",
    "sanitization_profile_drift_accepted",
    "overflow_rule_drift_accepted",
    "explicit_retry_context_request_on_policy_success_path_without_rejection_diagnostic_not_rejected",
    "missing_excerpt_source_behavior_outside_frozen_typed_marker_policy_accepted",
    "non_authoritative_retry_context_treated_as_policy_or_verification_input",
    "automatic_retry_dispatch_released_in_v52"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## A1) Shared Canonical Retry-Context Feeder + Deterministic Sanitization-Profile Baseline (`V34-D`)

### Goal

Make `V34-D` real as a shared canonical advisory retry-context feeder over structured runner
rejection diagnostics rather than ad hoc prompt assembly.

### Scope

- extract or define a shared canonical retry-context feeder over the current runner rejection
  diagnostic surface;
- emit deterministic `retry_context_feeder_result@1` from canonical rejection diagnostics
  plus canonical candidate-plan references;
- emit deterministic `retry_context_sanitization_profile@1` with frozen bounds and escaping
  rules;
- freeze retry-context content to bounded references plus sanitized excerpts already present
  in canonical artifacts.

### Locks

- v52 must not widen feeder scope beyond the current runner rejection-diagnostic surface.
- feeder input authority must derive only from:
  - canonical `candidate_change_plan_rejection_diagnostic@1`,
  - canonical `candidate_change_plan@1`,
  - taskpack/candidate hashes and canonical manifest references already present in artifact
    surfaces.
- verifier and packaging rejection-diagnostic families are out of scope as authority inputs
  in this arc.
- `policy_source` remains a closed inherited surface from the frozen runner
  rejection-diagnostic contract and is not expandable in v52.
- `taskpack_runner_result@1` is preserved here as a binding and continuity sibling artifact
  only; it is not a semantic input to retry-context content generation.
- raw repository file-content inclusion is forbidden.
- reflected diagnostic text is untrusted input and must be sanitized under the frozen
  profile before any model-facing serialization.
- if generation is explicitly requested on a policy-success path without a runner rejection
  diagnostic, generation fails closed rather than emitting an empty feeder artifact.
- duplicate `(issue_code, target_path, hunk_index, policy_source)` tuples in feeder input are
  invalid after `target_path` normalization to repo-relative posix form and fail closed;
  they are not silently deduplicated.
- overflow beyond any frozen excerpt or total-output bound truncates deterministically under
  the frozen sanitization profile; overflow handling must not vary by caller.
- if a referenced candidate-plan excerpt cannot be resolved from canonical artifacts,
  `sanitized_candidate_plan_excerpt` must resolve to a deterministic null typed excerpt and
  must not trigger repo fallback reads.
- `retry_context_feeder_result@1` is advisory-only and non-authoritative for policy,
  verification, and packaging decisions.
- automatic retry prompt dispatch or model invocation is forbidden in this arc.
- on policy-success paths, absence of `retry_context_feeder_result@1` is the expected
  deterministic behavior unless generation was explicitly requested.
- no new stop-gate metric keys are authorized in this path unless explicitly released in the
  corresponding lock doc.

### Acceptance

- identical inputs produce deterministic `retry_context_feeder_result@1` bytes across reruns;
- identical inputs produce deterministic `retry_context_sanitization_profile@1` bytes across
  reruns;
- sanitized feeder payload excludes disallowed raw control markers under the frozen profile;
- total serialized feeder output remains bounded by the frozen sanitization profile;
- on policy-success paths, no feeder artifact is required unless generation was explicitly
  requested;
- if generation is explicitly requested without a runner rejection diagnostic, generation
  fails closed;
- unresolvable candidate-plan excerpts resolve deterministically to the frozen typed null
  excerpt shape without repo fallback;
- generation fails closed when invoked without a runner rejection diagnostic input.

## A2) Canonical Retry-Context Evidence + Guard Suite and Advisory-Only Integration (`V34-D`)

### Goal

Make the retry-context feeder auditable and enforce that it remains advisory-only while
closing the evidence gap for this lane.

### Scope

- add canonical closeout evidence for the v34d feeder lane;
- add deterministic guard coverage for:
  - feeder determinism,
  - no generation without runner rejection diagnostics,
  - raw repo-content exclusion,
  - control-marker neutralization,
  - advisory-only non-authoritative posture;
- integrate the feeder lane into canonical closeout evidence without making downstream
  verifier or packaging behavior depend on it.

### Locks

- retry-context evidence is closeout-authoritative only via its deterministic artifact hash
  bindings.
- v52 must not make verifier, packaging, or stop-gate pass/fail decisions depend on retry
  context content.
- closeout proof must distinguish between:
  - `retry_context_feeder_result@1`,
  - `retry_context_sanitization_profile@1`,
  - docs-side `v34d_retry_context_evidence@1`.
- advisory-only posture must be encoded in both tests and closeout evidence.
- runtime-observability evidence remains required and informational-only.

### Acceptance

- closeout path emits the required `v34d_retry_context_evidence@1` block;
- guard suites prove retry-context generation remains deterministic and advisory-only;
- no downstream verifier/package authority path consumes retry-context output in this arc;
- deterministic guard suites remain green under frozen environment requirements.

## Stop-Gate Impact (v52)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v52 closeout must include runtime-observability comparison row against v51 baseline.
- v52 closeout must include metric-key continuity assertion against v51 baseline.
- v52 closeout must include retry-context evidence block:
  - block schema is docs-only `v34d_retry_context_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a deterministic
    JSON evidence input artifact and included in the canonical closeout path,
  - required keys are:
    - `schema`
    - `contract_source`
    - `feeder_entrypoint`
    - `shared_feeder_engine_used`
    - `shared_feeder_engine_identifier`
    - `retry_context_feeder_result_path`
    - `retry_context_feeder_result_hash`
    - `sanitization_profile_path`
    - `sanitization_profile_hash`
    - `source_rejection_diagnostic_schema`
    - `policy_source_closed_inherited_surface`
    - `runner_result_semantic_input_forbidden`
    - `advisory_only_non_authoritative`
    - `automatic_retry_dispatch_forbidden`
    - `downstream_diagnostic_aggregation_forbidden`
    - `policy_success_explicit_request_without_diagnostic_fails_closed`
    - `raw_repo_file_content_forbidden`
    - `duplicate_issue_tuples_forbidden`
    - `excerpt_bounds_enforced`
    - `overflow_policy`
    - `missing_excerpt_source_policy`
    - `total_output_bound_enforced`
    - `control_marker_neutralization_enforced`
    - `deterministic_issue_order_enforced`
    - `verification_passed`
    - `verification_passed_policy`
    - `success_path_absence_without_request_allowed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v51`
    - `notes`

## Error/Exit Policy (v52)

- No new URM runtime error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v52 introduces new retry-context feeder diagnostics, they must be constrained to an
  authoritative `AHK52xx` registry and remain error-only with non-zero exit behavior.
- If v52 introduces new feeder diagnostics, deterministic issue ordering must sort by
  `(issue_code, target_path, hunk_index, policy_source)`.
- for feeder exact-input subjects, `target_path` serializes in repo-relative posix form and
  `hunk_index` remains integer-typed from the frozen runner rejection-diagnostic surface.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v34d retry-context feeder baseline`
2. `tests: add v34d retry-context evidence and advisory guards`

## Intermediate Preconditions (for v52 start)

1. v51 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v51 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS51.md`
3. Existing v51 policy-recompute baseline remains available at v52 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/policy_recompute.py`
   - `artifacts/agent_harness/v51/evidence_inputs/v34c_policy_recompute_evidence_v51.json`
4. Existing runner/verifier/closeout evidence surfaces remain available at v52 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
5. Existing v51 closeout artifacts remain available at v52 start:
   - `artifacts/quality_dashboard_v51_closeout.json`
   - `artifacts/stop_gate/metrics_v51_closeout.json`
   - `artifacts/stop_gate/report_v51_closeout.md`
   - `artifacts/agent_harness/v51/evidence_inputs/runtime_observability_comparison_v51.json`
   - `artifacts/agent_harness/v51/evidence_inputs/metric_key_continuity_assertion_v51.json`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. No additional `L2` boundary release beyond v51 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `A1` and `A2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V34-D` retry-context feeder baseline remains advisory-only and does not widen into
  automatic retry dispatch or downstream authority consumption.
- v52 closeout evidence includes runtime-observability comparison row against v51 baseline,
  metric-key continuity assertion against v51 baseline, and
  `v34d_retry_context_evidence@1`.
- `retry_context_feeder_result@1` and `retry_context_sanitization_profile@1` are
  deterministic under identical inputs.
- raw repo file content remains excluded from the feeder artifact.
- v36-v51 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
