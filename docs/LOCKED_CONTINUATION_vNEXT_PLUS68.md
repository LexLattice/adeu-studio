# Locked Continuation vNext+68 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS67.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS67.md`
- `docs/ASSESSMENT_vNEXT_PLUS67_EDGES.md`
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/LOCKED_URM_CODEX_INTEGRATION_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 17, 2026 UTC).

## Decision Basis

- `vNext+67` (`V37-B`, `B1`/`B2`) is merged on `main` with green CI checks.
- `vNext+67` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS67.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS67_EDGES.md` marks `V37-B` as closed and restores
  eligibility for the next bounded recursive-compilation path.
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` remains the higher-order methodology note
  distinguishing:
  - soft operational influence in the active builder loop;
  - accepted compilation into explicit repo governance.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md` now names `V37-C` as the next default candidate
  after `V37-B` closure.
- current repo reality after `v67` is narrower than typed recursive-compilation
  diagnostics or advisory control export:
  - canonical `meta_testing_intent_packet@1`, canonical `meta_module_catalog@1`, one
    accepted bound reference-instance pair, and canonical
    `v37a_meta_intent_module_catalog_evidence@1` now exist on `main`;
  - canonical `meta_loop_sequence_contract@1`, canonical `meta_loop_run_trace@1`, one
    accepted bound sequence/trace reference pair, and canonical
    `v37b_sequence_trace_evidence@1` now also exist on `main`;
  - hard checkpoint executor surfaces already exist on `main` and are typed in the
    released module catalog and sequence contract, but no released executable reference
    loop yet binds those modules into one actual governed run;
  - no released `meta_loop_checkpoint_result_manifest@1` exists on `main`;
  - no released `meta_loop_drift_diagnostics@1`,
    `meta_loop_conformance_report@1`, `meta_control_update_candidate@1`, or
    `meta_control_update_manifest@1` exists on `main`.
- `vNext+68` therefore selects one thin `V37-C` baseline slice only:
  - one bounded executable `arc_bundle_recursive_compilation_loop` over the released
    `V37-A` and `V37-B` substrate;
  - canonical `meta_loop_checkpoint_result_manifest@1`;
  - one accepted executable reference run anchored to one concrete existing native
    terrain:
    a `v65`-style closeout bundle instance;
  - normalized capture of hard checkpoint outputs, emitted artifact refs/hashes, and
    executed-run trace state under the shared binding tuple;
  - closeout evidence plus determinism/guard coverage;
  - no drift diagnostics/conformance lane and no control-update export in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS67.md` remain authoritative for baseline
  continuity.
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` remains methodology above arcs:
  it informs this arc but does not itself authorize runtime behavior, lock changes, or
  control updates.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v68,
  - v68 keyset must be exactly equal to v67 keyset,
  - baseline derived cardinality at v68 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v68 is explicit and narrow:
  - this arc authorizes one `L0` bounded executable reference-loop lane only,
  - no `L1` diagnostics/conformance release is authorized in this arc,
  - no `L2` broad autonomous coordination or repo-wide benchmark lane is authorized in
    this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35`, `V36`, `V37-A`, and `V37-B` baseline,
  - no autonomous repo mutation, branch management, PR submission, or policy promotion
    is authorized in this arc.
- `V35-A` through `V35-E` runtime/state/delegation/visibility/topology/enforcement
  surfaces remain frozen prerequisites and are not redefined by this arc.
- `V36-A` through `V36-E` UX-governance/compiler-export surfaces remain frozen
  prerequisites and are not redefined by this arc.
- `V37-A` release-shape lock for v66 is now frozen prerequisite substrate:
  - `meta_testing_intent_packet@1`, `meta_module_catalog@1`, the accepted bound
    reference-instance pair, and canonical
    `v37a_meta_intent_module_catalog_evidence@1` remain authoritative inputs and are not
    redefined by this arc.
- `V37-B` release-shape lock for v67 is now frozen prerequisite substrate:
  - `meta_loop_sequence_contract@1`, `meta_loop_run_trace@1`, the accepted bound
    sequence/trace reference pair, and canonical `v37b_sequence_trace_evidence@1`
    remain authoritative inputs and are not redefined by this arc.
- `V37-C` release-shape lock for v68 is frozen:
  - this arc is one bounded executable reference-loop baseline only,
  - the arc must define `meta_loop_checkpoint_result_manifest@1` and one accepted
    executable reference run for the same bounded
    `arc_bundle_recursive_compilation_loop`,
  - the arc must preserve the frozen shared binding tuple across consumed and emitted
    artifacts:
    `reference_loop_family`, `reference_instance_id`, `intent_packet_id`,
  - the arc must bind exactly back to the released `V37-A` and `V37-B` reference pairs
    rather than introducing a new reference terrain,
  - the first executable reference run must remain anchored to one concrete
    `v65`-style closeout bundle instance rather than to a family abstraction only,
  - the first executable reference run must declare its executed hard-checkpoint subset
    intentionally rather than by omission;
    released hard-checkpoint capabilities not executed in the first run should be named
    explicitly as deferred for later family expansion,
  - the arc must execute reasoning modules and hard checkpoint modules only in accepted
    sequence-contract order;
    no hidden prompt-only step order, hidden branch logic, or undocumented retry
    behavior is authorized in this arc,
  - the arc must deliberately freeze the authoritative stop-gate executor binding for
    the first family rather than leaving adjacent repo surfaces interchangeable under the
    capability label;
    `apps/api/scripts/build_stop_gate_metrics.py` is the authoritative stop-gate
    executor surface for this path,
  - any parameter flowing from a reasoning step into a checkpoint executor binding must
    pass typed validation before invocation;
    validated argument vectors are authorized, raw shell interpolation is not,
  - the arc must normalize actual hard-checkpoint outputs into canonical
    `meta_loop_checkpoint_result_manifest@1`,
  - any attempted checkpoint step, including a failed checkpoint step, must still emit a
    normalized result-manifest record;
    missing manifest rows may not be used to imply that an attempted step never ran,
  - the accepted executed run must use explicit executed-run trace semantics rather than
    the `reference_not_executed` trace mode frozen in v67;
    checkpoint-result refs must point to actual emitted or preaccepted artifact refs,
  - the accepted executed run must emit a distinct executed-trace artifact rather than a
    mutation or reinterpretation of the frozen `V37-B` reference trace,
  - realized control-flow provenance must be explicit in the executed artifacts:
    actual branch outcomes should be recorded whenever a branch condition is evaluated,
    and actual retry outcomes should be recorded whenever a retry occurs,
  - observed pass/fail or gate-relevant truth in the run must be derived from actual
    hard checkpoint outputs and bound artifact refs/hashes rather than from reasoning
    prose,
  - no `V37-D` diagnostics/conformance surface or `V37-E` control-update export is
    authorized in this arc,
  - no new stop-gate metric keys are authorized in this path unless explicitly released
    in the corresponding lock doc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `C1` Executable reference loop + checkpoint-result-manifest baseline (`V37-C`)
2. `C2` Executable reference-loop evidence + determinism/guard suite (`V37-C`)

Out-of-scope note:

- any `V37-D` drift-diagnostics or conformance lane in this arc,
- any `V37-E` control-update export in this arc,
- any generalized autonomous self-improvement engine in this arc,
- any prompt-only self-testing without actual checkpoint execution in this arc,
- any hidden prompt choreography as operative execution law in this arc,
- any automatic repo mutation or automatic validator/policy rollout in this arc,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v68)

- `V37-D` drift diagnostics + conformance baseline
- `V37-E` advisory control-update export
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold

## V67 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS67.md",
  "target": "V37-C-baseline",
  "required_continuity_guards": [
    "V37_B_B1_SEQUENCE_TRACE_BASELINE_GREEN",
    "V37_B_B2_SEQUENCE_TRACE_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v67_v37b_closed_sequence_and_reference_trace_substrate_remains_frozen_while_v37c_executable_reference_loop_and_checkpoint_result_manifest_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v68.
- this narrowed machine-checkable consumption block is v67-local only and does not
  weaken the global continuity locks declared above; v14-v67 baseline continuity remains
  in force for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V37-C Executable Reference Loop Contract (Machine-Checkable)

```json
{
  "schema": "v37c_executable_reference_loop_contract@1",
  "target_arc": "vNext+68",
  "target_path": "V37-C",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v11.md",
    "recursive_compilation_note": "docs/DRAFT_RECURSIVE_COMPILATION_v0.md",
    "practical_harness_flow": "docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md",
    "codex_integration_lock": "docs/LOCKED_URM_CODEX_INTEGRATION_v0.md",
    "externalized_reasoning_kernel": "docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md",
    "v67_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS67.md",
    "v67_edge_assessment": "docs/ASSESSMENT_vNEXT_PLUS67_EDGES.md",
    "v66_meta_testing_intent_packet_reference": "apps/api/fixtures/meta_testing/vnext_plus66/meta_testing_intent_packet_arc_closeout_v65_reference.json",
    "v66_meta_module_catalog_reference": "apps/api/fixtures/meta_testing/vnext_plus66/meta_module_catalog_arc_closeout_v65_reference.json",
    "v67_meta_loop_sequence_contract_reference": "apps/api/fixtures/meta_testing/vnext_plus67/meta_loop_sequence_contract_arc_closeout_v65_reference.json",
    "v67_meta_loop_run_trace_reference": "apps/api/fixtures/meta_testing/vnext_plus67/meta_loop_run_trace_arc_closeout_v65_reference.json",
    "v66_v37a_evidence": "artifacts/agent_harness/v66/evidence_inputs/v37a_meta_intent_module_catalog_evidence_v66.json",
    "v67_v37b_evidence": "artifacts/agent_harness/v67/evidence_inputs/v37b_sequence_trace_evidence_v67.json",
    "bounded_reference_loop_family": "arc_bundle_recursive_compilation_loop",
    "first_reference_loop_anchor": {
      "shape": "arc_closeout_bundle_instance",
      "reference_arc": 65,
      "reference_phase": "closeout"
    },
    "stop_gate_schema_family": "stop_gate_metrics@1",
    "authoritative_stop_gate_executor": "apps/api/scripts/build_stop_gate_metrics.py"
  },
  "executable_reference_loop_requirements": {
    "foundation_status": "bounded_executable_reference_loop_over_released_v37a_and_v37b_substrate",
    "meta_loop_checkpoint_result_manifest_schema_required": true,
    "accepted_executable_reference_run_required": true,
    "accepted_executable_reference_run_must_bind_v37a_and_v37b_reference_tuple": true,
    "reference_loop_family": "arc_bundle_recursive_compilation_loop",
    "required_binding_fields": [
      "reference_loop_family",
      "reference_instance_id",
      "intent_packet_id"
    ],
    "first_reference_loop_anchor": {
      "shape": "arc_closeout_bundle_instance",
      "reference_arc": 65,
      "reference_phase": "closeout"
    },
    "required_executed_checkpoint_capabilities": [
      "bundle_lint",
      "quality_dashboard_build",
      "stop_gate_metrics_build",
      "instruction_policy_validation",
      "committed_event_stream_validation"
    ],
    "executed_capability_subset_is_intentional": true,
    "non_executed_released_capabilities_for_first_run": [
      "artifact_consistency_lint",
      "semantic_closeout_lint"
    ],
    "checkpoint_executor_bindings_must_resolve_via_v37a_catalog": true,
    "sequence_contract_order_must_drive_execution": true,
    "reasoning_dispatch_provenance_must_match_v37b_contract": true,
    "typed_argument_validation_required_before_checkpoint_invocation": true,
    "raw_shell_interpolation_for_soft_originated_inputs_rejected": true,
    "checkpoint_result_manifest_must_normalize_actual_outputs": true,
    "checkpoint_result_manifest_rows_required_for_attempted_failed_checkpoints": true,
    "executed_run_trace_artifact_required": true,
    "executed_run_trace_must_be_distinct_from_v67_reference_trace": true,
    "executed_run_trace_mode_required_value": "executed_reference_run",
    "actual_checkpoint_result_refs_required_for_executed_steps": true,
    "actual_branch_outcome_refs_required_when_branch_condition_present": true,
    "actual_retry_outcome_refs_required_when_retry_occurs": true,
    "output_artifact_refs_and_hashes_required": true,
    "reasoning_vs_checkpoint_truth_boundary_preserved": true,
    "make_arc_closeout_check_is_one_checkpoint_binding_not_monolithic_loop": true,
    "no_hidden_prompt_only_execution_order": true,
    "no_hidden_branch_logic": true,
    "no_undocumented_retry_behavior": true
  },
  "test_requirements": [
    "canonical_json_hashing_deterministic",
    "v37a_reference_tuple_consumed_without_drift",
    "v37b_reference_tuple_consumed_without_drift",
    "executed_reference_run_emitted",
    "checkpoint_result_manifest_emitted_and_hash_bound",
    "executed_run_trace_artifact_distinct_from_v67_reference_trace",
    "executed_run_trace_mode_verified",
    "hard_checkpoint_results_captured_from_actual_executors",
    "executed_capability_subset_declared_intentionally",
    "authoritative_stop_gate_executor_binding_verified",
    "actual_branch_and_retry_outcomes_verified",
    "failed_checkpoint_attempts_still_emit_normalized_result_rows",
    "output_artifact_refs_and_hashes_verified",
    "reasoning_vs_checkpoint_truth_boundary_preserved",
    "executed_step_order_matches_v37b_contract",
    "v37c_scope_boundary_preserved",
    "metric_key_exact_set_equal_v67"
  ],
  "fail_closed_conditions": [
    "checkpoint_result_manifest_missing_or_invalid",
    "reference_tuple_drift_from_v37a_or_v37b",
    "executed_run_claims_truth_without_actual_checkpoint_output",
    "checkpoint_step_executed_without_exact_catalog_binding",
    "executed_capability_subset_implicit_or_undeclared",
    "stop_gate_executor_binding_not_frozen_to_authoritative_surface",
    "soft_originated_parameter_reaches_executor_without_typed_validation",
    "hidden_execution_order_branch_or_retry_logic_introduced",
    "executed_branch_condition_without_outcome_record",
    "retried_step_without_retry_outcome_record",
    "executed_checkpoint_without_normalized_result_record",
    "output_artifact_ref_or_hash_missing_for_executed_checkpoint",
    "diagnostics_conformance_or_control_update_surface_introduced_in_v37c",
    "metric_key_regression_from_v67"
  ],
  "closeout_required_block_keys": [
    "metric_key_exact_set_equal_v67",
    "v37a_reference_tuple_consumed_without_drift",
    "v37b_reference_tuple_consumed_without_drift",
    "executed_reference_run_emitted",
    "checkpoint_result_manifest_emitted_and_hash_bound",
    "executed_run_trace_artifact_distinct_from_v67_reference_trace",
    "executed_run_trace_mode_verified",
    "hard_checkpoint_results_captured_from_actual_executors",
    "executed_capability_subset_declared_intentionally",
    "authoritative_stop_gate_executor_binding_verified",
    "actual_branch_and_retry_outcomes_verified",
    "failed_checkpoint_attempts_still_emit_normalized_result_rows",
    "output_artifact_refs_and_hashes_verified",
    "reasoning_vs_checkpoint_truth_boundary_preserved",
    "v37c_scope_boundary_preserved",
    "verification_passed"
  ],
  "exit_criteria": [
    "C1_and_C2_merged_with_green_ci",
    "meta_loop_checkpoint_result_manifest_exists_as_canonical_hash_bound_artifact",
    "one_bound_executable_reference_run_exists_for_arc_bundle_recursive_compilation_loop",
    "executed_reference_run_binds_exactly_to_released_v37a_and_v37b_reference_pairs",
    "hard_checkpoint_outputs_are_captured_from_actual_executors_under_shared_binding_tuple",
    "executed_capability_subset_is_explicit_and_intentional_for_first_family_run",
    "authoritative_stop_gate_executor_is_frozen_and_verified",
    "executed_trace_is_distinct_from_v67_reference_trace_and_records_realized_control_flow",
    "failed_checkpoint_attempts_still_emit_normalized_result_manifest_rows",
    "observed_gate_truth_is_derived_from_actual_checkpoint_outputs_not_reasoning_prose",
    "stop_gate_schema_family_and_metric_keyset_remain_unchanged",
    "no_diagnostics_conformance_or_control_update_export_is_released"
  ]
}
```

## Release Shape (Narrative)

- `vNext+68` is the first bounded executable recursive-compilation loop arc only.
- `C1` should execute one bounded reference loop on native repo terrain and normalize
  actual hard checkpoint outputs into canonical
  `meta_loop_checkpoint_result_manifest@1`.
- that first executed run should declare its bounded intentional hard-checkpoint subset
  explicitly rather than implying that the full released `V37-A` catalog is already in
  active execution scope.
- `C2` should prove determinism, hash binding, exact cross-artifact binding back to the
  released `V37-A` and `V37-B` pairs, actual executor capture, stop-gate continuity,
  distinct executed-trace emission, realized branch/retry outcome capture, manifest-row
  completeness for attempted failed checkpoints, and executable truth-boundary
  preservation while rejecting diagnostics/conformance or control-update bleed.
- the first accepted executable reference run should remain intentionally narrow:
  one `v65`-style closeout bundle instance under one explicit intent packet and one
  accepted module/sequence substrate, not a generalized autonomy stack.

## Acceptance Summary

- v68 is successful only if one bounded executable reference loop can be run end-to-end
  against an explicit intent packet under the released module catalog and released
  sequence contract;
- the accepted executable run must remain bound to one concrete existing
  arc-bundle closeout instance rather than to a family abstraction only;
- observed gate-relevant truth in the run must be derived from actual hard checkpoint
  outputs and accepted artifact refs/hashes rather than from reasoning prose;
- the emitted manifest and executed-run artifacts must be deterministic and sufficient
  for later typed drift diagnostics and conformance work without introducing those later
  surfaces in this arc.
