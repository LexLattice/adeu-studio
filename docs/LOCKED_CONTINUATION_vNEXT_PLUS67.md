# Locked Continuation vNext+67 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS66.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS66.md`
- `docs/ASSESSMENT_vNEXT_PLUS66_EDGES.md`
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

- `vNext+66` (`V37-A`, `A1`/`A2`) is merged on `main` with green CI checks.
- `vNext+66` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS66.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS66_EDGES.md` marks `V37-A` as closed and restores
  eligibility for the next bounded recursive-compilation path.
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` remains the higher-order methodology note
  distinguishing:
  - soft operational influence in the active builder loop;
  - accepted compilation into explicit repo governance.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md` now names `V37-B` as the next default candidate
  after `V37-A` closure.
- current repo reality after `v66` is narrower than a runnable recursive-compilation
  loop:
  - canonical `meta_testing_intent_packet@1`, canonical `meta_module_catalog@1`, one
    accepted bound reference-instance pair, and canonical
    `v37a_meta_intent_module_catalog_evidence@1` now exist on `main`;
  - hard checkpoint executor surfaces already exist on `main` and are typed in the
    released module catalog, but no released sequence contract yet freezes how those
    modules compose under explicit step law;
  - no released `meta_loop_sequence_contract@1` or `meta_loop_run_trace@1` exists on
    `main`;
  - no released `meta_loop_checkpoint_result_manifest@1`, executable reference loop,
    drift-diagnostics/conformance lane, or control-update export exists on `main`.
- `vNext+67` therefore selects one thin `V37-B` baseline slice only:
  - canonical `meta_loop_sequence_contract@1`,
  - canonical `meta_loop_run_trace@1`,
  - one accepted bound sequence/trace reference pair for the same bounded
    `arc_bundle_recursive_compilation_loop`,
  - frozen step ids, phase boundaries, branch conditions, checkpoint bindings, operator
    gates, reasoning-step dispatch binding, and explicit `operational_influence` versus
    `accepted_compilation` markers,
  - closeout evidence plus determinism/guard coverage,
  - no executable reference loop, checkpoint-result manifest, drift diagnostics,
    conformance aggregation, or control-update export in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS66.md` remain authoritative for baseline
  continuity.
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` remains methodology above arcs:
  it informs this arc but does not itself authorize runtime behavior, lock changes, or
  control updates.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v67,
  - v67 keyset must be exactly equal to v66 keyset,
  - baseline derived cardinality at v67 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v67 is explicit and narrow:
  - this arc authorizes one `L1` recursive-compilation sequence/trace lane only,
  - no `L0` runnable reference loop release is authorized in this arc,
  - no `L2` broad autonomous coordination or repo-wide benchmark lane is authorized in
    this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35`, `V36`, and `V37-A` baseline,
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
- `V37-B` release-shape lock for v67 is frozen:
  - this arc is a typed sequence-contract and run-trace baseline only,
  - the arc must define `meta_loop_sequence_contract@1` and `meta_loop_run_trace@1`
    plus one accepted bound reference pair for the same bounded
    `arc_bundle_recursive_compilation_loop`,
  - the arc must preserve the frozen `V37-A` binding tuple:
    `reference_loop_family`, `reference_instance_id`, `intent_packet_id`,
  - the arc must freeze stable step ids, ordered phase boundaries, branch conditions,
    failure edges, checkpoint bindings, operator-gate surfaces, and per-step reasoning
    dispatch binding,
  - any hard checkpoint/evidence-gate/operator-gate step must bind to the exact executor
    ref already frozen in the accepted `V37-A` module catalog rather than to a generic
    capability label,
  - any reasoning step that asserts sufficiency, closure, pass/fail expectation, or
    drift classification must bind to an explicit downstream checkpoint module, evidence
    gate, or operator gate,
  - the arc must make `operational_influence` and `accepted_compilation` explicit and
    distinct in the accepted trace layer,
  - no runnable loop execution, checkpoint-result manifest, drift diagnostics,
    conformance report, or control-update export is authorized in this arc,
  - no hidden prompt-only step order, hidden branch logic, or undocumented retry edge is
    authorized in this arc,
  - no new stop-gate metric keys are authorized in this path unless explicitly released
    in the corresponding lock doc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `B1` Sequence contract + run trace baseline (`V37-B`)
2. `B2` Sequence/trace evidence + determinism/guard suite (`V37-B`)

Out-of-scope note:

- any `V37-C` runnable reference-loop implementation in this arc,
- any `meta_loop_checkpoint_result_manifest@1` release in this arc,
- any `V37-D` drift-diagnostics or conformance lane in this arc,
- any `V37-E` control-update export in this arc,
- any generalized autonomous self-improvement engine in this arc,
- any prompt-only self-testing without explicit sequence/trace law in this arc,
- any hidden prompt choreography as operative step order in this arc,
- any automatic repo mutation or automatic validator/policy rollout in this arc,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v67)

- `V37-C` executable reference meta-loop
- `V37-D` drift diagnostics + conformance baseline
- `V37-E` advisory control-update export
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold

## V66 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS66.md",
  "target": "V37-B-baseline",
  "required_continuity_guards": [
    "V37_A_A1_META_INTENT_BASELINE_GREEN",
    "V37_A_A2_META_INTENT_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v66_v37a_closed_meta_testing_substrate_remains_frozen_while_v37b_sequence_contract_and_run_trace_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v67.
- this narrowed machine-checkable consumption block is v66-local only and does not
  weaken the global continuity locks declared above; v14-v66 baseline continuity remains
  in force for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V37-B Sequence Contract and Run Trace Contract (Machine-Checkable)

```json
{
  "schema": "v37b_sequence_trace_contract@1",
  "target_arc": "vNext+67",
  "target_path": "V37-B",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v11.md",
    "recursive_compilation_note": "docs/DRAFT_RECURSIVE_COMPILATION_v0.md",
    "practical_harness_flow": "docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md",
    "codex_integration_lock": "docs/LOCKED_URM_CODEX_INTEGRATION_v0.md",
    "externalized_reasoning_kernel": "docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md",
    "v66_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS66.md",
    "v66_edge_assessment": "docs/ASSESSMENT_vNEXT_PLUS66_EDGES.md",
    "v66_meta_testing_intent_packet_reference": "apps/api/fixtures/meta_testing/vnext_plus66/meta_testing_intent_packet_arc_closeout_v65_reference.json",
    "v66_meta_module_catalog_reference": "apps/api/fixtures/meta_testing/vnext_plus66/meta_module_catalog_arc_closeout_v65_reference.json",
    "v66_v37a_evidence": "artifacts/agent_harness/v66/evidence_inputs/v37a_meta_intent_module_catalog_evidence_v66.json",
    "bounded_reference_loop_family": "arc_bundle_recursive_compilation_loop",
    "first_reference_loop_anchor": {
      "shape": "arc_closeout_bundle_instance",
      "reference_arc": 65,
      "reference_phase": "closeout"
    },
    "stop_gate_schema_family": "stop_gate_metrics@1"
  },
  "sequence_trace_requirements": {
    "foundation_status": "deterministic_sequence_and_trace_law_over_released_v37a_substrate",
    "meta_loop_sequence_contract_schema_required": true,
    "meta_loop_run_trace_schema_required": true,
    "accepted_reference_sequence_trace_pair_required": true,
    "accepted_reference_sequence_trace_pair_must_bind_v37a_reference_tuple": true,
    "reference_loop_family": "arc_bundle_recursive_compilation_loop",
    "required_binding_fields": [
      "reference_loop_family",
      "reference_instance_id",
      "intent_packet_id"
    ],
    "required_sequence_fields": [
      "step_id",
      "module_id",
      "phase_boundary",
      "required_inputs",
      "expected_outputs",
      "checkpoint_binding_id",
      "branch_condition_id",
      "failure_edge_ids",
      "operator_gate_id",
      "dispatch_provenance_ref"
    ],
    "required_run_trace_fields": [
      "planned_step_id",
      "actual_module_id",
      "consumed_inputs",
      "emitted_outputs",
      "observed_checkpoint_result_refs",
      "step_status",
      "operational_influence_occurred",
      "accepted_compilation_occurred"
    ],
    "reasoning_step_dispatch_binding_required": true,
    "hard_step_executor_binding_must_resolve_via_v37a_catalog": true,
    "reasoning_claims_must_bind_downstream_gate": true,
    "operator_gate_surface_explicit": true,
    "operational_influence_threshold_explicit": true,
    "accepted_compilation_threshold_explicit": true,
    "no_hidden_prompt_only_step_order": true,
    "no_hidden_branch_logic": true,
    "no_model_prose_truth_substitution": true
  },
  "test_requirements": [
    "canonical_json_hashing_deterministic",
    "v37a_reference_tuple_consumed_without_drift",
    "sequence_trace_reference_pair_binding_verified",
    "step_ids_unique_and_phase_boundaries_frozen",
    "checkpoint_bindings_resolve_via_v37a_catalog",
    "reasoning_dispatch_bindings_resolve_per_step",
    "operator_gate_surfaces_explicit",
    "operational_influence_distinct_from_accepted_compilation",
    "hidden_branch_logic_rejected",
    "v37b_scope_boundary_preserved",
    "metric_key_exact_set_equal_v66"
  ],
  "fail_closed_conditions": [
    "sequence_contract_missing_required_fields",
    "run_trace_missing_required_fields",
    "reference_tuple_drift_from_v37a",
    "step_missing_resolvable_module_binding",
    "reasoning_step_missing_dispatch_binding",
    "checkpoint_or_operator_step_missing_exact_v37a_executor_binding",
    "hidden_branch_logic_or_undocumented_retry_edge_introduced",
    "reasoning_claim_without_downstream_gate_binding",
    "operational_influence_accepted_compilation_collapse",
    "out_of_scope_runnable_loop_or_diagnostics_surfaces_introduced"
  ],
  "closeout_required_block_keys": [
    "metric_key_exact_set_equal_v66",
    "v37a_reference_tuple_consumed_without_drift",
    "sequence_trace_reference_pair_binding_verified",
    "step_order_and_phase_boundary_verified",
    "checkpoint_bindings_resolved_via_v37a_catalog",
    "operator_gate_surfaces_verified",
    "reasoning_claims_bound_to_downstream_gates",
    "operational_influence_distinct_from_accepted_compilation",
    "v37b_scope_boundary_preserved",
    "verification_passed"
  ],
  "exit_criteria": [
    "B1_and_B2_merged_with_green_ci",
    "meta_loop_sequence_contract_and_meta_loop_run_trace_exist_as_canonical_hash_bound_artifacts",
    "one_bound_reference_sequence_trace_pair_exists_for_arc_bundle_recursive_compilation_loop",
    "sequence_trace_pair_binds_exactly_to_released_v37a_reference_tuple",
    "step_order_phase_boundaries_branch_conditions_and_operator_gates_are_frozen",
    "hard_step_executor_bindings_resolve_only_through_released_v37a_catalog",
    "operational_influence_and_accepted_compilation_remain_explicitly_distinct",
    "stop_gate_schema_family_and_metric_keyset_remain_unchanged",
    "no_runnable_loop_diagnostics_conformance_or_control_update_export_is_released"
  ]
}
```

## Release Shape (Narrative)

- `vNext+67` is the first bounded recursive-compilation sequence/trace arc only.
- `B1` should freeze typed step law and typed observed trace for one bounded
  `arc_bundle_recursive_compilation_loop`.
- `B2` should prove determinism, hash binding, exact cross-artifact binding back to the
  released `V37-A` tuple, checkpoint-binding resolution, reasoning-claim-to-gate
  binding, operator-gate explicitness, and stop-gate continuity while rejecting hidden
  branch logic or threshold collapse.
- the arc must consume the released `V37-A` intent/module substrate and current hard
  checkpoint executor surfaces as authoritative downstream bindings without pretending
  the loop is already executed end-to-end;
- the arc must keep the distinction between:
  - operational influence in the active builder loop;
  - accepted compilation into repo governance;
  explicit rather than implicit.

## Recommendation

- proceed with `V37-B` only in `vNext+67`;
- keep the first implementation lane narrow:
  explicit sequence law plus trace law first,
  runnable execution later;
- preserve the recursive-compilation methodology note as a higher-order input rather than
  collapsing it into immediate runtime authority.
