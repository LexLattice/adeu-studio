# Locked Continuation vNext+66 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS65.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS65.md`
- `docs/ASSESSMENT_vNEXT_PLUS65_EDGES.md`
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/LOCKED_URM_CODEX_INTEGRATION_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 15, 2026 UTC).

## Decision Basis

- `vNext+65` (`V36-E`, `E1`/`E2`) is merged on `main` with green CI checks.
- `vNext+65` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS65.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS65_EDGES.md` marks the `V36` family as closed and restores
  eligibility for a fresh post-`V36` family.
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` now records the higher-order methodology
  distinction between:
  - soft operational influence in the active builder loop;
  - accepted compilation into explicit repo governance.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md` now names `V37-A` as the next default candidate
  after `V36-E` closure.
- current repo reality is narrower than a full executable recursive-compilation family:
  - hard checkpoint executor surfaces already exist on `main`:
    docs-only arc validation, closeout consistency linting, semantic closeout linting,
    stop-gate metrics/report generation, quality dashboard generation,
    instruction-policy validation, and committed event-stream validation,
  - the repo already has docs-first planning/closeout workflow, committed artifact trees,
    deterministic hashing, and released runtime/UX/harness substrate through closed
    `V35` and `V36`,
  - no released `meta_testing_intent_packet@1` or `meta_module_catalog@1` exists on
    `main`,
  - no released bound reference pair exists for an
    `arc_bundle_recursive_compilation_loop`,
  - no released `meta_loop_sequence_contract@1`, `meta_loop_run_trace@1`,
    `meta_loop_drift_diagnostics@1`, `meta_loop_conformance_report@1`,
    `meta_control_update_candidate@1`, or `meta_control_update_manifest@1` exists on
    `main`,
  - no released typed module catalog binds soft reasoning modules and hard checkpoint
    modules into one accepted meta-loop ontology on `main`.
- `vNext+66` therefore selects one thin `V37-A` baseline slice only:
  - canonical `meta_testing_intent_packet@1`,
  - canonical `meta_module_catalog@1`,
  - one accepted bound reference-instance pair for one bounded
    `arc_bundle_recursive_compilation_loop`,
  - frozen module classes, binding tuple, checkpoint executor binding requirements,
    checkpoint parameter-safety rules, reasoning dispatch provenance requirements, and
    ADEU drift taxonomy,
  - closeout evidence plus determinism/guard coverage,
  - no runnable end-to-end meta-loop release, no sequence contract, no run trace, no
    drift diagnostics, no conformance aggregation, and no control-update export in this
    arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS65.md` remain authoritative for baseline
  continuity.
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` remains methodology above arcs:
  it informs this arc but does not itself authorize runtime behavior, lock changes, or
  control updates.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v66,
  - v66 keyset must be exactly equal to v65 keyset,
  - baseline derived cardinality at v66 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v66 is explicit and narrow:
  - this arc authorizes one `L1` recursive-compilation substrate lane only,
  - no `L0` runnable meta-loop release is authorized in this arc,
  - no `L2` broad autonomous coordination or repo-wide benchmark lane is authorized in
    this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35`/`V36` baseline,
  - no autonomous repo mutation, branch management, PR submission, or policy promotion
    is authorized in this arc.
- `V35-A` through `V35-E` runtime/state/delegation/visibility/topology/enforcement
  surfaces remain frozen prerequisites and are not redefined by this arc.
- `V36-A` through `V36-E` UX-governance/compiler-export surfaces remain frozen
  prerequisites and are not redefined by this arc.
- `V37-A` release-shape lock for v66 is frozen:
  - this arc is a typed meta intent and module-ontology baseline only,
  - the arc must define `meta_testing_intent_packet@1` and `meta_module_catalog@1` plus
    one accepted bound reference-instance pair for one bounded
    `arc_bundle_recursive_compilation_loop`,
  - the arc must freeze the first-family module classes:
    `reasoning_module`, `checkpoint_module`, `evidence_gate_module`,
    `operator_gate_module`,
  - the arc must freeze the first-family binding tuple:
    `reference_loop_family`, `reference_instance_id`, `intent_packet_id`,
  - the arc must require exact executor binding refs for checkpoint/evidence-gate/
    operator-gate modules and dispatch provenance refs for reasoning modules,
  - the arc must require executor parameter policies with typed slots and explicit
    prohibition on unchecked shell interpolation for soft-originated inputs,
  - the arc must freeze the first-family ADEU drift taxonomy:
    `ontology_drift`, `epistemic_drift`, `deontic_drift`, `utility_drift`,
  - reasoning modules may express hypotheses, comparisons, and repair candidates, but
    may not mint pass/fail, completion, or governance truth by prose alone,
  - no sequence contract, run trace, runnable loop execution, drift diagnostics,
    conformance report, or control-update export is authorized in this arc,
  - no hidden prompt-only module authority is authorized, and no implicit sequence law
    may be introduced in this arc,
  - no checkpoint capability may be treated as present unless named in the accepted
    module catalog,
  - no new stop-gate metric keys are authorized in this path unless explicitly released
    in the corresponding lock doc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `A1` Meta intent packet + module ontology baseline (`V37-A`)
2. `A2` Meta intent/module evidence + determinism/guard suite (`V37-A`)

Out-of-scope note:

- any `V37-B` sequence-contract or run-trace work in this arc,
- any `V37-C` runnable end-to-end reference loop in this arc,
- any `V37-D` drift-diagnostics or conformance lane in this arc,
- any `V37-E` control-update export in this arc,
- any generalized autonomous self-improvement engine in this arc,
- any prompt-only self-testing without explicit module ontology in this arc,
- any hidden prompt choreography as operative sequence law in this arc,
- any automatic repo mutation or automatic validator/policy rollout in this arc,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v66)

- `V37-B` sequence contract + run trace baseline
- `V37-C` executable reference meta-loop
- `V37-D` drift diagnostics + conformance baseline
- `V37-E` advisory control-update export
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold

## V65 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS65.md",
  "target": "V37-A-baseline",
  "required_continuity_guards": [
    "V36_E_E1_SURFACE_COMPILER_EXPORT_BASELINE_GREEN",
    "V36_E_E2_SURFACE_COMPILER_EXPORT_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v65_v36e_closed_surfaces_and_recursive_compilation_methodology_remain_frozen_while_v37a_meta_intent_and_module_ontology_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v66.
- this narrowed machine-checkable consumption block is v65-local only and does not
  weaken the global continuity locks declared above; v14-v65 baseline continuity remains
  in force for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V37-A Meta Intent and Module Ontology Contract (Machine-Checkable)

```json
{
  "schema": "v37a_meta_intent_module_catalog_contract@1",
  "target_arc": "vNext+66",
  "target_path": "V37-A",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v11.md",
    "recursive_compilation_note": "docs/DRAFT_RECURSIVE_COMPILATION_v0.md",
    "practical_harness_flow": "docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md",
    "codex_integration_lock": "docs/LOCKED_URM_CODEX_INTEGRATION_v0.md",
    "externalized_reasoning_kernel": "docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md",
    "v65_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS65.md",
    "v65_edge_assessment": "docs/ASSESSMENT_vNEXT_PLUS65_EDGES.md",
    "bounded_reference_loop_family": "arc_bundle_recursive_compilation_loop",
    "first_reference_loop_anchor": {
      "shape": "arc_closeout_bundle_instance",
      "reference_arc": 65,
      "reference_phase": "closeout"
    },
    "stop_gate_schema_family": "stop_gate_metrics@1"
  },
  "meta_intent_module_requirements": {
    "foundation_status": "deterministic_meta_intent_and_module_ontology_over_existing_repo_hard_checkpoint_surfaces",
    "meta_testing_intent_packet_schema_required": true,
    "meta_module_catalog_schema_required": true,
    "accepted_reference_instance_pair_required": true,
    "accepted_reference_instance_pair_must_bind_exact_authoritative_input_refs_and_hashes": true,
    "first_reference_loop_authoritative_inputs_must_bind_exact_artifact_refs_and_hashes": true,
    "reference_loop_family": "arc_bundle_recursive_compilation_loop",
    "required_binding_fields": [
      "reference_loop_family",
      "reference_instance_id",
      "intent_packet_id"
    ],
    "module_classes": [
      "reasoning_module",
      "checkpoint_module",
      "evidence_gate_module",
      "operator_gate_module"
    ],
    "required_checkpoint_capabilities": [
      "bundle_lint",
      "artifact_consistency_lint",
      "semantic_closeout_lint",
      "stop_gate_metrics_build",
      "quality_dashboard_build",
      "committed_event_stream_validation",
      "instruction_policy_validation"
    ],
    "capability_to_executor_granularity_must_be_explicit": true,
    "capability_entries_must_resolve_as_single_executor_or_explicit_executor_family": true,
    "reasoning_dispatch_provenance_required": true,
    "hard_module_executor_binding_required": true,
    "hard_module_executor_parameter_policy_required": true,
    "unchecked_shell_interpolation_for_soft_originated_inputs_rejected": true,
    "required_drift_taxonomy": [
      "ontology_drift",
      "epistemic_drift",
      "deontic_drift",
      "utility_drift"
    ],
    "hard_checkpoint_truth_boundary_preserved": true,
    "no_hidden_prompt_only_module_authority": true,
    "no_model_prose_truth_substitution": true
  },
  "test_requirements": [
    "canonical_json_hashing_deterministic",
    "reference_instance_pair_binding_verified",
    "authoritative_input_refs_and_hashes_resolve_for_reference_instance_pair",
    "module_class_enum_frozen",
    "drift_taxonomy_enum_frozen",
    "checkpoint_executor_bindings_resolve_for_hard_modules",
    "capability_to_executor_granularity_verified",
    "checkpoint_parameter_policies_reject_untyped_soft_inputs",
    "reasoning_dispatch_provenance_required_for_soft_modules",
    "unbound_module_capabilities_rejected",
    "module_authority_status_drift_rejected",
    "v37a_scope_boundary_preserved",
    "metric_key_exact_set_equal_v65"
  ],
  "fail_closed_conditions": [
    "intent_packet_missing_objective_or_success_or_failure_condition",
    "intent_packet_missing_authoritative_inputs_or_required_hard_checkpoints",
    "authoritative_input_ref_or_hash_missing_or_unresolvable",
    "hard_module_missing_executor_binding_or_parameter_policy",
    "checkpoint_capability_declared_without_resolvable_bound_executor",
    "capability_to_executor_granularity_ambiguous",
    "reasoning_module_missing_dispatch_provenance",
    "unchecked_shell_interpolation_attempted_from_soft_output",
    "unknown_module_class_or_unknown_capability_declared",
    "reference_instance_pair_binding_drift",
    "hard_checkpoint_truth_boundary_blurred",
    "out_of_scope_sequence_or_runnable_loop_surfaces_introduced"
  ],
  "closeout_required_block_keys": [
    "metric_key_exact_set_equal_v65",
    "reference_instance_pair_binding_verified",
    "authoritative_input_refs_and_hashes_verified",
    "checkpoint_executor_bindings_verified",
    "capability_to_executor_granularity_verified",
    "checkpoint_parameter_safety_verified",
    "reasoning_dispatch_provenance_verified",
    "hard_checkpoint_truth_boundary_preserved",
    "v37a_scope_boundary_preserved",
    "verification_passed"
  ],
  "exit_criteria": [
    "A1_and_A2_merged_with_green_ci",
    "meta_testing_intent_packet_and_meta_module_catalog_exist_as_canonical_hash_bound_artifacts",
    "one_bound_reference_instance_pair_exists_for_arc_bundle_recursive_compilation_loop",
    "the_bound_reference_pair_resolves_exact_authoritative_input_refs_and_hashes_for_the_chosen_v65_closeout_instance",
    "module_classes_binding_tuple_and_drift_taxonomy_are_frozen",
    "capability_to_executor_granularity_is_frozen",
    "hard_module_executor_bindings_and_parameter_safety_are_frozen",
    "reasoning_dispatch_provenance_is_frozen",
    "stop_gate_schema_family_and_metric_keyset_remain_unchanged",
    "no_sequence_contract_run_trace_runnable_loop_or_control_update_export_is_released",
    "no_v37b_or_v37c_surface_is_released"
  ]
}
```

## Release Shape (Narrative)

- `vNext+66` is the first bounded recursive-compilation substrate arc only.
- `A1` should freeze typed intent and typed module ontology for one bounded
  `arc_bundle_recursive_compilation_loop`.
- `A2` should prove determinism, hash binding, executor-binding integrity,
  parameter-safety integrity, dispatch-provenance integrity, authoritative-input
  ref/hash integrity, capability-granularity integrity, and stop-gate continuity while
  rejecting authority drift.
- the arc must consume current hard checkpoint executor surfaces as authoritative
  downstream validators without pretending those surfaces are already one runnable
  meta-loop;
- the arc must keep the distinction between:
  - operational influence in the active builder loop;
  - accepted compilation into repo governance;
  explicit rather than implicit.

## Recommendation

- proceed with `V37-A` only in `vNext+66`;
- keep the first implementation lane narrow:
  typed intent plus module ontology first,
  runnable sequence law later;
- preserve the recursive-compilation methodology note as a higher-order input rather than
  collapsing it into immediate runtime authority.
