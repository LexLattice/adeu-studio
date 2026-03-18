# Locked Continuation vNext+70 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS69.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS69.md`
- `docs/ASSESSMENT_vNEXT_PLUS69_EDGES.md`
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/LOCKED_URM_CODEX_INTEGRATION_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 18, 2026 UTC).

## Decision Basis

- `vNext+69` (`V37-D`, `D1`/`D2`) is merged on `main` with green CI checks.
- `vNext+69` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS69.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS69_EDGES.md` marks `V37-D` as closed and restores
  eligibility for the next bounded recursive-compilation path.
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` remains the higher-order methodology note
  distinguishing:
  - soft operational influence in the active builder loop;
  - accepted compilation into explicit repo governance.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md` now names `V37-E` as the next default candidate
  after `V37-D` closure.
- current repo reality after `v69` is narrower than advisory control-update export:
  - canonical `meta_testing_intent_packet@1`, canonical `meta_module_catalog@1`, one
    accepted bound reference-instance pair, and canonical
    `v37a_meta_intent_module_catalog_evidence@1` now exist on `main`;
  - canonical `meta_loop_sequence_contract@1`, canonical `meta_loop_run_trace@1`, one
    accepted bound sequence/trace reference pair, and canonical
    `v37b_sequence_trace_evidence@1` now also exist on `main`;
  - canonical `meta_loop_checkpoint_result_manifest@1`, one accepted executed
    `meta_loop_run_trace@1`, one accepted executable reference loop, and canonical
    `v37c_reference_loop_evidence@1` now also exist on `main`;
  - canonical `meta_loop_drift_diagnostics@1`, canonical
    `meta_loop_conformance_report@1`, and canonical
    `v37d_drift_diagnostics_conformance_evidence@1` now also exist on `main`;
  - no released `meta_control_update_candidate@1`,
    `meta_control_update_manifest@1`, or
    `v37e_control_update_export_evidence@1` exists on `main`.
- `vNext+70` therefore selects one thin `V37-E` baseline slice only:
  - canonical `meta_control_update_candidate@1`;
  - canonical `meta_control_update_manifest@1`;
  - one accepted advisory export lane over the released `V37-A` / `V37-B` / `V37-C` /
    `V37-D` tuple;
  - frozen advisory-only posture, hard-control-first target ranking, and typed
    application friction between recommendation and application;
  - closeout evidence plus determinism/guard coverage;
  - no automatic repo mutation, policy adoption, or broader loop-family widening in
    this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS69.md` remain authoritative for baseline
  continuity.
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` remains methodology above arcs:
  it informs this arc but does not itself authorize runtime behavior, lock changes, or
  control updates.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v70,
  - v70 keyset must be exactly equal to v69 keyset,
  - baseline derived cardinality at v70 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v70 is explicit and narrow:
  - this arc authorizes one `L1` advisory control-update export lane only,
  - no new `L0` executable reference-loop widening is authorized in this arc,
  - no `L2` broad autonomous coordination or repo-wide benchmark lane is authorized in
    this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35`, `V36`, and `V37-A` through `V37-D` baseline,
  - no autonomous repo mutation, branch management, PR submission, policy promotion,
    prompt rewrite, or validator rollout is authorized in this arc.
- `V35-A` through `V35-E` runtime/state/delegation/visibility/topology/enforcement
  surfaces remain frozen prerequisites and are not redefined by this arc.
- `V36-A` through `V36-E` UX-governance/compiler-export surfaces remain frozen
  prerequisites and are not redefined by this arc.
- `V37-A` through `V37-D` release-shape locks for v66-v69 are now frozen prerequisite
  substrate:
  - accepted explicit intent, accepted module ontology, accepted sequence law, accepted
    reference/executed trace law, accepted checkpoint-result evidence, and accepted
    diagnostics/conformance all remain authoritative inputs and are not redefined by
    this arc.
- `V37-E` release-shape lock for v70 is frozen:
  - this arc is one bounded advisory control-update export baseline only,
  - the arc must define `meta_control_update_candidate@1` and
    `meta_control_update_manifest@1`,
  - the arc must preserve the frozen shared binding tuple across consumed and emitted
    artifacts:
    `reference_loop_family`, `reference_instance_id`, `intent_packet_id`,
  - the arc must bind exactly back to the released `V37-A`, `V37-B`, `V37-C`, and
    `V37-D` artifacts rather than introducing a new reference terrain,
  - the first-family accepted manifest must emit exactly one candidate id; v70 is a
    single-candidate advisory export lane, not an open-cardinality candidate bag,
  - candidates may be derived only from accepted explicit intent, accepted
    module/sequence artifacts, accepted hard checkpoint outputs, accepted drift
    diagnostics, and accepted conformance reports,
  - only `error` and `warning` findings may emit candidates in the first family;
    `advisory` findings remain non-exporting in v70,
  - the arc must freeze the minimum candidate structure:
    `candidate_id`, `target_control_class`, `target_surface_ref`,
    `bound_finding_ids`, `supporting_evidence_refs`,
    `expected_drift_reduction_claim`, `risk_notes`, `application_friction_mode`,
    `advisory_only`,
  - `target_surface_ref` must resolve only through canonical repo-native reference
    namespaces rather than prose labels:
    `lock_anchor_ref`, `schema_field_ref`, `validator_rule_ref`,
    `evidence_requirement_ref`, `runtime_guard_ref`,
    `prompt_dispatch_ref`, `module_catalog_field_ref`,
    `sequence_contract_field_ref`,
  - `expected_drift_reduction_claim` must remain qualitative, evidence-bound, and
    explicitly non-authoritative; free numeric efficacy claims are forbidden unless a
    later arc freezes a formal numeric basis,
  - `application_friction_mode` must remain explicit and bounded to a frozen
    first-family enum:
    `review_only`, `adjudication_required`, `blocked_from_direct_application`,
  - minimum application-friction floors are frozen by target class:
    `validator_rule`, `runtime_guard`, `evidence_requirement`, `schema_field`, and
    `lock_text` may not fall below `adjudication_required` in the first family,
  - the arc must freeze the minimum manifest structure:
    shared binding tuple, emitted candidate ids, candidate class counts,
    emitted candidate count, derivation refs/hashes, target-class priority order
    actually used for ranking, ranking basis used, suppressed lower-ranked alternatives
    considered but not emitted, and an explicit statement that emission is not
    acceptance,
  - allowed first-family target control classes are bounded to repo-native surfaces:
    `lock_text`, `schema_field`, `validator_rule`, `evidence_requirement`,
    `runtime_guard`, `prompt_dispatch_convention`, `module_catalog_field`,
    `sequence_contract_field`,
  - the first-family export lane must use one frozen total target-class priority order:
    `validator_rule`, `runtime_guard`, `evidence_requirement`, `schema_field`,
    `lock_text`, `module_catalog_field`, `sequence_contract_field`,
    `prompt_dispatch_convention`,
  - deterministic tie-breaks among same-rank candidate alternatives are frozen:
    bound finding severity, then bound finding id lexical order, then candidate id
    lexical order,
  - all emitted candidates remain advisory:
    candidate existence is not policy, not acceptance, and not a repo mutation,
  - canonical `meta_control_update_candidate@1` and
    `meta_control_update_manifest@1` must not carry raw ready-to-apply patch payload
    fields or raw executable shell payload fields in v70,
  - no generalized self-improvement engine, open-ended patch generator, or blind
    mutation surface is authorized in this arc,
  - no new stop-gate metric keys are authorized in this path unless explicitly released
    in the corresponding lock doc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `E1` Advisory control-update candidate/manifest baseline (`V37-E`)
2. `E2` Advisory control-update export evidence + determinism/guard suite (`V37-E`)

Out-of-scope note:

- any broader multi-run loop-family widening in this arc,
- any generalized autonomous self-improvement engine in this arc,
- any automatic repo mutation, automatic lock update, or automatic policy adoption in
  this arc,
- any automatic validator rollout or automatic prompt rewrite in this arc,
- any raw ready-to-apply patch payload field or raw executable shell payload field in
  canonical v70 artifacts,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v70)

- broader multi-run evaluation windows for recurring drift across more than the first
  bounded reference-loop instance
- later widening of target control classes beyond the bounded first-family set
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold

## V69 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS69.md",
  "target": "V37-E-baseline",
  "required_continuity_guards": [
    "V37_D_D1_DRIFT_DIAGNOSTICS_BASELINE_GREEN",
    "V37_D_D2_DRIFT_DIAGNOSTICS_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v69_v37d_closed_diagnostics_and_conformance_substrate_remains_frozen_while_v37e_advisory_control_update_export_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v70.
- this narrowed machine-checkable consumption block is v69-local only and does not
  weaken the global continuity locks declared above; v14-v69 baseline continuity
  remains in force for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V37-E Advisory Control-Update Export Contract (Machine-Checkable)

```json
{
  "schema": "v37e_control_update_export_contract@1",
  "target_arc": "vNext+70",
  "target_path": "V37-E",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v11.md",
    "recursive_compilation_note": "docs/DRAFT_RECURSIVE_COMPILATION_v0.md",
    "practical_harness_flow": "docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md",
    "codex_integration_lock": "docs/LOCKED_URM_CODEX_INTEGRATION_v0.md",
    "externalized_reasoning_kernel": "docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md",
    "v69_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS69.md",
    "v69_edge_assessment": "docs/ASSESSMENT_vNEXT_PLUS69_EDGES.md",
    "v66_meta_testing_intent_packet_reference": "apps/api/fixtures/meta_testing/vnext_plus66/meta_testing_intent_packet_arc_closeout_v65_reference.json",
    "v66_meta_module_catalog_reference": "apps/api/fixtures/meta_testing/vnext_plus66/meta_module_catalog_arc_closeout_v65_reference.json",
    "v67_meta_loop_sequence_contract_reference": "apps/api/fixtures/meta_testing/vnext_plus67/meta_loop_sequence_contract_arc_closeout_v65_reference.json",
    "v67_meta_loop_run_trace_reference": "apps/api/fixtures/meta_testing/vnext_plus67/meta_loop_run_trace_arc_closeout_v65_reference.json",
    "v68_meta_loop_checkpoint_result_manifest_reference": "apps/api/fixtures/meta_testing/vnext_plus68/meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
    "v68_executed_meta_loop_run_trace_reference": "apps/api/fixtures/meta_testing/vnext_plus68/meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
    "v69_meta_loop_drift_diagnostics_reference": "apps/api/fixtures/meta_testing/vnext_plus69/meta_loop_drift_diagnostics_arc_closeout_v65_reference.json",
    "v69_meta_loop_conformance_report_reference": "apps/api/fixtures/meta_testing/vnext_plus69/meta_loop_conformance_report_arc_closeout_v65_reference.json",
    "v66_v37a_evidence": "artifacts/agent_harness/v66/evidence_inputs/v37a_meta_intent_module_catalog_evidence_v66.json",
    "v67_v37b_evidence": "artifacts/agent_harness/v67/evidence_inputs/v37b_sequence_trace_evidence_v67.json",
    "v68_v37c_evidence": "artifacts/agent_harness/v68/evidence_inputs/v37c_reference_loop_evidence_v68.json",
    "v69_v37d_evidence": "artifacts/agent_harness/v69/evidence_inputs/v37d_drift_diagnostics_conformance_evidence_v69.json",
    "bounded_reference_loop_family": "arc_bundle_recursive_compilation_loop",
    "first_reference_loop_anchor": {
      "shape": "arc_closeout_bundle_instance",
      "reference_arc": 65,
      "reference_phase": "closeout"
    },
    "stop_gate_schema_family": "stop_gate_metrics@1"
  },
  "control_update_export_requirements": {
    "foundation_status": "deterministic_advisory_control_update_export_over_released_v37a_v37b_v37c_v37d_substrate",
    "meta_control_update_candidate_schema_required": true,
    "meta_control_update_manifest_schema_required": true,
    "accepted_reference_candidate_required": true,
    "accepted_reference_manifest_required": true,
    "required_binding_fields": [
      "reference_loop_family",
      "reference_instance_id",
      "intent_packet_id"
    ],
    "reference_binding_tuple_must_match_v37a_v37b_v37c_v37d": true,
    "accepted_reference_candidate_cardinality": "exactly_one",
    "candidate_generation_eligible_severities": [
      "error",
      "warning"
    ],
    "candidate_required_fields": [
      "candidate_id",
      "target_control_class",
      "target_surface_ref",
      "bound_finding_ids",
      "supporting_evidence_refs",
      "expected_drift_reduction_claim",
      "risk_notes",
      "application_friction_mode",
      "advisory_only"
    ],
    "target_surface_ref_allowed_namespaces": [
      "lock_anchor_ref",
      "schema_field_ref",
      "validator_rule_ref",
      "evidence_requirement_ref",
      "runtime_guard_ref",
      "prompt_dispatch_ref",
      "module_catalog_field_ref",
      "sequence_contract_field_ref"
    ],
    "target_surface_ref_must_use_canonical_repo_native_ref_syntax": true,
    "expected_drift_reduction_claim_must_be_qualitative_evidence_bound_and_non_numeric_without_frozen_basis": true,
    "application_friction_mode_enum": [
      "review_only",
      "adjudication_required",
      "blocked_from_direct_application"
    ],
    "minimum_application_friction_by_target_control_class": {
      "validator_rule": "adjudication_required",
      "runtime_guard": "adjudication_required",
      "evidence_requirement": "adjudication_required",
      "schema_field": "adjudication_required",
      "lock_text": "adjudication_required",
      "module_catalog_field": "review_only",
      "sequence_contract_field": "review_only",
      "prompt_dispatch_convention": "review_only"
    },
    "manifest_required_fields": [
      "reference_loop_family",
      "reference_instance_id",
      "intent_packet_id",
      "emitted_candidate_ids",
      "candidate_class_counts",
      "emitted_candidate_count",
      "derivation_refs",
      "derivation_hashes",
      "target_class_priority_order",
      "ranking_basis_used",
      "suppressed_lower_ranked_target_classes",
      "emission_is_not_acceptance"
    ],
    "allowed_first_family_target_control_classes": [
      "lock_text",
      "schema_field",
      "validator_rule",
      "evidence_requirement",
      "runtime_guard",
      "prompt_dispatch_convention",
      "module_catalog_field",
      "sequence_contract_field"
    ],
    "target_control_class_total_priority_order": [
      "validator_rule",
      "runtime_guard",
      "evidence_requirement",
      "schema_field",
      "lock_text",
      "module_catalog_field",
      "sequence_contract_field",
      "prompt_dispatch_convention"
    ],
    "candidate_selection_tie_break_order": [
      "bound_finding_severity",
      "bound_finding_id_lexical",
      "candidate_id_lexical"
    ],
    "candidate_derivation_sources_must_bind_to_released_substrate": [
      "accepted_intent_packet",
      "accepted_module_catalog",
      "accepted_sequence_contract",
      "accepted_reference_trace",
      "accepted_executed_trace",
      "accepted_checkpoint_result_manifest",
      "accepted_drift_diagnostics",
      "accepted_conformance_report",
      "accepted_v37d_evidence"
    ],
    "emission_is_advisory_only": true,
    "suppressed_lower_ranked_alternatives_must_be_recorded": true,
    "raw_patch_or_shell_payload_fields_forbidden_in_canonical_v37e_artifacts": true,
    "no_automatic_repo_mutation_or_policy_adoption": true,
    "no_generalized_self_improvement_engine": true
  },
  "test_requirements": [
    "canonical_json_hashing_deterministic",
    "v37a_reference_tuple_consumed_without_drift",
    "v37b_reference_tuple_consumed_without_drift",
    "v37c_reference_tuple_consumed_without_drift",
    "v37d_reference_tuple_consumed_without_drift",
    "meta_control_update_candidate_schema_serialization_deterministic",
    "meta_control_update_manifest_schema_serialization_deterministic",
    "reference_control_update_candidate_serialization_deterministic",
    "reference_control_update_manifest_serialization_deterministic",
    "accepted_reference_candidate_cardinality_verified",
    "candidate_structure_verified",
    "manifest_structure_verified",
    "advisory_only_status_verified",
    "candidate_generation_severity_gate_verified",
    "target_surface_ref_namespace_verified",
    "expected_drift_reduction_claim_bounded_verified",
    "application_friction_mode_verified",
    "application_friction_floor_verified",
    "target_control_class_enum_verified",
    "target_control_class_total_priority_order_verified",
    "candidate_selection_tie_breaks_verified",
    "candidate_derivation_bindings_verified",
    "suppressed_lower_ranked_alternatives_recorded",
    "candidate_emission_is_not_acceptance_verified",
    "raw_patch_or_shell_payload_fields_absent",
    "v37e_scope_boundary_preserved",
    "metric_key_exact_set_equal_v69"
  ],
  "fail_closed_conditions": [
    "control_update_candidate_missing_or_invalid",
    "control_update_manifest_missing_or_invalid",
    "reference_tuple_drift_from_v37a_v37b_v37c_or_v37d",
    "accepted_manifest_emits_not_exactly_one_candidate",
    "candidate_missing_required_fields",
    "manifest_missing_required_fields",
    "candidate_emitted_from_ineligible_advisory_severity",
    "target_surface_ref_not_canonical_namespace_bound",
    "expected_drift_reduction_claim_unbound_or_numeric_without_frozen_basis",
    "application_friction_mode_below_class_floor",
    "candidate_derived_from_non_canonical_or_unaccepted_inputs",
    "target_control_priority_order_or_tie_break_drift",
    "suppressed_lower_ranked_alternatives_not_recorded",
    "candidate_emission_collapses_into_acceptance_or_mutation",
    "raw_patch_or_shell_payload_field_present_in_canonical_artifact",
    "out_of_scope_target_control_class_emitted",
    "metric_key_regression_from_v69"
  ],
  "closeout_required_block_keys": [
    "metric_key_exact_set_equal_v69",
    "v37a_reference_tuple_consumed_without_drift",
    "v37b_reference_tuple_consumed_without_drift",
    "v37c_reference_tuple_consumed_without_drift",
    "v37d_reference_tuple_consumed_without_drift",
    "meta_control_update_candidate_schema_path",
    "meta_control_update_candidate_schema_hash",
    "meta_control_update_manifest_schema_path",
    "meta_control_update_manifest_schema_hash",
    "meta_control_update_candidate_reference_path",
    "meta_control_update_candidate_reference_hash",
    "meta_control_update_manifest_reference_path",
    "meta_control_update_manifest_reference_hash",
    "accepted_reference_candidate_cardinality_verified",
    "candidate_structure_verified",
    "manifest_structure_verified",
    "advisory_only_status_verified",
    "candidate_generation_severity_gate_verified",
    "target_surface_ref_namespace_verified",
    "expected_drift_reduction_claim_bounded_verified",
    "application_friction_mode_verified",
    "application_friction_floor_verified",
    "target_control_class_enum_verified",
    "target_control_class_total_priority_order_verified",
    "candidate_selection_tie_breaks_verified",
    "candidate_derivation_bindings_verified",
    "suppressed_lower_ranked_alternatives_recorded",
    "candidate_emission_is_not_acceptance_verified",
    "raw_patch_or_shell_payload_fields_absent",
    "v37e_scope_boundary_preserved",
    "verification_passed"
  ],
  "exit_criteria": [
    "E1_and_E2_merged_with_green_ci",
    "meta_control_update_candidate_exists_as_canonical_hash_bound_artifact",
    "meta_control_update_manifest_exists_as_canonical_hash_bound_artifact",
    "accepted_manifest_emits_exactly_one_candidate_for_the_first_family_lane",
    "accepted_candidate_and_manifest_bind_exactly_to_released_v37a_v37b_v37c_v37d_reference_tuple",
    "advisory_export_ranking_preserves_the_frozen_total_priority_order_and_tie_breaks",
    "export_preserves_typed_friction_between_recommendation_and_application",
    "candidate_generation_remains_limited_to_error_and_warning_findings",
    "candidate_emission_does_not_equal_acceptance_or_repo_mutation",
    "candidate_derivation_remains_bound_to_accepted_diagnostics_and_conformance",
    "canonical_v37e_artifacts_do_not_carry_raw_patch_or_shell_payload_fields",
    "stop_gate_schema_family_and_metric_keyset_remain_unchanged",
    "no_broader_autonomy_or_mutation_surface_is_released"
  ]
}
```

## Release Shape (Narrative)

- `vNext+70` is the bounded recursive-compilation advisory export arc only.
- `E1` should define canonical `meta_control_update_candidate@1` and canonical
  `meta_control_update_manifest@1`, then add one accepted advisory candidate and one
  accepted manifest over the already released `v69` diagnostics/conformance lane.
- `E2` should prove determinism, hash binding, exact cross-artifact binding back to the
  released `V37-A`, `V37-B`, `V37-C`, and `V37-D` tuple, exact first-family
  single-candidate cardinality, total ranking/tie-break law, typed target-surface
  refs, bounded claim semantics, application-friction floors, advisory-only posture,
  and stop-gate continuity while rejecting autonomous mutation or raw patch/shell
  payload surfaces.
- the first accepted advisory export lane should remain intentionally narrow:
  one bounded `v65`-style closeout reference-loop instance under one explicit intent
  packet, one accepted module/sequence substrate, one accepted executed loop result
  set, one accepted diagnostics artifact, and one accepted conformance report, not a
  generalized self-improvement or multi-loop export surface.

## Acceptance Summary

- v70 is successful only if one bounded typed advisory export layer can be emitted
  deterministically over the released diagnostics/conformance lane;
- the accepted candidate and manifest artifacts must remain bound to the same concrete
  existing reference-loop instance rather than to a family abstraction only;
- the accepted manifest must emit exactly one candidate id in the first family;
- export ranking must preserve the frozen total target priority order and deterministic
  tie-breaks rather than defaulting to prompt-local fixes when harder substrate fixes
  are available;
- target surface refs must remain canonically typed repo-native refs rather than prose
  labels, and drift-reduction claims must remain qualitative and evidence-bound rather
  than rhetorical or numeric-without-basis;
- the emitted advisory artifacts must preserve typed friction between recommendation and
  application rather than collapsing into blind copy-paste mutation surfaces;
- the emitted advisory artifacts must be sufficient to make recurring high-governance
  drift legible as a candidate future hardening path without treating candidate
  emission as accepted compilation.

## E1) Advisory Control-Update Candidate / Manifest Baseline (`V37-E`)

### Goal

Make `V37-E` real as a deterministic advisory export substrate rather than leaving
recurring drift as diagnostics-only output.

### Scope

- add canonical `meta_control_update_candidate@1` and canonical
  `meta_control_update_manifest@1` schemas for the bounded
  `arc_bundle_recursive_compilation_loop` family;
- add one accepted deterministic reference candidate artifact and one accepted
  deterministic manifest, bound by the shared
  `reference_loop_family`, `reference_instance_id`, and `intent_packet_id` fields back
  to the released `V37-A`, `V37-B`, `V37-C`, and `V37-D` substrate;
- freeze the first-family candidate cardinality:
  exactly one emitted candidate id in the accepted manifest;
- freeze first-family severity eligibility:
  only `error` and `warning` findings may emit candidates in v70;
- freeze equality of the reference binding tuple across the accepted `V37-A`, `V37-B`,
  `V37-C`, and `V37-D` artifacts, the accepted candidate, and the accepted manifest;
- freeze the minimum candidate structure:
  stable `candidate_id`, bounded `target_control_class`, `target_surface_ref`,
  bound finding ids, supporting evidence refs, expected drift-reduction claim,
  risk notes, explicit `application_friction_mode`, and `advisory_only`;
- freeze canonical `target_surface_ref` syntax to bounded repo-native namespaces rather
  than prose labels;
- freeze `expected_drift_reduction_claim` as qualitative, evidence-bound, and
  explicitly non-authoritative;
- freeze the minimum manifest structure:
  shared binding fields, emitted candidate ids, candidate class counts,
  emitted candidate count, derivation refs/hashes, target-class priority order,
  ranking basis used, suppressed lower-ranked alternatives, and explicit
  `emission_is_not_acceptance`;
- freeze the first-family allowed target control classes, exact total ranking order,
  and deterministic tie-break chain;
- freeze advisory-only status, target-class friction floors, and typed friction between
  recommendation and application;
- forbid raw ready-to-apply patch fields and raw executable shell payload fields from
  canonical v70 artifacts entirely.

### Locks

- v70 must not widen into broader multi-run loop-family export;
- v70 must not redefine the released `V37-A`, `V37-B`, `V37-C`, or `V37-D` artifacts;
- v70 must not widen into automatic repo mutation, validator rollout, prompt rewrite,
  or generalized self-improvement;
- emitted artifacts must not mint governance effect or acceptance merely by existing;
- canonical v70 artifacts must not carry raw patch/shell payload fields even as
  optional extras.

### Acceptance

- one bounded typed advisory export layer exists on `main` with canonical schemas, one
  coherent accepted advisory candidate artifact, one coherent accepted manifest,
  frozen single-candidate cardinality, frozen target-class set, frozen total ranking
  and tie-break order, explicit friction mode, and deterministic
  serialization/hashability without authority drift.

## E2) Advisory Export Evidence + Determinism / Guard Suite (`V37-E`)

### Goal

Make the v70 `V37-E` release closeout-grade rather than relying on schema files alone by
binding it to canonical evidence and fail-closed guard coverage.

### Scope

- materialize canonical `v37e_control_update_export_evidence@1`;
- validate schema/reference outputs against the frozen `V37-E` contract and consumed
  `V37-A` / `V37-B` / `V37-C` / `V37-D` substrate;
- prove deterministic serialization and hash binding for the canonical artifacts;
- fail closed on:
  - missing accepted candidate artifact or manifest,
  - accepted manifest cardinality drift,
  - advisory export binding mismatch against the released substrate,
  - invalid or missing candidate structure,
  - invalid or missing manifest structure,
  - ranking/tie-break drift,
  - target-surface refs that are not canonically namespace-bound,
  - drift-reduction claims that are rhetorical or numeric without a frozen basis,
  - friction modes that fall below the frozen class floors,
  - candidate emission from ineligible `advisory` severity findings,
  - candidate emission that collapses into acceptance or automatic mutation,
  - raw patch/shell payload fields present in canonical artifacts,
  - out-of-scope target control classes,
  - stop-gate metric-key continuity drift.

### Locks

- the `V37-E` evidence lane must not redefine semantics or widen authority surfaces;
- v70 closeout evidence must preserve exact stop-gate metric-key continuity versus v69;
- evidence/test wiring must stay advisory-only;
- no new stop-gate metric keys or schema-family changes are authorized for this slice.

### Acceptance

- v70 closeout can prove that the `V37-E` advisory export layer is canonical,
  deterministic, fail-closed, and authority-preserving without widening into automatic
  mutation, generalized autonomy, or raw patch/shell bypass surfaces;
- v70 closeout can prove that the accepted candidate/manifest artifacts remain anchored
  to the released accepted `V37-A` / `V37-B` / `V37-C` / `V37-D` substrate, preserve
  single-candidate cardinality, hard-control-first total priority order with frozen
  tie-breaks, and keep candidate emission advisory rather than treating it as accepted
  compilation.

## Implementation Slices

### `E1`

Branch/PR intent:

- add the canonical advisory control-update candidate and manifest baseline for the
  first bounded recursive-compilation surface.

Suggested PR title:

- `core_ir: add v70 e1 advisory control update baseline`

### `E2`

Branch/PR intent:

- add canonical v70 advisory export closeout evidence and fail-closed guard coverage.

Suggested PR title:

- `core_ir: add v70 e2 advisory export evidence`

## Exit Criteria

`vNext+70` is eligible for closeout only if:

1. `E1` and `E2` merge to `main` with green CI.
2. stop-gate schema family remains `stop_gate_metrics@1`.
3. stop-gate metric key cardinality remains exactly `80`.
4. canonical `meta_control_update_candidate@1`, canonical
   `meta_control_update_manifest@1`, and canonical
   `v37e_control_update_export_evidence@1` exist on `main`.
5. accepted candidate/manifest artifacts serialize deterministically and remain
   coherently bound to the released accepted `V37-A`, `V37-B`, `V37-C`, and `V37-D`
   substrate.
6. the accepted manifest emits exactly one candidate id in the first-family lane.
7. export ranking preserves the frozen total target priority order, deterministic
   tie-breaks, and the bounded first-family target-control-class set.
8. candidate emission remains advisory-only, severity-gated to `error`/`warning`
   findings, and preserves explicit friction between recommendation and application.
9. canonical v70 artifacts do not carry raw ready-to-apply patch payload fields or raw
   executable shell payload fields.
10. no automatic repo mutation, automatic prompt rewrite, or automatic validator rollout
    is released.
11. no broader multi-run loop-family widening or other later-family autonomy surface is
    released.

## Recommendation

- lock `vNext+70` as a narrow `V37-E` advisory control-update export baseline only;
- require canonical candidate/manifest schemas, accepted reference artifacts,
  hard-control-first ranking, advisory-only friction, and fail-closed evidence guards
  before treating recurring drift as a candidate future hardening path;
- defer broader multi-run evaluation, later target-class widening, and the separate
  closeout-hardening bundle to later locked work.
