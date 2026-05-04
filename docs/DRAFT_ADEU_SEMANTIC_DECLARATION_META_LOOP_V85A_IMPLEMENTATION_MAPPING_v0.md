# Draft ADEU Semantic Declaration Meta-Loop V85-A Implementation Mapping v0

Status: support / slice mapping for planned `V85-A`.

Authority layer: support.

This note is not a starter lock. The future active `V85-A` starter should come
from the canonical `vNext+239` trio if no intervening arc claims that number:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS239.md`
- `docs/ASSESSMENT_vNEXT_PLUS239_EDGES.md`

`V85-A` should select only declaration request intake, source indexing, and
non-authority guardrails. It should not create canonical lookup registries,
obligation expansion, evidence contracts, audit taskpacks, summaries,
handoffs, implementation, runtime behavior, or `V86`.

## Selected Surfaces

- `repo_turn_semantic_declaration_request@1`
- `repo_semantic_declaration_source_index@1`
- `repo_semantic_declaration_non_authority_guardrail@1`

## Package Scope

Expected implementation files:

- `packages/adeu_repo_description/src/adeu_repo_description/semantic_declaration_meta_loop.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Expected schema files:

- `packages/adeu_repo_description/schema/repo_turn_semantic_declaration_request.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_declaration_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_declaration_non_authority_guardrail.v1.json`
- `spec/repo_turn_semantic_declaration_request.schema.json`
- `spec/repo_semantic_declaration_source_index.schema.json`
- `spec/repo_semantic_declaration_non_authority_guardrail.schema.json`

Expected tests and fixtures:

- `packages/adeu_repo_description/tests/test_semantic_declaration_meta_loop_v85a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus239/repo_turn_semantic_declaration_request_v239_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus239/repo_semantic_declaration_source_index_v239_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus239/repo_semantic_declaration_non_authority_guardrail_v239_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus239/repo_semantic_declaration_v239_reject_*.json`

## Source Index Requirements

Minimum `semantic_declaration_source_role` values for `V85-A`:

- `v84_readiness_summary_source`
- `v84_handoff_source`
- `v84_closeout_source`
- `v83_projection_packet_context`
- `combined_dogfood_context`
- `post_v84_roadmap_source`
- `canonical_meta_loop_support_source`
- `morphic_ux_support_context`
- `direct_oai_support_context`
- `meta_orchestrator_support_context`
- `operator_turn_source`
- `repo_task_context_source`
- `natural_task_context_source`
- `code_context_source`
- `canonical_pointer_context`
- `opaque_pointer_context`
- `generated_declaration_candidate_source`
- `model_or_agent_profile_source`
- `reviewer_amendment_source`
- `explicit_absence_marker`
- `support_process_context`

Minimum source currentness values:

- `current_concrete_source`
- `current_operator_turn`
- `support_context_only`
- `historical_context_only`
- `explicit_absence_marker`
- `stale_or_superseded`
- `unknown_needs_review`

Minimum declaration authority posture values:

- `source_for_review_only`
- `candidate_only`
- `support_context_not_authority`
- `authority_requires_later_lock`
- `authority_explicitly_absent`
- `not_applicable`

Eligibility rule:

```text
if declaration_review_eligibility_posture == eligible_for_semantic_declaration_review:
  source_refs include released V84-C substrate
  source_refs include operator_turn_source or repo_task_context_source
  semantic_act_witness_rows include direct/current witnesses for the proposed act
  support_process_context and support_context_only are not the only sources
  semantic_declaration_session_ref is non-empty
  binding_resolution_posture == selected_for_later_lookup_review
  declaration_candidate_status == candidate_recorded_for_review
  declaration_selection_status == not_selected_by_v85a
```

## Declaration Request Shape

Minimum request fields:

- `declaration_request_ref`
- `semantic_declaration_session_ref`
- `candidate_ref`
- `turn_ref`
- `source_refs`
- `source_witness_refs`
- `semantic_act_witness_rows`
- `operator_turn_refs`
- `repo_context_refs`
- `declared_semantic_act_rows`
- `negative_cue_rows`
- `resident_model_competency_rows`
- `declaration_horizon`
- `requested_declaration_review_horizon`
- `binding_posture`
- `binding_resolution_posture`
- `binding_basis_refs`
- `negative_cue_refs`
- `uncertainty_slot_refs`
- `canonical_lookup_required_posture`
- `declaration_candidate_status`
- `canonical_lookup_status`
- `declaration_selection_status`
- `declaration_recordability_posture`
- `declaration_review_eligibility_posture`
- `guardrail_refs`
- `non_authority_posture`
- `limitation_note`

Minimum `declaration_recordability_posture` values:

- `recordable_from_concrete_operator_turn`
- `recordable_from_repo_context`
- `recordable_from_support_context_only`
- `recordable_from_generated_declaration_candidate`
- `recordable_with_absence_markers`
- `not_recordable_missing_source`

Minimum `declaration_review_eligibility_posture` values:

- `eligible_for_semantic_declaration_review`
- `blocked_by_missing_turn_source`
- `blocked_by_missing_repo_context`
- `blocked_by_support_only_source`
- `blocked_by_generated_declaration_provenance_gap`
- `blocked_by_ambiguous_binding`
- `blocked_by_registry_gap`
- `blocked_by_missing_witness`
- `blocked_by_missing_guardrail`
- `future_family_only`
- `rejected_out_of_scope`

Minimum `canonical_lookup_required_posture` values:

- `lookup_required_later`
- `lookup_not_selected_by_v85a`
- `lookup_blocked_by_missing_pointer`
- `lookup_blocked_by_registry_gap`
- `lookup_not_applicable`

Minimum binding-resolution posture values:

- `selected_for_later_lookup_review`
- `ambiguous_requires_review`
- `abstain_declared`
- `registry_gap_declared`
- `malformed_input_declared`
- `blocked_by_missing_witness`
- `support_only_not_selected`

Minimum candidate / lookup / selection status values:

- `declaration_candidate_status`
  - `candidate_recorded_for_review`
  - `ambiguous_candidate`
  - `abstain_candidate`
  - `registry_gap_candidate`
  - `malformed_candidate`
  - `support_context_only_candidate`
- `canonical_lookup_status`
  - `lookup_not_selected_by_v85a`
  - `lookup_required_later`
  - `lookup_blocked_by_missing_pointer`
  - `lookup_blocked_by_registry_gap`
  - `lookup_not_applicable`
- `declaration_selection_status`
  - `not_selected_by_v85a`
  - `ambiguous_not_selected`
  - `abstained_not_selected`
  - `registry_gap_not_selected`
  - `blocked_not_selected`

Minimum resident-model competency rows:

- `competency_ref`
- `semantic_declaration_session_ref`
- `competency_kind`
- `required_posture`
- `evidence_or_fixture_refs`
- `failure_routing_posture`
- `non_authority_guardrail_refs`

Minimum `competency_kind` values:

- `pointer_obedience`
- `artifact_shape_obedience`
- `bounded_local_judgment`
- `declared_uncertainty_routing`
- `order_preservation`
- `duplicate_preservation`
- `unknown_pointer_abstention`
- `no_unauthorized_transition`
- `stop_at_schema_boundary`

These are independent competencies, not mutually exclusive enum choices.

## Declared Act Rows

Minimum declared semantic act row fields:

- `semantic_act_ref`
- `semantic_declaration_session_ref`
- `operator`
- `object_class`
- `source_class`
- `target_class`
- `target_context_refs`
- `modifiers`
- `binding_basis_refs`
- `source_witness_refs`
- `ambiguity_posture`
- `registry_gap_posture`
- `declaration_candidate_status`
- `declaration_selection_status`
- `canonical_status`
- `limitation_note`

`V85-A` may record a candidate operator or class, but it must not prove
canonical validity. Canonical validity belongs to `V85-B`. A non-canonical or
unknown class must remain `registry_gap`, `abstain`, `ambiguous`, or blocked.

Minimum `canonical_status` values:

- `canonical_pointer_claimed_for_later_lookup`
- `canonical_status_unverified_by_v85a`
- `candidate_class_only`
- `unknown_class_registry_gap`
- `not_applicable`

Semantic act witness rows should be embedded in the source index or request
payload. Minimum fields:

- `witness_ref`
- `semantic_declaration_session_ref`
- `source_refs`
- `witnessed_element`
- `witness_strength`
- `witness_currentness`
- `limitation_note`

Minimum witnessed elements:

- `operator`
- `object_class`
- `source_class`
- `target_class`
- `target_context`
- `modifier`
- `negative_cue`
- `uncertainty`

Minimum witness strengths:

- `direct`
- `indirect`
- `contextual`
- `support_only`
- `absence_marker`
- `conflict_marker`

Ambiguity, abstain, and registry-gap invariants:

```text
if ambiguity_posture != not_ambiguous:
  declaration_review_eligibility_posture must not be eligible_for_semantic_declaration_review
  unless the request is explicitly routed to ambiguity review only

if registry_gap_posture indicates unknown class:
  canonical_status == unknown_class_registry_gap
  canonical_lookup_required_posture == lookup_blocked_by_registry_gap

if binding_resolution_posture == abstain_declared:
  no obligation_family_refs may appear downstream for that act
```

## Negative Cue Rows

Minimum negative cue row fields:

- `negative_cue_ref`
- `semantic_declaration_session_ref`
- `source_refs`
- `cue_kind`
- `effect_on_declaration`
- `limitation_note`

Minimum `cue_kind` values:

- `asks_to_implement_now`
- `asks_to_execute_now`
- `asks_to_select_next_family`
- `asks_to_authorize_runtime`
- `asks_to_productize`
- `asks_to_release`
- `asks_to_expand_obligations_now`
- `asks_to_skip_lookup`
- `asks_to_invent_class`

Minimum `effect_on_declaration` values:

- `blocks_eligibility`
- `routes_to_guardrail`
- `routes_to_future_family_only`
- `allowed_context_only`

## Guardrail Requirements

Minimum forbidden declaration actions:

- `expand_obligations`
- `emit_evidence_contract`
- `emit_edge_probe_plan`
- `emit_reviewer_taskpack`
- `emit_audit_report`
- `run_closeout_transition_table`
- `create_implementation_lock`
- `activate_work_packet`
- `execute_work_packet`
- `edit_code`
- `run_command`
- `invoke_tool_for_effect`
- `mutate_target`
- `open_pr`
- `commit_changes`
- `merge_or_release`
- `authorize_product`
- `create_graph_memory_authority`
- `amend_recursive_policy`
- `select_v86`

Every request row should reference at least one non-authority guardrail. The
guardrail should carry:

- `declaration_non_authority_posture = no_declaration_authority_granted_by_v85`
- `obligation_expansion_posture = no_obligation_expansion_performed_by_v85a`
- `implementation_posture = no_implementation_performed_by_v85a`
- `runtime_transition_posture = no_runtime_transition_performed_by_v85a`
- `future_family_selection_posture = no_future_family_selected_by_v85a`

Guardrail linkage should include the same `semantic_declaration_session_ref`
and `candidate_ref` as the request row.

## Reference Fixture Strategy

The first `vNext+239` reference fixture should include:

- one source-bound semantic declaration request for institutionalizing
  semantic declaration review;
- one stable `semantic_declaration_session_ref` shared by request, act,
  witness, competency, and guardrail rows;
- one ambiguous or abstain request showing declared uncertainty;
- one registry-gap candidate showing that unknown classes fail closed;
- one support-context-only row that is recordable but not eligible;
- source rows for released `V84-C` fixtures and closeout evidence;
- source rows for the post-`V84` roadmap and canonical meta-loop support note;
- one non-authority guardrail with non-empty forbidden declaration and
  downstream actions.

The fixture should include zero:

- canonical lookup index rows;
- operator/class registry rows;
- obligation-family registry rows;
- pointer lookup fixtures;
- declaration summaries;
- handoffs;
- obligation expansion bundles;
- evidence contracts;
- audit taskpacks;
- deterministic transition tables;
- implementation locks;
- code edits;
- commands, tool invocations, PRs, commits, merges, releases;
- product, graph, recursive-policy, or `V86` selection rows.

## Mandatory Reject Cases

Reject:

- eligible declaration request with no `semantic_declaration_session_ref`;
- eligible declaration request with no released `V84-C` source posture;
- support-only source row marked eligible;
- generated/model declaration marked eligible without source witnesses;
- opaque pointer treated as natural semantic truth;
- ambiguous binding marked `selected`;
- unknown class or pointer marked canonical without registry-gap posture;
- unknown class repaired into nearest registry class instead of `registry_gap`;
- support doctrine class label treated as current turn eligibility;
- resident-model competency represented as one exclusive posture instead of
  required row coverage;
- declaration request claiming obligation expansion happened;
- declaration request claiming implementation or runtime authority;
- declaration request with empty forbidden action lists;
- operator preference treated as canonical pointer truth;
- `V86` or later-family selection inside `V85-A`.

## Verification

Recommended targeted checks for the future active slice:

```text
PYTHONPATH=packages/adeu_repo_description/src \
  pytest packages/adeu_repo_description/tests/test_semantic_declaration_meta_loop_v85a.py \
         packages/adeu_repo_description/tests/test_repo_description_export_schema.py
```

For PR readiness, follow repo guidance and prefer `make check` unless the
active diff is docs/artifacts-only and the lock explicitly permits the
arc-bundle shortcut.
