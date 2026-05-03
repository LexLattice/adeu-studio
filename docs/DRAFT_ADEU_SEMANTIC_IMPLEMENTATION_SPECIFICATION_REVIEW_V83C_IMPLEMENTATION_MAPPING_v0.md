# Draft ADEU Semantic Implementation Specification Review V83-C Implementation Mapping v0

Status: support / slice implementation mapping for planned `V83-C`.

Authority layer: support.

This note scopes the final `V83` slice. It is not an implementation lock.
`V83-C` should become active only after `V83-B` closes and a future canonical
starter trio selects it.

Read with:

- `docs/support/arc_series_mapping/REVIEW_GPTPRO_SEMANTIC_IMPLEMENTATION_SPECIFICATION_V83_PLANNING_v0.md`

## Slice Intent

`V83-C` should summarize released `V83-A` and `V83-B` substrate, project a
bounded implementation-spec packet, emit intent-to-work-packet handoffs, and
close the `V83` family without implementing code, executing work packets,
mutating workflow state, dispatching workers, productizing, releasing, creating
graph memory, or selecting `V84`.

## Selected Surfaces

`V83-C` should select only:

- `repo_implementation_spec_projection_packet@1`
- `repo_intent_to_work_packet_handoff@1`
- `repo_semantic_implementation_spec_family_closeout_alignment@1`

Expected files:

- updates to `packages/adeu_repo_description/src/adeu_repo_description/semantic_implementation_spec.py`
- schema and mirror schema files for the three selected surfaces
- `packages/adeu_repo_description/tests/test_semantic_implementation_spec_v83c.py`
- `apps/api/fixtures/repo_description/vnext_plus235/repo_implementation_spec_projection_packet_v235_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus235/repo_intent_to_work_packet_handoff_v235_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus235/repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus235/repo_semantic_implementation_spec_v235_reject_*.json`

## Consumed Substrate

`V83-C` should consume released `V83-A` and `V83-B` rows:

- `repo_semantic_intent_contract@1`
- `repo_intent_source_index@1`
- `repo_intent_non_implementation_guardrail@1`
- `repo_intent_edge_decomposition@1`
- `repo_artifact_obligation_map@1`
- `repo_semantic_drift_ambiguity_register@1`

It should not create a parallel projection universe. Every projection packet
and handoff row should reference known released rows.

## Minimum Row Fields

`repo_implementation_spec_projection_packet@1` should include:

- `projection_packet_ref`
- `intent_contract_refs`
- `edge_decomposition_refs`
- `obligation_map_refs`
- `drift_register_refs`
- `candidate_ref`
- `source_refs`
- `implementation_spec_rows`
- `projection_provenance_rows`
- `spec_review_checklist_rows`
- `implementation_spec_quality_gate_rows`
- `projection_posture`
- `semantic_coverage_posture`
- `ready_basis_posture`
- `carried_blocker_refs`
- `carried_warning_refs`
- `non_implementation_posture`
- `guardrail_refs`
- `limitation_note`

Minimum implementation spec row fields:

- `implementation_spec_ref`
- `artifact_obligation_refs`
- `target_artifact_kind`
- `target_surface_refs`
- `required_change_summary`
- `required_validation_refs`
- `explicit_non_goals`
- `semantic_preservation_refs`
- `acceptance_evidence_requirements`
- `implementation_execution_posture`
- `limitation_note`

Minimum projection provenance row fields:

- `projection_provenance_ref`
- `projection_actor_kind`
- `model_or_agent_profile_refs`
- `prompt_context_refs`
- `input_intent_contract_refs`
- `input_edge_decomposition_refs`
- `input_obligation_map_refs`
- `generated_spec_refs`
- `reviewer_amendment_refs`
- `generation_scope_posture`
- `review_status`
- `non_authority_posture`
- `limitation_note`

Minimum spec review checklist row fields:

- `review_check_ref`
- `implementation_spec_refs`
- `semantic_edge_refs`
- `artifact_obligation_refs`
- `check_kind`
- `check_posture`
- `source_refs`
- `blocking_posture`
- `limitation_note`

Minimum implementation spec quality gate row fields:

- `quality_gate_ref`
- `projection_packet_refs`
- `required_check_refs`
- `gate_posture`
- `ready_basis_posture`
- `carried_blocker_refs`
- `carried_warning_refs`
- `non_implementation_guardrail`
- `limitation_note`

`repo_intent_to_work_packet_handoff@1` should include:

- `handoff_ref`
- `candidate_ref`
- `projection_packet_refs`
- `intent_contract_refs`
- `artifact_obligation_refs`
- `carried_drift_refs`
- `handoff_target`
- `handoff_subject_horizon`
- `handoff_posture`
- `required_later_authority_refs`
- `work_packet_authority_posture`
- `implementation_lock_requirement`
- `work_packet_execution_posture`
- `implementation_execution_posture`
- `meta_orchestrator_runtime_posture`
- `guardrail_refs`
- `limitation_note`

`repo_semantic_implementation_spec_family_closeout_alignment@1` should include:

- `family`
- `closed_by_arc`
- `closed_slice_ladder`
- `shipped_record_shapes`
- `consumed_source_families`
- `family_closed_on_main`
- `future_family_authority`
- `unselected_future_surfaces`
- `semantic_implementation_spec_boundary`
- `limitation_note`

## Vocabulary

Minimum projection posture:

- `projection_packet_ready_for_review`
- `projection_packet_ready_with_nonblocking_warnings`
- `blocked_by_missing_intent_contract`
- `blocked_by_missing_edge_decomposition`
- `blocked_by_missing_obligation_map`
- `blocked_by_semantic_drift`
- `blocked_by_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum semantic coverage posture:

- `all_required_edges_covered`
- `covered_with_nonblocking_warnings`
- `blocked_by_uncovered_edge`
- `blocked_by_unvalidated_edge`
- `blocked_by_ambiguous_edge`
- `future_family_only`

Minimum ready basis posture:

- `ready_no_blockers`
- `ready_with_nonblocking_warnings`
- `not_ready_blockers_remain`
- `authority_review_requested_for_blockers`
- `future_family_only`
- `rejected_out_of_scope`

Minimum projection actor kind:

- `human_operator`
- `model`
- `agent`
- `reviewer`
- `tool_assisted_review`
- `mixed`
- `unknown`

Minimum projection review status:

- `candidate_unreviewed`
- `reviewed_for_source_binding`
- `reviewed_for_edge_coverage`
- `reviewed_for_artifact_obligation_coverage`
- `blocked_by_missing_context`
- `blocked_by_semantic_drift`
- `blocked_by_authority_gap`

Minimum spec review check kind:

- `source_binding_check`
- `non_goal_preservation_check`
- `authority_boundary_check`
- `target_surface_boundedness_check`
- `edge_coverage_check`
- `validation_evidence_check`
- `reject_fixture_check`
- `generated_spec_provenance_check`
- `semantic_drift_check`
- `future_family_boundary_check`

Minimum spec review check posture:

- `passed_for_review_only`
- `blocked`
- `warning`
- `not_applicable`
- `requires_later_review`

Minimum implementation spec quality gate posture:

- `ready_for_later_implementation_slice_review`
- `ready_with_nonblocking_warnings`
- `blocked_by_missing_source_binding`
- `blocked_by_uncovered_edge`
- `blocked_by_unbounded_target_surface`
- `blocked_by_missing_validation_evidence`
- `blocked_by_generated_spec_provenance_gap`
- `blocked_by_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum work packet authority posture:

- `no_work_packet_authority_granted`
- `work_packet_requires_later_lock`
- `work_packet_review_only`
- `work_packet_forbidden_by_this_family`

Minimum implementation lock requirement:

- `canonical_starter_lock_required`
- `later_selector_required`
- `maintainer_review_required`
- `future_family_only`
- `not_applicable`

Minimum handoff target:

- `future_implementation_slice_review`
- `future_work_packet_review`
- `future_meta_orchestrator_workflow_review`
- `future_morphic_ux_projection_review`
- `future_direct_oai_harness_review`
- `future_general_digital_artifact_projection_review`
- `future_product_review`
- `future_graph_memory_review`
- `future_family_review`
- `deferred_no_selection`

Minimum handoff subject horizon:

- `implementation_spec_package`
- `code_implementation_spec`
- `schema_fixture_test_spec`
- `docs_support_spec`
- `ux_projection_spec`
- `provider_capability_profile_spec`
- `workflow_orchestrator_spec`
- `general_artifact_projection_pressure`
- `product_authority_gap`
- `graph_memory_pressure`

Minimum execution posture:

- `no_execution_performed_by_v83`
- `execution_requires_later_lock`
- `execution_forbidden_by_this_family`

Minimum meta-orchestrator runtime posture:

- `no_meta_orchestrator_runtime_performed_by_v83`
- `workflow_transition_review_only`
- `runtime_requires_later_family`
- `not_applicable`

## Validation Requirements

`V83-C` should enforce:

- every projection packet references known `V83-A` intent rows and `V83-B`
  edge / obligation / drift rows;
- model / agent generated projection packets carry non-empty projection
  provenance rows with prompt context, actor/profile refs, input intent refs,
  and candidate-only non-authority posture;
- projection packets include checklist rows and quality gates before they can
  be marked ready for later implementation slice review;
- ready projection packets cannot hide blocking drift rows;
- projection packets with nonblocking warnings carry those warnings explicitly;
- each implementation spec row references known artifact obligations;
- target surface refs must be bounded and concrete, not broad globs;
- acceptance evidence requirements must point to semantic preservation refs or
  explicit gaps;
- quality gates cannot pass from tests alone without semantic edge coverage,
  source binding, and reject-fixture posture;
- handoffs remain later-review requests only;
- work-packet handoffs require `work_packet_authority_posture` and
  `implementation_lock_requirement` fields showing that later lock authority
  is still required;
- work-packet handoffs do not execute work packets;
- meta-orchestrator handoffs do not mutate workflow state;
- Morphic UX handoffs do not change UI runtime surfaces;
- direct OAI handoffs do not grant provider runtime authority;
- generalized digital-artifact projection remains future-family-only unless a
  future selector chooses it;
- family closeout alignment closes `V83` only and does not select `V84`.

## Mandatory Reject Fixtures

The `V83-C` slice should include rejects for:

- projection packet without intent contract refs;
- projection packet without edge decomposition refs;
- projection packet without obligation map refs;
- projection packet generated by model or agent with no provenance rows;
- projection packet marked ready while generated-spec provenance is missing;
- ready projection packet with carried blockers;
- implementation spec row without artifact obligation refs;
- broad target surface treated as bounded implementation spec;
- projection packet marked ready while target surfaces are broad globs;
- acceptance evidence that does not bind to semantic preservation refs or an
  explicit gap;
- quality gate passes with tests only and no semantic edge coverage;
- work-packet handoff missing canonical later-lock requirement;
- handoff marked ready to implement now;
- work-packet handoff marked executed;
- meta-orchestrator handoff marked workflow-transition-completed;
- handoff to meta-orchestrator runtime marked transition-authorized;
- Morphic UX projection handoff marked runtime UI change;
- handoff to Morphic UX marked runtime UI change authorized;
- direct OAI handoff marked provider authority granted;
- closeout selecting `V84`;
- closeout claiming code implementation, PR creation, release, product
  authorization, graph-memory authority, or recursive policy amendment.

## Reference Fixture Shape

The first `V83-C` reference fixture should include:

- one implementation-spec projection packet for the intent-to-implementation
  spec institutionalization candidate;
- implementation spec rows for source index, semantic intent contract,
  non-implementation guardrail, edge decomposition, obligation map, drift
  register, projection packet, handoff, fixture, reject fixture, and test
  coverage;
- projection provenance rows for any human/model/agent/tool-assisted
  projection candidate;
- checklist rows for source binding, non-goal preservation, authority
  boundaries, target boundedness, edge coverage, validation evidence, reject
  fixture coverage, generated-spec provenance, and future-family boundaries;
- a quality gate row that is ready for later implementation-slice review only
  when blockers are absent;
- one handoff to later implementation slice review;
- one handoff to future Morphic UX projection review as a scoped test case;
- one future-family-only handoff for generalized digital artifact projection;
- a family closeout alignment row closing `V83` only.

It should include zero:

- code edits;
- work-packet execution;
- meta-orchestrator runtime transition events;
- command execution;
- PR creation;
- product, release, graph, or later-family selection rows.
