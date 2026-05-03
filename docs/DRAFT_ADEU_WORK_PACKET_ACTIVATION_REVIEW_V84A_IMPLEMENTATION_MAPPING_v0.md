# Draft ADEU Work Packet Activation Review V84-A Implementation Mapping v0

Status: support / slice implementation mapping for planned `V84-A`.

Authority layer: support.

This note scopes the first `V84` slice. It is not an implementation lock. The
active starter authority should come from a future canonical `vNext+236`
starter trio if this slice is selected.

## Slice Intent

`V84-A` should create the starter schema / model / validator backbone for
source-bound implementation work-packet activation-review requests. It should
record request source posture, released `V83-C` projection / quality-gate /
handoff refs, target and validation posture, canonical later-lock
requirements, and non-execution guardrails before any scope contract,
target-boundary, validation plan, readiness summary, handoff, or
implementation exists.

It must not create work-packet scope contracts, target-surface boundary rows,
validation evidence plans, activation exception registers, readiness
summaries, post-activation handoffs, implementation work, code edits, command
execution, tool invocation, worker assignment, dispatch execution, PR
creation, commit, merge, release, product authorization, graph-memory
authority, recursive policy amendment, or `V85` selection.

## Selected Starter Surfaces

`V84-A` should select only:

- `repo_work_packet_activation_review_request@1`
- `repo_work_packet_activation_source_index@1`
- `repo_work_packet_activation_non_execution_guardrail@1`

Expected files:

- `packages/adeu_repo_description/src/adeu_repo_description/work_packet_activation_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/schema/repo_work_packet_activation_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_work_packet_activation_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_work_packet_activation_non_execution_guardrail.v1.json`
- `spec/repo_work_packet_activation_review_request.schema.json`
- `spec/repo_work_packet_activation_source_index.schema.json`
- `spec/repo_work_packet_activation_non_execution_guardrail.schema.json`
- `packages/adeu_repo_description/tests/test_work_packet_activation_review_v84a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus236/repo_work_packet_activation_review_request_v236_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus236/repo_work_packet_activation_source_index_v236_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus236/repo_work_packet_activation_non_execution_guardrail_v236_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus236/repo_work_packet_activation_v236_reject_*.json`

## Source Basis

The starter should consume concrete source rows for:

- released `V83` closeout evidence:
  - `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v235/evidence_inputs/v83_family_closeout_alignment_v235.json`
  - `artifacts/agent_harness/v235/evidence_inputs/v83c_semantic_projection_closeout_evidence_v235.json`
- released `V83-C` fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus235/repo_implementation_spec_projection_packet_v235_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus235/repo_intent_to_work_packet_handoff_v235_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus235/repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json`
- combined support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.json`
- support doctrine:
  - `docs/support/morphic_ux. v2.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`

Support context can contextualize `V84-A`; it cannot be the only eligibility
source. Missing expected sources should be explicit absence rows, not
reconstructed from prose memory, model preference, or uncommitted transcript.

## Minimum Row Fields

`repo_work_packet_activation_source_index@1` should include:

- `source_rows`
  - `source_ref`
  - `source_kind`
  - `authority_layer`
  - `source_status`
  - `source_presence_posture`
  - `activation_source_role`
  - `source_horizon`
  - `source_currentness`
  - `source_scope_posture`
  - `source_import_posture`
  - `projection_authority_posture`
  - `work_packet_authority_posture`
  - `limitation_note`

Minimum `activation_source_role` values:

- `v83_projection_packet_source`
- `v83_quality_gate_source`
- `v83_implementation_spec_source`
- `v83_handoff_source`
- `v83_closeout_source`
- `semantic_intent_contract_source`
- `semantic_edge_source`
- `artifact_obligation_source`
- `drift_or_ambiguity_source`
- `non_implementation_guardrail_source`
- `combined_dogfood_source`
- `repo_support_doctrine_source`
- `morphic_ux_support_context`
- `direct_oai_support_context`
- `meta_orchestrator_support_context`
- `operator_activation_request_source`
- `generated_work_packet_candidate_source`
- `generated_work_packet_candidate_review_source`
- `canonical_lock_requirement_source`
- `target_surface_context`
- `target_boundary_context_source`
- `read_dependency_context_source`
- `prospective_write_target_context_source`
- `forbidden_target_context_source`
- `validation_evidence_context`
- `authority_boundary_source`
- `explicit_absence_marker`
- `support_process_context`

Minimum `projection_authority_posture` values:

- `projection_source_for_review_only`
- `quality_gate_source_for_review_only`
- `projection_missing`
- `projection_blocked_by_carried_drift`
- `projection_not_authority`
- `unknown_needs_review`

Minimum `work_packet_authority_posture` values:

- `no_work_packet_authority_granted`
- `work_packet_requires_later_lock`
- `work_packet_review_only`
- `work_packet_forbidden_by_this_family`

`repo_work_packet_activation_review_request@1` should include:

- `activation_request_rows`
  - `activation_request_ref`
  - `activation_package_ref`
  - `candidate_ref`
  - `source_refs`
  - `projection_packet_refs`
  - `quality_gate_refs`
  - `implementation_spec_refs`
  - `intent_contract_refs`
  - `edge_decomposition_refs`
  - `artifact_obligation_refs`
  - `drift_register_refs`
  - `handoff_refs`
  - `requested_work_packet_horizon`
  - `requested_activation_review_horizon`
  - `activation_request_recordability_posture`
  - `activation_review_eligibility_posture`
  - `target_surface_posture`
  - `validation_evidence_posture`
  - `canonical_lock_requirement`
  - `canonical_lock_requirement_refs`
  - `generated_candidate_refs`
  - `activation_authority_posture`
  - `implementation_lock_status`
  - `target_family_boundary_posture`
  - `carried_blocker_refs`
  - `carried_warning_refs`
  - `guardrail_refs`
  - `activation_execution_posture`
  - `implementation_execution_posture`
  - `work_packet_authority_posture`
  - `limitation_note`

Minimum `activation_request_recordability_posture` values:

- `recordable_from_released_v83_projection`
- `recordable_from_released_v83_handoff`
- `recordable_from_operator_request_with_absence_markers`
- `recordable_from_support_context_only`
- `not_recordable_missing_projection_source`

Minimum `activation_review_eligibility_posture` values:

- `eligible_for_work_packet_activation_review`
- `request_recorded_for_review_only`
- `blocked_by_missing_projection_packet`
- `blocked_by_missing_quality_gate`
- `blocked_by_missing_handoff`
- `blocked_by_carried_semantic_drift`
- `blocked_by_unbounded_target_surface`
- `blocked_by_missing_validation_evidence`
- `blocked_by_missing_canonical_lock_requirement`
- `blocked_by_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum `activation_authority_posture` values:

- `no_activation_authority_granted_by_v84`
- `activation_requires_later_canonical_lock`
- `activation_forbidden_by_this_family`

Minimum `implementation_lock_status` values:

- `no_implementation_lock_created_by_v84`
- `later_implementation_lock_review_requested`
- `later_selector_required`
- `deferred_no_selection`

Minimum `target_family_boundary_posture` values:

- `repo_description_implementation_allowed_for_later_lock_review`
- `morphic_ux_requires_runtime_ui_authority_review`
- `direct_oai_requires_provider_runtime_authority_review`
- `meta_orchestrator_requires_workflow_runtime_authority_review`
- `product_requires_product_authority_review`
- `graph_requires_graph_memory_authority_review`
- `future_family_only`

Minimum requested work packet horizon:

- `repo_schema_or_model_implementation_slice`
- `repo_fixture_or_test_implementation_slice`
- `repo_doc_or_support_artifact_slice`
- `morphic_ux_projection_implementation_review`
- `direct_oai_harness_implementation_review`
- `meta_orchestrator_workflow_activation_review`
- `product_work_future_family`
- `graph_memory_future_family`
- `future_family_only`

`repo_work_packet_activation_non_execution_guardrail@1` should include:

- `guardrail_rows`
  - `guardrail_ref`
  - `candidate_ref`
  - `source_refs`
  - `forbidden_implementation_actions`
  - `forbidden_runtime_actions`
  - `forbidden_downstream_authority`
  - `required_later_authority_refs`
  - `activation_execution_posture`
  - `work_packet_execution_posture`
  - `implementation_execution_posture`
  - `target_mutation_posture`
  - `pr_commit_release_posture`
  - `activation_authority_posture`
  - `implementation_lock_status`
  - `limitation_note`

Optional generated work-packet candidate rows should include:

- `generated_candidate_ref`
- `source_refs`
- `generating_actor_kind`
- `prompt_context_refs`
- `model_or_agent_profile_refs`
- `input_projection_packet_refs`
- `input_quality_gate_refs`
- `generated_output_refs`
- `reviewer_amendment_refs`
- `generation_scope_posture`
- `candidate_authority_posture`
- `limitation_note`

Minimum `candidate_authority_posture` values:

- `candidate_only`
- `candidate_blocked_by_missing_v83_projection`
- `candidate_blocked_by_missing_quality_gate`
- `candidate_blocked_by_unbounded_target`
- `candidate_blocked_by_missing_review`

## Validation Requirements

`V84-A` should enforce:

- every activation-review request references known activation source rows;
- every eligible activation-review request carries a stable
  `activation_package_ref`;
- every eligible activation-review request cites released `V83-C` projection
  packet or handoff rows;
- every eligible row cites a `V83-C` quality gate or explicit no-blocker
  posture;
- every eligible row cites intent contract refs, edge decomposition refs,
  artifact obligation refs, guardrail refs, and handoff refs;
- support context, dogfood context, or operator desire cannot be the only
  eligibility source;
- generated work-packet candidates are candidate-only and cannot grant
  activation authority;
- generated work-packet candidates require prompt/context/profile/projection
  and quality-gate provenance before they may be referenced by an eligible
  request;
- broad target surfaces or globs cannot become bounded activation targets;
- carried semantic drift blockers prevent eligibility unless the row is
  routed to later blocker settlement review;
- validation evidence posture must be explicit, edge-bound, and review-only;
- canonical later-lock requirement must be present and typed for any eligible
  request;
- `activation_authority_posture` must not grant activation authority;
- `implementation_lock_status` must not claim a lock was created by `V84-A`;
- Morphic UX, direct OAI, meta-orchestrator, product, graph, and future-family
  rows must carry target-specific later authority posture;
- guardrail rows must forbid implementation, command execution, tool
  invocation, target mutation, PR creation, commit, merge, release, product
  authority, graph authority, recursive policy amendment, and `V85` selection.

## Reference Fixture Intent

The first reference fixture should include:

- one source-bound semantic implementation-spec workflow request eligible for
  activation review only;
- one Morphic UX projection row carried as warning-ready or future-family
  activation-review pressure;
- one direct OAI / meta-orchestrator support row carried as workflow-review
  pressure, not runtime behavior;
- stable `activation_package_ref` values on request rows;
- typed canonical later-lock requirements;
- source rows for released `V83-C` projection, handoff, closeout, and dogfood
  artifacts;
- non-execution guardrails for each candidate;
- zero scope contracts, target-boundary rows, validation plans, exception
  registers, summaries, handoffs, implementation work, commands, tool
  invocations, PRs, commits, releases, product authority, graph authority, or
  `V85` selection.

## Mandatory Rejects

Reject fixtures should cover:

- unknown candidate refs;
- request without released `V83-C` source refs;
- eligible request with no `activation_package_ref`;
- support-only source marked eligible;
- generated work-packet candidate marked authoritative;
- generated work-packet candidate without provenance marked eligible;
- missing quality gate but eligible posture;
- carried blocker hidden by eligible posture;
- broad target surface or glob treated as bounded target;
- validation evidence posture omitted, test-only, or treated as executed
  validation;
- missing or untyped canonical lock requirement;
- target family boundary posture set to `future_family_only` while request is
  marked eligible;
- handoff marked "ready to implement now";
- command execution, tool invocation, PR, commit, merge, release, product,
  graph, recursive-policy, or `V85` authority claimed by `V84-A`.
