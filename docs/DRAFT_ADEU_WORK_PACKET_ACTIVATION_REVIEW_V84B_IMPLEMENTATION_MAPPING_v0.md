# Draft ADEU Work Packet Activation Review V84-B Implementation Mapping v0

Status: support / slice implementation mapping for planned `V84-B`.

Authority layer: support.

This note scopes the second `V84` slice. It is not an implementation lock.
`V84-B` should become active only after `V84-A` closes and a future canonical
starter trio selects it.

## Slice Intent

`V84-B` should extend released `V84-A` activation-review request, source, and
guardrail rows with bounded work-packet scope contracts, implementation
target-surface boundaries, validation evidence plans, and activation exception
posture. It should make the implementation-lock package reviewable before any
readiness summary or handoff exists.

It must not create readiness summaries, post-activation handoffs, work-packet
execution, code edits, command execution, tool invocation, worker dispatch,
PR creation, commit, merge, release, product authorization, graph-memory
authority, recursive policy amendment, or `V85` selection.

## Selected Surfaces

`V84-B` should select only:

- `repo_work_packet_scope_contract@1`
- `repo_implementation_target_surface_boundary@1`
- `repo_work_packet_validation_evidence_plan@1`
- `repo_work_packet_activation_exception_register@1`

Expected files:

- updates to `packages/adeu_repo_description/src/adeu_repo_description/work_packet_activation_review.py`
- schema and mirror schema files for the four selected surfaces
- `packages/adeu_repo_description/tests/test_work_packet_activation_review_v84b.py`
- `apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_scope_contract_v237_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus237/repo_implementation_target_surface_boundary_v237_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_validation_evidence_plan_v237_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_activation_exception_register_v237_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_activation_v237_reject_*.json`

## Consumed Substrate

`V84-B` should consume released `V84-A` rows:

- `repo_work_packet_activation_review_request@1`
- `repo_work_packet_activation_source_index@1`
- `repo_work_packet_activation_non_execution_guardrail@1`

It should also preserve refs back to released `V83-C` projection packets,
quality gates, implementation spec rows, and handoffs. It should not create a
parallel activation universe.

## Minimum Row Fields

`repo_work_packet_scope_contract@1` should include:

- `scope_contract_ref`
- `activation_package_ref`
- `activation_request_refs`
- `projection_packet_refs`
- `implementation_spec_refs`
- `candidate_ref`
- `source_refs`
- `work_packet_kind`
- `scope_statement`
- `in_scope_artifact_refs`
- `out_of_scope_artifact_refs`
- `target_boundary_refs`
- `validation_plan_refs`
- `canonical_lock_requirement_refs`
- `activation_package_lineage_refs`
- `scope_completeness_posture`
- `activation_review_posture`
- `work_packet_execution_posture`
- `implementation_execution_posture`
- `guardrail_refs`
- `limitation_note`

`repo_implementation_target_surface_boundary@1` should include:

- `target_boundary_ref`
- `activation_package_ref`
- `scope_contract_refs`
- `activation_request_refs`
- `candidate_ref`
- `source_refs`
- `target_surface_kind`
- `target_surface_refs`
- `target_resolution_kind`
- `target_currentness_posture`
- `target_mutability_review_posture`
- `target_access_role_rows`
- `allowed_target_review_actions`
- `forbidden_target_mutation_actions`
- `ownership_or_authority_refs`
- `boundary_posture`
- `guardrail_refs`
- `limitation_note`

Minimum target access role row fields:

- `target_access_role_ref`
- `target_surface_refs`
- `target_access_role`
- `source_refs`
- `target_mutability_review_posture`
- `in_scope_counting_posture`
- `limitation_note`

`repo_work_packet_validation_evidence_plan@1` should include:

- `validation_plan_ref`
- `activation_package_ref`
- `scope_contract_refs`
- `activation_request_refs`
- `candidate_ref`
- `source_refs`
- `semantic_edge_refs`
- `artifact_obligation_refs`
- `implementation_spec_refs`
- `validation_evidence_rows`
- `validation_matrix_rows`
- `required_positive_evidence_posture`
- `required_reject_evidence_posture`
- `manual_review_posture`
- `tool_run_posture`
- `validation_plan_posture`
- `tests_not_truth_guardrail`
- `work_packet_execution_posture`
- `implementation_execution_posture`
- `guardrail_refs`
- `limitation_note`

Minimum validation evidence row fields:

- `validation_evidence_ref`
- `semantic_edge_refs`
- `artifact_obligation_refs`
- `implementation_spec_refs`
- `evidence_kind`
- `required_artifact_refs`
- `required_execution_horizon`
- `evidence_presence_posture`
- `acceptance_not_truth_guardrail`
- `limitation_note`

Minimum validation matrix row fields:

- `validation_matrix_ref`
- `semantic_edge_refs`
- `artifact_obligation_refs`
- `implementation_spec_refs`
- `target_boundary_refs`
- `evidence_kind`
- `positive_evidence_requirement`
- `reject_evidence_requirement`
- `regression_evidence_requirement`
- `manual_review_requirement`
- `tool_applicability_posture`
- `execution_required_later`
- `acceptance_not_truth_guardrail`
- `limitation_note`

`repo_work_packet_activation_exception_register@1` should include:

- `exception_register_ref`
- `activation_package_ref`
- `activation_request_refs`
- `scope_contract_refs`
- `target_boundary_refs`
- `validation_plan_refs`
- `candidate_ref`
- `source_refs`
- `exception_rows`
- `blocking_posture`
- `required_next_surface`
- `guardrail_refs`
- `limitation_note`

Minimum exception row fields:

- `exception_ref`
- `exception_kind`
- `source_refs`
- `related_scope_refs`
- `related_target_refs`
- `related_validation_refs`
- `related_drift_refs`
- `blocking_posture`
- `visibility_posture`
- `required_resolution_horizon`
- `limitation_note`

Canonical lock requirement rows should include:

- `canonical_lock_requirement_ref`
- `activation_package_ref`
- `required_lock_kind`
- `required_lock_inputs`
- `required_lock_guardrails`
- `required_stop_gate_refs`
- `required_assessment_refs`
- `required_closeout_refs`
- `required_later_authority_refs`
- `lock_not_created_by_v84`
- `limitation_note`

Activation package lineage rows should include:

- `activation_package_lineage_ref`
- `activation_package_ref`
- `candidate_ref`
- `projection_packet_refs`
- `quality_gate_refs`
- `implementation_spec_refs`
- `scope_contract_refs`
- `target_boundary_refs`
- `validation_plan_refs`
- `lineage_posture`
- `limitation_note`

## Vocabulary

Minimum work packet kind:

- `schema_model_fixture_test_slice`
- `docs_support_slice`
- `morphic_ux_projection_slice`
- `direct_oai_harness_slice`
- `meta_orchestrator_workflow_slice`
- `product_future_family_slice`
- `graph_memory_future_family_slice`
- `future_family_only`

Minimum target resolution kind:

- `concrete_file_ref`
- `concrete_schema_ref`
- `concrete_fixture_ref`
- `concrete_test_ref`
- `concrete_doc_ref`
- `bounded_directory_with_child_refs`
- `support_artifact_ref`
- `external_support_ref`
- `no_target_boundary`

Minimum target access role:

- `read_dependency`
- `prospective_write_target_for_later_lock`
- `validation_target`
- `generated_artifact_target`
- `forbidden_target`
- `context_only`

Minimum validation matrix evidence kind:

- `schema_export_check`
- `model_shape_check`
- `validator_acceptance_check`
- `validator_reject_check`
- `fixture_positive_case`
- `fixture_negative_case`
- `unit_test_requirement`
- `integration_test_requirement`
- `doc_alignment_review`
- `semantic_edge_review`
- `manual_reviewer_check`
- `tool_run_review_only`
- `future_family_review`

Minimum scope completeness posture:

- `complete_for_activation_review_only`
- `incomplete_for_review`
- `blocked_by_missing_projection_packet`
- `blocked_by_unbounded_target_surface`
- `blocked_by_missing_validation_plan`
- `blocked_by_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum validation plan posture:

- `plan_complete_for_review_only`
- `plan_incomplete_for_review`
- `blocked_by_missing_semantic_edges`
- `blocked_by_missing_artifact_obligations`
- `blocked_by_missing_positive_evidence`
- `blocked_by_missing_reject_evidence`
- `blocked_by_tests_as_truth_gap`
- `future_family_only`

Minimum exception kind:

- `missing_released_projection_packet`
- `missing_quality_gate`
- `carried_semantic_drift_blocker`
- `generated_spec_provenance_gap`
- `unbounded_target_surface`
- `target_glob_without_child_refs`
- `missing_validation_plan`
- `missing_positive_evidence_requirement`
- `missing_reject_evidence_requirement`
- `operator_confirmation_as_authority`
- `implementation_authority_gap`
- `runtime_authority_gap`
- `product_authority_gap`
- `release_authority_gap`
- `graph_memory_authority_gap`
- `unknown_needs_review`
- `activation_package_lineage_mismatch`
- `scope_target_validation_candidate_mismatch`
- `canonical_lock_requirement_missing_or_untyped`
- `read_set_write_set_collision`
- `forbidden_target_included_in_scope`
- `generated_candidate_without_review_provenance`
- `quality_gate_ready_but_blockers_carried`
- `validation_plan_not_edge_complete`
- `validation_plan_not_obligation_complete`
- `later_family_boundary_unclear`

## Validation Requirements

`V84-B` should enforce:

- every scope contract references known released `V84-A` request rows;
- every scope, target, validation, exception, canonical-lock, and lineage row
  uses the same `activation_package_ref`, `candidate_ref`, and released
  `V83-C` projection lineage when summarized together;
- every target boundary references known scope contracts or activation
  requests;
- target globs are discovery context only and cannot become target boundaries;
- bounded directories require concrete child refs;
- `bounded_directory_with_child_refs` cannot be bounded without concrete child
  target refs;
- prospective write targets must carry mutation-requires-later-lock posture;
- forbidden targets cannot appear in in-scope artifact refs;
- context-only targets cannot count as bounded implementation scope;
- validation evidence plans reference known semantic edges, artifact
  obligations, and implementation spec rows;
- every required semantic edge has at least one validation matrix row;
- every artifact obligation has positive and reject evidence posture;
- validation plans do not execute tests or claim semantic truth;
- tool runs cannot satisfy semantic preservation without edge-bound
  interpretation;
- canonical lock requirements remain requirements and do not create locks;
- exception rows cannot be marked resolved by `V84-B`;
- product, release, graph, runtime, and recursive-policy gaps remain blockers
  or future-family-only;
- every row carries no work-packet execution and no implementation posture.

## Mandatory Rejects

Reject fixtures should cover:

- scope contract without released `V84-A` request refs;
- target boundary with only a broad package or repo glob;
- bounded directory marked ready without concrete child refs;
- read dependency counted as prospective write scope;
- forbidden target included in in-scope artifact refs;
- validation plan with tests but no semantic edge refs;
- validation plan not complete across semantic edges or artifact obligations;
- validation plan treating passing tests as semantic truth;
- package-lineage mismatch across scope, target, validation, and exception
  rows;
- missing or untyped canonical lock requirement;
- exception register resolving blockers by prose;
- operator confirmation requirement treated as implementation authority;
- Morphic UX target boundary treated as runtime UI mutation authority;
- direct OAI target boundary treated as provider runtime authority;
- PR, commit, merge, release, or product authority claimed by `V84-B`.
