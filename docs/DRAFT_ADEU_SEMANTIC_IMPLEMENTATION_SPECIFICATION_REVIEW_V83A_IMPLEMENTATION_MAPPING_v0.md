# Draft ADEU Semantic Implementation Specification Review V83-A Implementation Mapping v0

Status: support / slice implementation mapping for planned `V83-A`.

Authority layer: support.

This note scopes the first `V83` slice. It is not an implementation lock. The
active starter authority should come from a future canonical `vNext+233`
starter trio if this slice is selected.

Read with:

- `docs/support/arc_series_mapping/REVIEW_GPTPRO_SEMANTIC_IMPLEMENTATION_SPECIFICATION_V83_PLANNING_v0.md`

## Slice Intent

`V83-A` should create the starter schema / model / validator backbone for
source-bound semantic intent contracts. It should record intent, scope,
success horizon, non-goals, constraints, source posture, authority boundaries,
artifact-family horizon, and non-implementation guardrails before any edge
decomposition or implementation-spec projection exists.

It must not create edge decomposition rows, artifact obligation maps,
semantic drift / ambiguity registers, implementation-spec projection packets,
intent-to-work-packet handoffs, meta-orchestrator runtime, work-packet
execution, code edits, command execution, tool invocation, worker assignment,
dispatch execution, product authorization, PR creation, commit, merge,
release, graph-memory authority, recursive policy amendment, or `V84`
selection.

## Selected Starter Surfaces

`V83-A` should select only:

- `repo_semantic_intent_contract@1`
- `repo_intent_source_index@1`
- `repo_intent_non_implementation_guardrail@1`

Expected files:

- `packages/adeu_repo_description/src/adeu_repo_description/semantic_implementation_spec.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/schema/repo_semantic_intent_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_intent_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_intent_non_implementation_guardrail.v1.json`
- `spec/repo_semantic_intent_contract.schema.json`
- `spec/repo_intent_source_index.schema.json`
- `spec/repo_intent_non_implementation_guardrail.schema.json`
- `packages/adeu_repo_description/tests/test_semantic_implementation_spec_v83a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus233/repo_semantic_intent_contract_v233_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus233/repo_intent_source_index_v233_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus233/repo_intent_non_implementation_guardrail_v233_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus233/repo_semantic_implementation_spec_v233_reject_*.json`

## Source Basis

The starter should consume concrete source rows for:

- released `V82` closeout evidence:
  - `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v232/evidence_inputs/v82_family_closeout_alignment_v232.json`
  - `artifacts/agent_harness/v232/evidence_inputs/v82c_corpus_ingestion_review_closeout_evidence_v232.json`
- combined support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_COMBINED_DOGFOOD_TEST_v0.json`
- support doctrine:
  - `docs/support/morphic_ux. v2.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
- external local support docs:
  - `/home/rose/work/LexLattice/codex-review-shell-direct/docs/META_ORCHESTRATOR_LOOP_ODEU_SPEC.md`
  - `/home/rose/work/LexLattice/codex-review-shell-direct/docs/OAI_CODEX_UPSTREAM_ODEU_PROFILE.md`

Support and external docs can contextualize `V83-A`; they cannot be the only
eligibility sources. Missing expected sources should be explicit absence rows,
not reconstructed from prose memory, model preference, or uncommitted
transcript.

## Minimum Row Fields

`repo_intent_source_index@1` should include:

- `source_rows`
  - `source_ref`
  - `source_kind`
  - `authority_layer`
  - `source_status`
  - `source_presence_posture`
  - `intent_source_role`
  - `source_horizon`
- `source_currentness`
- `source_scope_posture`
- `source_import_posture`
- `generation_posture`
- `model_agent_authority_posture`
- `limitation_note`

Minimum `intent_source_role` values:

- `v82_closeout_source`
- `v82_summary_source`
- `v82_handoff_source`
- `combined_dogfood_source`
- `operator_intent_source`
- `repo_planning_source`
- `repo_architecture_source`
- `repo_support_doctrine_source`
- `morphic_ux_support_source`
- `external_meta_orchestrator_support_source`
- `external_oai_profile_support_source`
- `model_generated_spec_candidate_source`
- `agent_generated_spec_candidate_source`
- `reviewer_amendment_source`
- `operator_revision_source`
- `prompt_context_source`
- `model_or_agent_profile_source`
- `implementation_prior_artifact_source`
- `implementation_context_source`
- `authority_boundary_source`
- `non_goal_source`
- `explicit_absence_marker`
- `support_process_context`

Minimum `source_import_posture` values:

- `repo_owned_source`
- `external_support_source`
- `external_import_required_before_lock`
- `support_context_only`
- `absence_marker`
- `unknown_needs_review`

Minimum `generation_posture` values:

- `not_generated`
- `generated_for_review_only`
- `generated_from_bounded_context`
- `generated_from_unbounded_context`
- `generated_source_missing`
- `generated_source_unknown`

Minimum `model_agent_authority_posture` values:

- `no_model_authority`
- `model_output_as_candidate_only`
- `agent_output_as_candidate_only`
- `reviewer_output_as_review_only`
- `authority_requires_later_lock`

`repo_semantic_intent_contract@1` should include:

- `intent_contract_rows`
  - `intent_contract_ref`
  - `intent_version_ref`
  - `intent_revision_posture`
  - `candidate_ref`
  - `source_refs`
  - `intent_title`
  - `intent_statement`
  - `artifact_family_horizon`
  - `implementation_surface_horizon`
  - `success_horizon`
  - `success_horizon_kind`
  - `intent_recordability_posture`
  - `semantic_spec_eligibility_posture`
  - `semantic_closure_posture`
  - `scope_posture`
  - `non_goal_refs`
  - `semantic_constraint_refs`
  - `operational_constraint_refs`
  - `authority_boundary_refs`
  - `expected_edge_classes`
  - `guardrail_refs`
  - `odeu_lanes`
  - `limitation_note`

Minimum `semantic_closure_posture` values:

- `closure_not_claimed`
- `closure_candidate_for_review`
- `closure_blocked_by_missing_source`
- `closure_blocked_by_missing_scope_boundary`
- `closure_blocked_by_missing_non_goals`
- `closure_blocked_by_missing_authority_boundary`
- `closure_blocked_by_missing_success_horizon`
- `closure_blocked_by_generated_spec_provenance_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum `intent_recordability_posture` values:

- `recordable_from_concrete_intent_source`
- `recordable_from_operator_turn_with_absence_markers`
- `recordable_from_support_context_only`
- `recordable_from_generated_spec_candidate`
- `not_recordable_missing_intent_source`

Minimum `semantic_spec_eligibility_posture` values:

- `eligible_for_semantic_spec_review`
- `blocked_by_missing_intent_source`
- `blocked_by_missing_non_goals`
- `blocked_by_missing_authority_boundary`
- `blocked_by_missing_success_horizon`
- `blocked_by_external_source_import_gap`
- `blocked_by_generated_spec_provenance_gap`
- `blocked_by_ambiguous_artifact_horizon`
- `future_family_only`
- `rejected_out_of_scope`

Minimum `success_horizon_kind` values:

- `schema_shape_success`
- `validator_behavior_success`
- `fixture_accept_reject_success`
- `workflow_transition_success`
- `ux_projection_success`
- `provider_capability_profile_success`
- `documentation_alignment_success`
- `implementation_packet_success`
- `future_family_only`

Minimum `artifact_family_horizon` values:

- `repo_code_implementation_spec`
- `repo_schema_implementation_spec`
- `repo_fixture_test_spec`
- `repo_docs_support_spec`
- `morphic_ux_projection_spec`
- `direct_oai_harness_spec`
- `workflow_orchestrator_spec`
- `general_digital_artifact_projection_future_family`
- `future_family_only`

`repo_intent_non_implementation_guardrail@1` should include:

- `guardrail_rows`
  - `guardrail_ref`
  - `candidate_ref`
  - `source_refs`
  - `forbidden_implementation_actions`
  - `forbidden_runtime_actions`
  - `forbidden_downstream_authority`
  - `required_later_authority_refs`
  - `non_implementation_posture`
  - `non_execution_posture`
  - `non_dispatch_posture`
  - `non_release_posture`
  - `limitation_note`

## Validation Requirements

`V83-A` should enforce:

- every intent contract references known source rows;
- every eligible intent contract cites released `V82` substrate and at least
  one concrete intent source;
- every eligible intent contract has `semantic_spec_eligibility_posture =
  eligible_for_semantic_spec_review`, non-empty source-bound `non_goal_refs`,
  non-empty `authority_boundary_refs`, and concrete `success_horizon_kind`;
- support-only rows cannot make an intent eligible;
- generated model or agent rows, when present, remain candidate-only and cite
  bounded prompt / profile / source context before they can support review;
- external local docs must be marked as external support sources or import gaps,
  not repo-owned lock authority;
- non-goal refs and authority-boundary refs are required for eligible rows;
- artifact-family horizon cannot be ambiguous for eligible rows;
- Morphic UX support examples cannot become general implementation contracts;
- direct OAI support profiles cannot become runtime capability authority;
- generated implementation-spec candidates cannot become semantic contracts,
  implementation truth, code correctness, or executable work packets;
- success horizon cannot be defined only as "passes tests";
- guardrail rows have non-empty forbidden implementation actions, forbidden
  runtime actions, and forbidden downstream authority;
- no starter row may include edge decomposition, artifact obligations, drift
  registers, projection packets, work-packet handoffs, implementation, command
  execution, dispatch, product, release, graph, or later-family selection.

## Mandatory Reject Fixtures

The `V83-A` starter should include rejects for:

- intent contract without source refs;
- eligible intent contract sourced only by support docs;
- external local doc treated as repo lock authority;
- model-generated implementation spec marked eligible without prompt, context,
  profile, or source provenance;
- generated implementation spec treated as implementation truth;
- Morphic UX example treated as universal implementation law;
- direct OAI inferred profile treated as runtime authority;
- operator preference with no non-goal refs;
- success horizon defined only as passing tests;
- non-goals represented only in prose without source-bound refs;
- operator intent source missing while the intent is marked eligible;
- support-only context marked as semantic closure;
- intent row with ambiguous artifact-family horizon marked eligible;
- guardrail with empty forbidden implementation actions;
- guardrail with empty forbidden runtime actions;
- starter row containing edge decomposition refs;
- starter row containing projection packet refs;
- row claiming code implementation, command execution, PR creation, release, or
  product authorization.

## Reference Fixture Shape

The first reference fixture should include:

- one source index with released `V82` closeout, combined dogfood, Morphic UX
  support, external meta-orchestrator support, external OAI profile support,
  operator-intent, non-goal, authority-boundary, and generated/model-spec
  source rows only if concretely present;
- one eligible semantic intent contract for institutionalizing
  intent-to-implementation specification review;
- one future-family-only row for generalized digital artifact projection;
- one blocked or context-only Morphic UX or direct OAI support-pressure row if
  those support sources are absent or import-only;
- one non-implementation guardrail with explicit forbidden implementation,
  runtime, dispatch, product, release, graph, and recursive-policy actions.

It should include zero:

- `V83-B` rows;
- `V83-C` rows;
- code implementation rows;
- work-packet execution rows;
- command execution rows;
- product, release, graph, or later-family selection rows.
