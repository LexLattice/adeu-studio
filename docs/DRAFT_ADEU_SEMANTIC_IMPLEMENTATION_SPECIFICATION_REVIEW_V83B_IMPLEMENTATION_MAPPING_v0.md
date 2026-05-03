# Draft ADEU Semantic Implementation Specification Review V83-B Implementation Mapping v0

Status: support / slice implementation mapping for planned `V83-B`.

Authority layer: support.

This note scopes the second `V83` slice. It is not an implementation lock.
`V83-B` should become active only after `V83-A` closes and a future canonical
starter trio selects it.

Read with:

- `docs/support/arc_series_mapping/REVIEW_GPTPRO_SEMANTIC_IMPLEMENTATION_SPECIFICATION_V83_PLANNING_v0.md`

## Slice Intent

`V83-B` should extend released `V83-A` intent / source / guardrail rows with
semantic edge decomposition, artifact obligation mapping, and semantic drift /
ambiguity posture. It should make the edges of intent visible before an
implementation-spec projection packet exists.

It must not create implementation-spec projection packets,
intent-to-work-packet handoffs, work-packet execution, code edits, command
execution, worker dispatch, product authorization, PR creation, commit, merge,
release, graph-memory authority, recursive policy amendment, or `V84`
selection.

## Selected Surfaces

`V83-B` should select only:

- `repo_intent_edge_decomposition@1`
- `repo_artifact_obligation_map@1`
- `repo_semantic_drift_ambiguity_register@1`

Expected files:

- updates to `packages/adeu_repo_description/src/adeu_repo_description/semantic_implementation_spec.py`
- schema and mirror schema files for the three selected surfaces
- `packages/adeu_repo_description/tests/test_semantic_implementation_spec_v83b.py`
- `apps/api/fixtures/repo_description/vnext_plus234/repo_intent_edge_decomposition_v234_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus234/repo_artifact_obligation_map_v234_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus234/repo_semantic_drift_ambiguity_register_v234_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus234/repo_semantic_implementation_spec_v234_reject_*.json`

## Consumed Substrate

`V83-B` should consume released `V83-A` rows:

- `repo_semantic_intent_contract@1`
- `repo_intent_source_index@1`
- `repo_intent_non_implementation_guardrail@1`

It should not create a parallel intent universe. Every edge decomposition,
artifact obligation, and drift / ambiguity row should reference known released
intent, source, and guardrail rows.

## Minimum Row Fields

`repo_intent_edge_decomposition@1` should include:

- `edge_decomposition_ref`
- `intent_contract_refs`
- `candidate_ref`
- `source_refs`
- `semantic_object_rows`
- `semantic_relation_rows`
- `constraint_rows`
- `non_goal_rows`
- `authority_edge_rows`
- `validation_need_rows`
- `edge_decomposition_posture`
- `semantic_closure_posture`
- `guardrail_refs`
- `limitation_note`

Minimum semantic object row fields:

- `semantic_object_ref`
- `object_kind`
- `object_label`
- `source_refs`
- `anticipated_artifact_kind_refs`
- `truth_posture`
- `mutability_posture`
- `authority_posture`
- `limitation_note`

Minimum semantic relation row fields:

- `semantic_relation_ref`
- `relation_kind`
- `from_object_ref`
- `to_object_ref`
- `source_refs`
- `preservation_requirement`
- `validation_need_refs`
- `limitation_note`

Minimum validation need row fields:

- `validation_need_ref`
- `semantic_edge_refs`
- `validation_kind`
- `required_evidence_kind`
- `required_positive_fixture_posture`
- `required_reject_fixture_posture`
- `manual_review_required`
- `tool_applicability_posture`
- `acceptance_not_truth_guardrail`
- `limitation_note`

`repo_artifact_obligation_map@1` should include:

- `obligation_map_ref`
- `intent_contract_refs`
- `edge_decomposition_refs`
- `candidate_ref`
- `source_refs`
- `artifact_obligation_rows`
- `coverage_posture`
- `implementation_readiness_posture`
- `guardrail_refs`
- `limitation_note`

Minimum artifact obligation row fields:

- `artifact_obligation_ref`
- `semantic_edge_refs`
- `artifact_kind`
- `target_surface_refs`
- `required_change_posture`
- `required_fixture_posture`
- `required_test_posture`
- `required_doc_posture`
- `acceptance_evidence_requirements`
- `non_implementation_posture`
- `limitation_note`

Minimum acceptance evidence requirement row fields:

- `evidence_requirement_ref`
- `semantic_edge_refs`
- `validation_need_refs`
- `evidence_kind`
- `required_artifact_refs`
- `non_truth_guardrail`
- `limitation_note`

`repo_semantic_drift_ambiguity_register@1` should include:

- `drift_register_ref`
- `intent_contract_refs`
- `edge_decomposition_refs`
- `obligation_map_refs`
- `candidate_ref`
- `source_refs`
- `drift_or_ambiguity_rows`
- `blocking_posture`
- `required_next_surface`
- `guardrail_refs`
- `limitation_note`

Minimum drift / ambiguity row fields:

- `drift_ref`
- `drift_kind`
- `semantic_edge_refs`
- `artifact_obligation_refs`
- `source_refs`
- `severity_posture`
- `blocking_posture`
- `required_resolution_horizon`
- `limitation_note`

## Vocabulary

Minimum object kind:

- `domain_object`
- `repo_module`
- `schema_surface`
- `fixture_surface`
- `test_surface`
- `doc_surface`
- `ux_surface`
- `workflow_surface`
- `provider_capability_surface`
- `authority_boundary`
- `non_goal`
- `future_family_surface`

Minimum relation kind:

- `requires`
- `constrains`
- `forbids`
- `preserves`
- `realizes`
- `refines`
- `conflicts_with`
- `disambiguates`
- `supersedes`
- `non_goal_of`
- `authority_requires`
- `validation_requires`
- `acceptance_requires`
- `derives_from`
- `must_remain_distinct_from`
- `hands_off_to`
- `validates`
- `blocks`
- `future_family_only`

Minimum validation kind:

- `schema_validation`
- `validator_behavior`
- `positive_fixture`
- `reject_fixture`
- `unit_test`
- `integration_test`
- `documentation_review`
- `semantic_review`
- `human_review`
- `tool_run_review`
- `future_family_review`

Minimum artifact kind:

- `code_module`
- `schema`
- `mirror_schema`
- `fixture`
- `reject_fixture`
- `test`
- `documentation`
- `support_artifact`
- `ux_projection_artifact`
- `provider_profile_artifact`
- `workflow_contract_artifact`
- `future_family_artifact`

Minimum edge decomposition posture:

- `edges_decomposed_for_review`
- `blocked_by_missing_intent_contract`
- `blocked_by_missing_source`
- `blocked_by_ambiguous_relation`
- `blocked_by_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum coverage posture:

- `obligations_cover_all_required_edges`
- `obligations_cover_with_nonblocking_warnings`
- `blocked_by_unmapped_edge`
- `blocked_by_unknown_target_surface`
- `blocked_by_missing_validation_need`
- `future_family_only`
- `rejected_out_of_scope`

Minimum implementation readiness posture:

- `not_ready_requires_projection_packet`
- `ready_for_projection_review_only`
- `blocked_by_semantic_drift`
- `blocked_by_ambiguity`
- `blocked_by_authority_gap`
- `future_family_only`

Minimum drift kind:

- `missing_source`
- `ambiguous_intent`
- `ambiguous_artifact_horizon`
- `semantic_edge_unmapped`
- `implementation_target_overbroad`
- `implementation_target_underbroad`
- `non_goal_laundering`
- `authority_boundary_laundering`
- `test_coverage_mismatch`
- `fixture_coverage_mismatch`
- `morphic_ux_scope_drift`
- `direct_oai_runtime_scope_drift`
- `workflow_orchestrator_authority_drift`
- `future_family_pressure_unclassified`

## Validation Requirements

`V83-B` should enforce:

- every edge decomposition references known released `V83-A` intent contracts;
- edge rows cannot invent intent not present in source rows;
- edge rows cannot be invented from model / agent output unless the generated
  candidate is source-bound to released `V83-A` intent refs and candidate-only
  provenance;
- artifact obligations reference known semantic edges;
- every required edge is mapped to an obligation or a visible drift /
  ambiguity row;
- broad target surfaces without bounded refs are blocked;
- tests and fixtures cannot be treated as semantic preservation unless they
  bind to specific edges;
- acceptance evidence requirements must bind to semantic edges and validation
  needs, not only to a generic passing-test signal;
- non-goals cannot be converted into implementation obligations;
- authority boundaries cannot be converted into permissions;
- Morphic UX obligations stay scoped to UX projection artifacts;
- direct OAI obligations stay scoped to provider profile / capability evidence
  artifacts;
- ready-for-projection posture cannot hide blocking drift rows;
- no row claims implementation, work-packet execution, product authorization,
  release, graph-memory authority, or `V84` selection.

## Mandatory Reject Fixtures

The `V83-B` slice should include rejects for:

- edge decomposition without an intent contract ref;
- semantic object invented without source refs;
- generated-spec edge invented from model output without source-bound intent
  refs;
- artifact obligation without semantic edge refs;
- obligation map marked ready with unmapped required edge;
- broad package or repo target treated as bounded artifact obligation;
- non-goal converted into implementation requirement;
- authority boundary converted into permission;
- passing tests treated as semantic preservation without edge refs;
- edge marked preserved with tests but no semantic relation refs;
- artifact obligation maps a non-goal into a required change;
- artifact obligation points at an unbounded package or repo target;
- Morphic UX support source used to require runtime composer changes;
- Morphic UX support example turned into a generic runtime obligation;
- direct OAI profile source used to grant runtime capability;
- direct OAI profile turned into provider capability authority;
- drift register resolving blockers by prose;
- drift blocker resolved by model prose rather than source-bound evidence;
- row claiming code implementation, work-packet execution, PR creation, release,
  or later-family selection.

## Reference Fixture Shape

The first `V83-B` reference fixture should include:

- edge decomposition for the intent-to-implementation-spec institutionalization
  candidate;
- artifact obligations for source index, intent contract, guardrail, fixture,
  reject fixture, and validator coverage;
- validation-need rows for schema validation, validator behavior, positive
  fixture, reject fixture, semantic review, and human review;
- acceptance evidence requirement rows bound to semantic edges rather than
  generic passing-test posture;
- one Morphic UX example classified as scoped downstream obligation pressure,
  not runtime work;
- one direct OAI / meta-orchestrator example classified as support input for
  workflow/capability obligations, not direct runtime authority;
- a drift / ambiguity row for generalized digital-artifact projection deferred
  to a later family.

It should include zero:

- projection packets;
- work-packet handoffs;
- code edits;
- runtime execution;
- product, release, graph, or later-family selection rows.
