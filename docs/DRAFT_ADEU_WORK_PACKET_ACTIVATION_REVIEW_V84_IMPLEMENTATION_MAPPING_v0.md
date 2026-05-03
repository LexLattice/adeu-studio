# Draft ADEU Work Packet Activation Review V84 Implementation Mapping v0

Status: support / implementation mapping record for planned `V84`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V84` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v74.md`
- `docs/ARCHITECTURE_ADEU_WORK_PACKET_ACTIVATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V84` should add implementation work-packet activation review records without
turning them into:

- implementation, file edits, or target mutation;
- work-packet activation or work-packet execution;
- command execution or tool invocation;
- worker assignment, dispatch execution, or meta-orchestrator runtime
  transition;
- Morphic UX runtime changes or direct OAI runtime behavior;
- PR creation, commit, merge, release, product authorization, or released
  truth;
- corpus ingestion, connector activation, endpoint access, data transfer, or
  external branch activation;
- graph-memory authority, benchmark truth, generalized artifact authority, or
  recursive policy amendment;
- `V85` or later-family selection.

The implementation target is a typed activation-review family that can
represent:

- source-bound activation-review requests;
- source indexes over released `V83-C` projection / handoff / closeout
  substrate;
- non-execution guardrails;
- work-packet scope contracts;
- implementation target-surface boundaries;
- validation evidence plans;
- activation exceptions;
- readiness summaries and post-activation-review handoffs.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded work-packet activation review records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus236/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V84` still describes repo review
metadata and implementation-work-packet posture. If a later family becomes a
live work-packet executor, meta-orchestrator runtime, product UI, direct OAI
runtime harness, graph runtime, or release automation layer, that work should
split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/work_packet_activation_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_work_packet_activation_review_v84a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_work_packet_activation_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_work_packet_activation_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_work_packet_activation_non_execution_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_work_packet_scope_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_implementation_target_surface_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_work_packet_validation_evidence_plan.v1.json`
- `packages/adeu_repo_description/schema/repo_work_packet_activation_exception_register.v1.json`
- `packages/adeu_repo_description/schema/repo_work_packet_activation_readiness_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_work_packet_activation_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_work_packet_activation_family_closeout_alignment.v1.json`

Expected mirror schema files follow the same names under `spec/`.

## 3. Candidate `V84` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_work_packet_activation_review_request@1` | `V84-A` | source-bound request rows for later work-packet activation review |
| `repo_work_packet_activation_source_index@1` | `V84-A` | source rows over released `V83-C` projection, quality gate, handoff, closeout, support, and absence posture |
| `repo_work_packet_activation_non_execution_guardrail@1` | `V84-A` | guardrails preventing requests from becoming implementation, execution, PR, commit, merge, release, product, graph, or later-family authority |
| `repo_work_packet_scope_contract@1` | `V84-B` | bounded work-packet scope for later review only |
| `repo_implementation_target_surface_boundary@1` | `V84-B` | concrete target-surface boundary rows with mutation forbidden by `V84` |
| `repo_work_packet_validation_evidence_plan@1` | `V84-B` | edge-bound and obligation-bound validation evidence plan rows |
| `repo_work_packet_activation_exception_register@1` | `V84-B` | blockers and warnings over scope, target, validation, authority, provenance, and drift |
| `repo_work_packet_activation_readiness_summary@1` | `V84-C` | activation-readiness summary without implementation |
| `repo_post_work_packet_activation_review_handoff@1` | `V84-C` | later-lock handoff without work-packet execution |
| `repo_work_packet_activation_family_closeout_alignment@1` | `V84-C` | family closeout alignment without `V85` selection |

`V84-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement scope contracts,
target-boundary rows, validation evidence plans, exception registers,
readiness summaries, handoffs, code edits, PR creation, commits, releases, or
runtime changes.

## 4. Source Classes

The family should consume concrete source refs from:

- `V83` family closeout:
  - `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v235/evidence_inputs/v83_family_closeout_alignment_v235.json`
  - `artifacts/agent_harness/v235/evidence_inputs/v83c_semantic_projection_closeout_evidence_v235.json`
- `V83-C` reference fixtures:
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
  - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
  - `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become activation source rows. Support docs may contextualize
`V84`; they do not become activation eligibility by themselves.

## 5. Shared Row Vocabulary

Minimum activation source row fields:

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

Optional generated work-packet candidate rows:

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

Minimum candidate authority posture:

- `candidate_only`
- `candidate_blocked_by_missing_v83_projection`
- `candidate_blocked_by_missing_quality_gate`
- `candidate_blocked_by_unbounded_target`
- `candidate_blocked_by_missing_review`

Minimum activation-review request fields:

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

Minimum activation review eligibility posture:

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

Minimum activation authority posture:

- `no_activation_authority_granted_by_v84`
- `activation_requires_later_canonical_lock`
- `activation_forbidden_by_this_family`

Minimum implementation lock status:

- `no_implementation_lock_created_by_v84`
- `later_implementation_lock_review_requested`
- `later_selector_required`
- `deferred_no_selection`

Minimum target family boundary posture:

- `repo_description_implementation_allowed_for_later_lock_review`
- `morphic_ux_requires_runtime_ui_authority_review`
- `direct_oai_requires_provider_runtime_authority_review`
- `meta_orchestrator_requires_workflow_runtime_authority_review`
- `product_requires_product_authority_review`
- `graph_requires_graph_memory_authority_review`
- `future_family_only`

Minimum non-execution guardrail fields:

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

Reference rows should use:

- `activation_execution_posture = no_activation_performed_by_v84`
- `work_packet_execution_posture = no_work_packet_execution_performed_by_v84`
- `implementation_execution_posture = no_implementation_performed_by_v84`
- `target_mutation_posture = no_target_mutation_performed_by_v84`
- `activation_authority_posture = no_activation_authority_granted_by_v84`
- `implementation_lock_status = no_implementation_lock_created_by_v84`

Canonical lock requirement rows should be represented as current `V84` review
requirements, not as created locks:

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

Minimum required lock kind:

- `repo_schema_model_fixture_test_lock`
- `docs_support_artifact_lock`
- `morphic_ux_implementation_review_lock`
- `direct_oai_harness_implementation_review_lock`
- `meta_orchestrator_workflow_activation_review_lock`
- `future_family_lock`

## 6. Slice Ladder

`V84-A` should establish recordability, eligibility, and guardrails only.

`V84-B` should add bounded scope, target, validation, and exception posture. It
should add `activation_package_ref` to scope, target, validation, exception,
and lineage rows; distinguish read dependencies, prospective write targets,
validation targets, generated artifact targets, forbidden targets, and
context-only targets; and represent validation as a matrix over semantic
edges, artifact obligations, implementation specs, target boundaries, positive
evidence, reject evidence, regression evidence, manual review, and tool
applicability.

`V84-C` should summarize readiness, emit later-lock handoff posture, and close
the family without implementation or later-family selection.
It should require every readiness summary row to resolve to one
`activation_package_ref`, one `candidate_ref`, and one released `V83-C`
projection lineage.

## 7. Reference Fixture Strategy

The first `V84-A` reference fixture should include:

- one activation-review request sourced from released `V83-C` projection /
  quality-gate / handoff rows for the semantic implementation-spec workflow;
- one Morphic UX projection row carried as later projection or implementation
  review pressure with warning-only or future-family posture;
- one direct OAI / meta-orchestrator support row carried as workflow review
  pressure, not runtime behavior;
- explicit non-execution guardrails for every candidate;
- zero scope contracts, target-boundary rows, validation plans, exception
  registers, readiness summaries, handoffs, implementation work, commands,
  PRs, commits, merges, releases, product authority, graph authority, or `V85`
  selection.

Mandatory reject fixtures should cover:

- support-only activation eligibility;
- generated work-packet candidate treated as activation authority;
- projection packet missing released `V83-C` source refs;
- quality gate missing or carrying blockers but request marked eligible;
- broad target surface or glob treated as bounded implementation scope;
- validation evidence listed without semantic edge or artifact obligation refs;
- work-packet handoff treated as permission to implement now;
- command / tool / PR / commit / release authority claimed by `V84-A`;
- Morphic UX support context treated as runtime UI authority;
- direct OAI support context treated as provider runtime authority;
- `V85` selected by closeout or starter rows.

## 8. Recommended `V84-A` Starter Lock Scope

The future `vNext+236` starter should select only:

```text
packages/adeu_repo_description/src/adeu_repo_description/work_packet_activation_review.py
packages/adeu_repo_description/src/adeu_repo_description/export_schema.py
packages/adeu_repo_description/src/adeu_repo_description/__init__.py

packages/adeu_repo_description/schema/repo_work_packet_activation_review_request.v1.json
packages/adeu_repo_description/schema/repo_work_packet_activation_source_index.v1.json
packages/adeu_repo_description/schema/repo_work_packet_activation_non_execution_guardrail.v1.json

spec/repo_work_packet_activation_review_request.schema.json
spec/repo_work_packet_activation_source_index.schema.json
spec/repo_work_packet_activation_non_execution_guardrail.schema.json

packages/adeu_repo_description/tests/test_work_packet_activation_review_v84a.py
packages/adeu_repo_description/tests/test_repo_description_export_schema.py

apps/api/fixtures/repo_description/vnext_plus236/
  repo_work_packet_activation_review_request_v236_reference.json
  repo_work_packet_activation_source_index_v236_reference.json
  repo_work_packet_activation_non_execution_guardrail_v236_reference.json
  repo_work_packet_activation_v236_reject_*.json
```

No `V84-B`, no `V84-C`, no scope contracts, no target-surface boundary rows,
no validation evidence plans, no activation exception register, no readiness
summary, no handoff, no implementation, no work-packet execution, no command
execution, no tool invocation, no target mutation, no PR / commit / merge /
release, no product authorization, no graph-memory authority, no recursive
policy amendment, and no `V85`.
