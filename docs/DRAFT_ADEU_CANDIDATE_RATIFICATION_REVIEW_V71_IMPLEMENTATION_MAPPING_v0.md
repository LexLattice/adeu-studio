# Draft ADEU Candidate Ratification Review V71 Implementation Mapping v0

Status: support / implementation mapping record for planned `V71`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned `V71`
family into likely package, schema, validator, fixture, and evidence work so the
family can be reviewed before the first active slice lock is drafted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v61.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71C_IMPLEMENTATION_MAPPING_v0.md`

## 1. Family Intent

`V71` should add ratification review without turning ratification into:

- implementation scheduling;
- contained integration;
- commit / merge / release authority;
- product projection;
- runtime permission;
- dispatch or execution widening.

The implementation target is a typed ratification-review family that can
represent:

- source-bound requests over released `V70-C` handoff rows;
- authority profiles for human / maintainer / model / tool / support roles;
- requested ratification horizon and scope;
- settlement posture over V70 conflicts, gaps, and dissent;
- ratification, rejection, or deferral outcomes;
- amendment-scope boundaries for later families;
- post-ratification handoff to `V72` or future-family review.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded candidate ratification review
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus197/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative: `V71` still describes repo/corpus metadata
and ratification state. If a later slice tries to become live runtime
permissioning, merge automation, product UI, or dispatch orchestration, that
work should be split away instead of expanding `adeu_repo_description` by
implication.

The proposed `repo_*` schemas are repo-description ratification-review surfaces,
not runtime execution, release, product, or ARC challenge artifacts.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/candidate_ratification_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_candidate_ratification_review_v71a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected later implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/candidate_ratification_settlement.py`
- `packages/adeu_repo_description/src/adeu_repo_description/candidate_ratification_handoff.py`
- `packages/adeu_repo_description/tests/test_candidate_ratification_review_v71b.py`
- `packages/adeu_repo_description/tests/test_candidate_ratification_review_v71c.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_candidate_ratification_request.v1.json`
- `packages/adeu_repo_description/schema/repo_ratification_authority_profile.v1.json`
- `packages/adeu_repo_description/schema/repo_ratification_request_scope_boundary.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_candidate_ratification_record.v1.json`
- `packages/adeu_repo_description/schema/repo_review_settlement_record.v1.json`
- `packages/adeu_repo_description/schema/repo_ratification_dissent_register.v1.json`
- `packages/adeu_repo_description/schema/repo_ratification_amendment_scope_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_ratification_handoff.v1.json`

Expected mirror schema files:

- `spec/repo_candidate_ratification_request.schema.json`
- `spec/repo_ratification_authority_profile.schema.json`
- `spec/repo_ratification_request_scope_boundary.schema.json`
- `spec/repo_candidate_ratification_record.schema.json`
- `spec/repo_review_settlement_record.schema.json`
- `spec/repo_ratification_dissent_register.schema.json`
- `spec/repo_ratification_amendment_scope_boundary.schema.json`
- `spec/repo_post_ratification_handoff.schema.json`

## 3. Candidate `V71` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_candidate_ratification_request@1` | `V71-A` | top-level request rows over released `V70-C` handoffs |
| `repo_ratification_authority_profile@1` | `V71-A` | actor / source / authority posture rows |
| `repo_ratification_request_scope_boundary@1` | `V71-A` | requested horizon, allowed ratification actions, and forbidden downstream roles |
| `repo_candidate_ratification_record@1` | `V71-B` | ratification, rejection, and deferral outcome rows |
| `repo_review_settlement_record@1` | `V71-B` | settlement posture over conflicts, gaps, blockers, and carry-forward rows |
| `repo_ratification_dissent_register@1` | `V71-B` | dissent or minority-review rows preserved after settlement |
| `repo_ratification_amendment_scope_boundary@1` | `V71-C` | amendment-scope limits for later families |
| `repo_post_ratification_handoff@1` | `V71-C` | handoff rows to `V72`, future-family review, or deferral without integration |

`V71-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not need to derive every ratification
outcome automatically.

## 4. Source Classes

The family should consume concrete source refs from:

- `V68` cartography family closeout:
  - `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v190/evidence_inputs/v68_family_closeout_alignment_v190.json`
- `V69` candidate-intake family closeout:
  - `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v193/evidence_inputs/v69_family_closeout_alignment_v193.json`
- `V70` review-classification family closeout:
  - `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v196/evidence_inputs/v70_family_closeout_alignment_v196.json`
- `V70` pre-ratification substrate:
  - `artifacts/agent_harness/v196/evidence_inputs/v70c_candidate_review_summary_handoff_evidence_v196.json`
  - `apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json`
- support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become ratification source rows.

If any expected source is missing when the active starter lock is drafted, the
absence should be represented as an explicit source or request-source row. The
reference fixture should not reconstruct ratification state from planning prose.

## 5. Required Starter Enumerations

Ratification request posture:

- `eligible_for_ratification_review`
- `requires_settlement_before_ratification`
- `deferred_to_future_family`
- `rejected_out_of_scope`

Authority actor kind:

- `human_operator`
- `maintainer`
- `model_reviewer`
- `tool_validator`
- `external_reviewer`

Authority grant source kind:

- `repo_lock`
- `closeout_decision`
- `maintainer_record`
- `policy_doc`
- `support_doc`
- `transcript`
- `tool_output`

Authority posture:

- `ratification_authority`
- `settlement_authority`
- `review_only`
- `advisory_only`
- `tool_evidence_only`
- `not_authorized`

Ratification horizon:

- `source_bound_candidate_validity`
- `review_conflict_settlement`
- `authority_boundary_acceptance`
- `future_family_routing`
- `integration_review_readiness`
- `utility_projection_acceptance`

Forbidden downstream role:

- `implementation_task`
- `contained_integration`
- `commit_release_authority`
- `product_authorization`
- `runtime_permission`
- `dispatch_authority`
- `external_contest_authority`

Review signal posture:

- `warning_only`
- `gating_blocker`
- `settlement_required`
- `evidence_required`
- `human_review_required`
- `future_family_only`

## 6. Shared Row Vocabulary

Minimum ratification source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `source_horizon`
- `limitation_note`

Minimum ratification request row fields:

- `request_ref`
- `candidate_ref`
- `ratification_source_refs`
- `source_handoff_refs`
- `summary_refs`
- `handoff_refs`
- `requested_ratification_horizon`
- `request_posture`
- `review_signal_posture`
- `odeu_lanes`
- `authority_profile_refs`
- `request_scope_boundary_refs`
- `limitation_note`

Minimum authority profile row fields:

- `authority_profile_ref`
- `authority_actor_ref`
- `authority_actor_kind`
- `authority_grant_source_kind`
- `authority_source_refs`
- `authority_posture`
- `binding_layer`
- `allowed_ratification_horizons`
- `forbidden_downstream_roles`
- `limitation_note`

Minimum request scope boundary row fields:

- `request_scope_boundary_ref`
- `candidate_ref`
- `ratification_source_refs`
- `request_refs`
- `allowed_ratification_actions`
- `forbidden_downstream_roles`
- `allowed_next_review_surfaces`
- `non_implementation_guardrail`

Minimum later ratification record row fields:

- `ratification_ref`
- `candidate_ref`
- `request_refs`
- `settlement_refs`
- `decision_posture`
- `ratification_horizon`
- `allowed_next_review_surface`
- `ratifying_authority_profile_refs`
- `dissent_refs`
- `amendment_scope_refs`
- `non_integration_guardrail`

## 7. Negative Laws

`V71` should reject:

- ratification request for candidate absent from released `V70-C` handoffs;
- request row with no source handoff refs;
- request row sourced only from prose memory;
- model reviewer as `ratification_authority` without explicit lock-level source;
- tool validator as ratification proof;
- support doc as ratification authority;
- transcript content as ratification authority;
- product wedge routed into `V71` ratification review;
- blocked handoff marked eligible without settlement requirement;
- ready handoff marked blocked without evidence;
- authority profile with empty forbidden downstream roles;
- scope boundary that allows implementation, integration, release, product,
  runtime, or dispatch;
- any `V71-A` row that emits final ratification outcome.
- ratification record whose horizon is outside any referenced authority
  profile's `allowed_ratification_horizons`.

## 8. Expected Starter Fixture Shape

The first `V71-A` reference fixture should be a post-`V70` seed, not a final
ratification ledger.

Expected coverage:

- one request row for a `ready_for_v71_review` handoff;
- one request row for a `blocked_by_conflict` handoff requiring settlement
  before ratification;
- one deferred row or boundary row proving product wedge pressure remains
  future-family review, not `V71` ratification;
- authority profile rows that distinguish human / maintainer authority from
  model, tool, support, or transcript inputs;
- scope boundary rows with non-empty forbidden downstream roles;
- no ratification outcome, implementation, integration, release, product, or
  dispatch authority.

Recommended first fixture names:

- `repo_candidate_ratification_request_v197_reference.json`
- `repo_ratification_authority_profile_v197_reference.json`
- `repo_ratification_request_scope_boundary_v197_reference.json`
- `repo_candidate_ratification_v197_reject_missing_v70c_handoff_ref.json`
- `repo_candidate_ratification_v197_reject_model_self_ratification.json`
- `repo_candidate_ratification_v197_reject_tool_pass_as_ratification.json`
- `repo_candidate_ratification_v197_reject_support_doc_as_ratification_authority.json`
- `repo_candidate_ratification_v197_reject_product_wedge_to_v71.json`
- `repo_candidate_ratification_v197_reject_scope_allows_release.json`
- `repo_candidate_ratification_v197_reject_v71a_records_final_ratification.json`

## 9. Closeout Expectation

The family should close only after `V71-C` proves that ratified, rejected,
deferred, and future-family-routed candidates are all represented with explicit
authority and scope boundaries. `V72` remains responsible for contained
integration and release-posture review.
