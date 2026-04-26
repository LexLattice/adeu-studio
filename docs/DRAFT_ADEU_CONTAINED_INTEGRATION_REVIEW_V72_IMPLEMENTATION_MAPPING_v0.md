# Draft ADEU Contained Integration Review V72 Implementation Mapping v0

Status: support / implementation mapping record for planned `V72`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned `V72`
family into likely package, schema, validator, fixture, and evidence work so the
family can be reviewed before the first active slice lock is drafted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v62.md`
- `docs/ARCHITECTURE_ADEU_CONTAINED_INTEGRATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_CONTAINED_INTEGRATION_REVIEW_V72_PLANNING_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72C_IMPLEMENTATION_MAPPING_v0.md`

## 1. Family Intent

`V72` should add contained integration review without turning integration review
into:

- unbounded implementation scheduling;
- autonomous file edits;
- commit / merge / release authority;
- product projection;
- runtime permission;
- dispatch or execution widening.

The implementation target is a typed contained-integration-review family that
can represent:

- source-bound containment plans over released `V71-C` handoff rows;
- bounded repo target surfaces;
- non-release guardrails;
- contained trial records;
- effect-surface registers;
- rollback readiness;
- commit / PR / merge / release posture boundaries;
- handoff to `V73` or future-family review.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded contained integration review
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus200/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative: `V72` still describes repo/corpus metadata
and integration-review state. If a later slice tries to become live write
automation, merge automation, product UI, or dispatch orchestration, that work
should be split away instead of expanding `adeu_repo_description` by
implication.

The proposed `repo_*` schemas are repo-description contained-integration-review
surfaces, not runtime execution, release, product, or ARC challenge artifacts.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/contained_integration_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_contained_integration_review_v72a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_contained_integration_candidate_plan.v1.json`
- `packages/adeu_repo_description/schema/repo_integration_target_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_integration_non_release_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_contained_integration_trial_record.v1.json`
- `packages/adeu_repo_description/schema/repo_integration_effect_surface_register.v1.json`
- `packages/adeu_repo_description/schema/repo_integration_rollback_readiness.v1.json`
- `packages/adeu_repo_description/schema/repo_commit_release_authority_posture.v1.json`
- `packages/adeu_repo_description/schema/repo_post_integration_outcome_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_contained_integration_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_contained_integration_candidate_plan.schema.json`
- `spec/repo_integration_target_boundary.schema.json`
- `spec/repo_integration_non_release_guardrail.schema.json`
- `spec/repo_contained_integration_trial_record.schema.json`
- `spec/repo_integration_effect_surface_register.schema.json`
- `spec/repo_integration_rollback_readiness.schema.json`
- `spec/repo_commit_release_authority_posture.schema.json`
- `spec/repo_post_integration_outcome_review_handoff.schema.json`
- `spec/repo_contained_integration_family_closeout_alignment.schema.json`

## 3. Candidate `V72` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_contained_integration_candidate_plan@1` | `V72-A` | top-level contained integration plan rows over released `V71-C` handoffs |
| `repo_integration_target_boundary@1` | `V72-A` | bounded target rows for docs, schema, validator, fixture, test, workflow, or package surfaces |
| `repo_integration_non_release_guardrail@1` | `V72-A` | explicit guardrail rows preserving non-release and non-product posture |
| `repo_contained_integration_trial_record@1` | `V72-B` | dry-run, local-trial, blocked-trial, or trial-ready rows |
| `repo_integration_effect_surface_register@1` | `V72-B` | effect-surface rows for impacted repo surfaces |
| `repo_integration_rollback_readiness@1` | `V72-B` | rollback requirement and verification posture rows |
| `repo_commit_release_authority_posture@1` | `V72-C` | commit / PR / merge / release boundary rows |
| `repo_post_integration_outcome_review_handoff@1` | `V72-C` | handoff rows to `V73`, future-family review, or deferral |
| `repo_contained_integration_family_closeout_alignment@1` | `V72-C` | family closeout alignment without release truth |

`V72-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not execute trials or edit target files.

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
- `V71` ratification-review family closeout:
  - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v199/evidence_inputs/v71_family_closeout_alignment_v199.json`
- `V71` post-ratification substrate:
  - `artifacts/agent_harness/v199/evidence_inputs/v71c_candidate_ratification_closeout_evidence_v199.json`
  - `apps/api/fixtures/repo_description/vnext_plus199/repo_ratification_amendment_scope_boundary_v199_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus199/repo_post_ratification_handoff_v199_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus199/repo_candidate_ratification_family_closeout_alignment_v199_reference.json`
- support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become integration source rows.

If any expected source is missing when the active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct integration state from planning prose.

## 5. Required Starter Enumerations

Containment plan posture:

- `eligible_for_containment_planning`
- `blocked_by_dissent`
- `blocked_by_evidence_gap`
- `blocked_by_scope_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Target boundary kind:

- `docs_support_surface`
- `schema_surface`
- `validator_surface`
- `fixture_surface`
- `test_surface`
- `workflow_surface`
- `package_surface`
- `no_target_boundary`

Target resolution kind:

- `concrete_file_ref`
- `concrete_schema_ref`
- `concrete_fixture_ref`
- `concrete_test_ref`
- `concrete_doc_ref`
- `bounded_package_surface_with_child_refs`
- `no_target_boundary`

Integration target posture:

- `single_surface_bounded`
- `multi_surface_bounded`
- `target_requires_review`
- `target_blocked`
- `target_absent`

Required trial posture for `V72-A`:

- `no_trial_selected_in_v72a`
- `dry_run_required_later`
- `local_trial_required_later`
- `trial_blocked_until_source_gap_resolved`
- `trial_blocked_until_dissent_resolved`
- `future_family_trial_only`

Non-release guardrail posture:

- `no_commit_or_release_authority`
- `no_product_authorization`
- `no_runtime_permission`
- `no_dispatch_authority`
- `no_external_contest_authority`

## 6. Shared Row Vocabulary

Minimum integration source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `source_horizon`
- `limitation_note`

`V72-A` should embed these rows inside
`repo_contained_integration_candidate_plan@1` unless review proves a separate
source-register surface is needed. Target-boundary and guardrail source refs
must resolve through these rows or explicit absence rows.

Minimum containment plan row fields:

- `integration_source_rows`
- `plan_ref`
- `candidate_ref`
- `source_handoff_refs`
- `ratification_refs`
- `amendment_scope_refs`
- `target_boundary_refs`
- `containment_plan_posture`
- `required_trial_posture`
- `rollback_requirement`
- `odeu_lanes`
- `guardrail_refs`
- `limitation_note`

Minimum target boundary row fields:

- `target_boundary_ref`
- `candidate_ref`
- `target_boundary_kind`
- `target_resolution_kind`
- `target_refs`
- `target_posture`
- `allowed_change_kinds`
- `forbidden_change_kinds`
- `source_refs`
- `limitation_note`

Minimum non-release guardrail row fields:

- `guardrail_ref`
- `candidate_ref`
- `plan_refs`
- `forbidden_downstream_roles`
- `non_release_posture`
- `required_later_authority`
- `limitation_note`

Minimum later trial row fields:

- `trial_ref`
- `candidate_ref`
- `plan_refs`
- `target_boundary_refs`
- `trial_posture`
- `trial_diff_posture`
- `active_lock_refs`
- `trial_evidence_refs`
- `observed_effect_refs`
- `rollback_readiness_refs`
- `non_release_guardrail_refs`
- `limitation_note`

## 7. Negative Laws

`V72` should reject:

- containment plan for candidate absent from released `V71-C` handoffs;
- containment plan for `V71-C` handoff that is not `ready_for_v72_review`;
- product wedge routed into contained integration;
- conceptual diff deferred with dissent routed into contained integration;
- target boundary expressed as a glob instead of concrete bounded refs;
- package-surface target boundary without concrete child refs or explicit
  limitation;
- target boundary with empty forbidden change kinds;
- non-release guardrail with no forbidden downstream roles;
- eligible containment plan with no rollback requirement;
- blocked containment plan whose blocker is absent from both refs and limitation
  note;
- future-family-only plan with a concrete integration target boundary;
- any `V72-A` row claiming a trial was executed;
- any `V72-A` row claiming commit, merge, release, product, runtime, or dispatch
  authority.

## 8. Expected Starter Fixture Shape

The first `V72-A` reference fixture should be a post-`V71` seed, not a trial
execution ledger.

Expected coverage:

- one containment plan row for the self-evidencing workflow-type emergence
  candidate, because `V71-C` marks it `ready_for_v72_review`;
- one blocked or rejected row proving the conceptual-diff candidate remains
  deferred with dissent and cannot enter contained integration planning;
- one future-family row proving the typed-adjudication product wedge remains
  future-family review only;
- target boundary rows with concrete target refs and forbidden change kinds;
- `target_resolution_kind` proving package surfaces are bounded by concrete
  child refs when package visibility is needed;
- an eligible plan with non-empty source handoff refs, ratification refs,
  amendment-scope refs, target-boundary refs, guardrail refs, and rollback
  requirement;
- blocked / future-family rows whose trial posture is
  `trial_blocked_until_*`, `future_family_trial_only`, or
  `no_trial_selected_in_v72a`, never a recorded trial outcome;
- non-release guardrail rows with non-empty forbidden downstream roles;
- no trial execution, local write, commit, merge, release, product, runtime, or
  dispatch authority.

Recommended first fixture names:

- `repo_contained_integration_candidate_plan_v200_reference.json`
- `repo_integration_target_boundary_v200_reference.json`
- `repo_integration_non_release_guardrail_v200_reference.json`
- `repo_contained_integration_v200_reject_unknown_v71c_handoff.json`
- `repo_contained_integration_v200_reject_non_ready_handoff.json`
- `repo_contained_integration_v200_reject_product_wedge_to_integration.json`
- `repo_contained_integration_v200_reject_deferred_dissent_as_ready.json`
- `repo_contained_integration_v200_reject_glob_target_boundary.json`
- `repo_contained_integration_v200_reject_guardrail_allows_release.json`
- `repo_contained_integration_v200_reject_trial_executed_in_v72a.json`

## 9. Closeout Expectation

The family should close only after `V72-C` proves that contained integration
planning, trial posture, rollback readiness, and commit / release boundaries are
all represented separately. `V73` remains responsible for outcome review.
