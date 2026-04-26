# LOCKED_CONTINUATION_vNEXT_PLUS197

## Status

Bounded starter lock draft for `V71-A` (candidate ratification request,
authority-profile, request-scope boundary, and source-row backbone).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative `V71-A`
implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `V71`
- slice: `V71-A`
- branch-local execution target: `arc/v71-r1`

## Purpose

Freeze the bounded `V71-A` starter slice so the repo can represent
ratification-review requests over released `V70-C` summary and
pre-ratification handoff rows without performing ratification.

`vNext+197` authorizes docs plus the first implementation path over the existing
repo-owned `adeu_repo_description` package. It does not authorize final
ratification records, settlement records, dissent registers, amendment scope,
post-ratification handoff, `V72` contained integration, commit / merge / release
authority, `V73` outcome review, `V74` operator or product projection, `V75`
dispatch, runtime permission, or external contest participation.

In `vNext+197`, `V71-A` adds only ratification source rows, request rows,
authority profile rows, request-scope boundary rows, schema/model/validator
exports, and bounded reference / reject fixtures. It must not begin `V71-B`,
`V71-C`, `V72`, or any downstream implementation workflow.

## Instantiated Here

- `V71-A` instantiates one bounded candidate ratification-review starter seam:
  - existing repo-owned package only:
    - `adeu_repo_description`
  - consumed released basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS194.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS194.md`
    - `docs/ASSESSMENT_vNEXT_PLUS194_EDGES.md`
    - `artifacts/agent_harness/v194/evidence_inputs/v70a_candidate_review_classification_evidence_v194.json`
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS195.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS195.md`
    - `docs/ASSESSMENT_vNEXT_PLUS195_EDGES.md`
    - `artifacts/agent_harness/v195/evidence_inputs/v70b_candidate_review_adversarial_evidence_v195.json`
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS196.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS196.md`
    - `docs/ASSESSMENT_vNEXT_PLUS196_EDGES.md`
    - `artifacts/agent_harness/v196/evidence_inputs/v70c_candidate_review_summary_handoff_evidence_v196.json`
    - `artifacts/agent_harness/v196/evidence_inputs/v70_family_closeout_alignment_v196.json`
    - `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
    - `apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json`
    - shipped `V70-A`, `V70-B`, and `V70-C` review-classification surfaces
    - closed `V68` and `V69` family closeout records as source and authority
      boundary substrate
  - consumed support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v61.md`
    - `docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.md`
    - `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.json`
    - `docs/support/arc_series_mapping/REVIEW_GPTPRO_CANDIDATE_RATIFICATION_REVIEW_V71_PLANNING_v0.md`
    - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
  - emitted starter record shapes:
    - `repo_candidate_ratification_request@1`
    - `repo_ratification_authority_profile@1`
    - `repo_ratification_request_scope_boundary@1`
  - consumed `V70` record shapes:
    - `repo_candidate_evidence_source_index@1`
    - `repo_candidate_evidence_classification_record@1`
    - `repo_candidate_review_boundary_guardrail@1`
    - `repo_candidate_adversarial_review_matrix@1`
    - `repo_candidate_review_conflict_register@1`
    - `repo_candidate_review_gap_scan@1`
    - `repo_candidate_review_classification_summary@1`
    - `repo_candidate_pre_ratification_handoff@1`
  - required ratification request postures:
    - `eligible_for_ratification_review`
    - `requires_settlement_before_ratification`
    - `deferred_to_future_family`
    - `rejected_out_of_scope`
  - required authority actor kinds:
    - `human_operator`
    - `maintainer`
    - `model_reviewer`
    - `tool_validator`
    - `external_reviewer`
  - required authority grant source kinds:
    - `repo_lock`
    - `closeout_decision`
    - `maintainer_record`
    - `policy_doc`
    - `support_doc`
    - `transcript`
    - `tool_output`
  - required authority postures:
    - `ratification_authority`
    - `settlement_authority`
    - `review_only`
    - `advisory_only`
    - `tool_evidence_only`
    - `not_authorized`
  - required review signal postures:
    - `warning_only`
    - `gating_blocker`
    - `settlement_required`
    - `evidence_required`
    - `human_review_required`
    - `future_family_only`
  - required ratification horizons:
    - `source_bound_candidate_validity`
    - `review_conflict_settlement`
    - `authority_boundary_acceptance`
    - `future_family_routing`
    - `integration_review_readiness`
    - `utility_projection_acceptance`
  - required forbidden downstream roles:
    - `implementation_task`
    - `contained_integration`
    - `commit_release_authority`
    - `product_authorization`
    - `runtime_permission`
    - `dispatch_authority`
    - `external_contest_authority`
  - one explicit source-binding law:
    - every request, authority profile, and request-scope boundary resolves
      through concrete ratification source rows or explicit absence rows
  - one explicit authority-source law:
    - actor kind and authority grant source kind are distinct; `repo_lock` is a
      source kind, not an actor kind
  - one explicit request-scope law:
    - `repo_ratification_request_scope_boundary@1` bounds what a request may
      ask for; it is not `V71-C` amendment scope
  - one explicit non-ratification law:
    - `V71-A` request rows cannot emit final ratification, rejection, deferral,
      adoption, implementation, product, release, runtime, or dispatch authority

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `repo_candidate_ratification_request@1`
  - `repo_ratification_authority_profile@1`
  - `repo_ratification_request_scope_boundary@1`
- deterministic reference and reject fixtures for the bounded `V71-A` starter
  family only
- a hand-curated reference fixture seeded from released `V70-C` summary and
  pre-ratification handoff fixture material
- validators that prove:
  - ratification source rows are explicit and source presence is represented as
    row data
  - request rows reference known released `V70-C` summary and handoff refs
  - request rows have non-empty ratification source refs and source handoff refs
  - ready `V70-C` handoff rows can become eligible request rows only when no
    blockers remain
  - blocked `V70-C` handoff rows require settlement before ratification
  - future-family / product-wedge handoff rows remain non-`V71` deferrals
  - authority profile rows separate actor kind from authority grant source kind
  - model, tool, support, and transcript sources default to non-ratifying
    authority posture unless an explicit lock-level or maintainer source grants
    otherwise
  - request-scope boundaries have non-empty forbidden downstream roles
  - no request-scope boundary allows implementation, integration, release,
    product authorization, runtime permission, dispatch, or external contest
    authority
  - no `V71-A` row emits final ratification, settlement, amendment scope,
    post-ratification handoff, implementation, release, product, runtime, or
    dispatch authority
- tests that prove:
  - ratification request for unknown candidate is rejected
  - ratification request with no `V70-C` handoff refs is rejected
  - ratification request with dangling summary refs is rejected
  - blocked handoff marked eligible without settlement requirement is rejected
  - product wedge routed to `V71` ratification review is rejected
  - model reviewer granted self-ratification authority is rejected
  - tool validator treated as ratification proof is rejected
  - support doc marked as ratification authority is rejected
  - transcript content treated as truth or ratification authority is rejected
  - authority profile with empty forbidden downstream roles is rejected
  - request-scope boundary permitting implementation, integration, release,
    product, runtime, or dispatch is rejected
  - `V71-A` request row carrying final ratification, rejection, adoption, or
    integration outcome is rejected
- no final ratification record, settlement record, dissent register, amendment
  scope, post-ratification handoff, contained integration, product projection,
  commit/release authority, runtime permission, external contest participation,
  or dispatch widening lands in this slice.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+197",
  "target_path": "V71-A",
  "slice": "V71-A",
  "family": "V71",
  "branch_local_execution_target": "arc/v71-r1",
  "target_scope": "one_bounded_candidate_ratification_request_authority_profile_request_scope_starter_slice",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "api_surfaces": [],
  "cli_or_validation_entrypoints_for_v71a": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS194.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS195.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS196.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS194.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS195.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS196.md"
  ],
  "prerequisite_assessment_docs": [
    "docs/ASSESSMENT_vNEXT_PLUS194_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS195_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS196_EDGES.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v61.md",
  "family_architecture_doc": "docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md",
  "family_support_mapping_doc": "docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_IMPLEMENTATION_MAPPING_v0.md",
  "slice_support_mapping_doc": "docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71A_IMPLEMENTATION_MAPPING_v0.md",
  "downstream_slice_support_mapping_docs": [
    "docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71C_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "admitted_support_review": "docs/support/arc_series_mapping/REVIEW_GPTPRO_CANDIDATE_RATIFICATION_REVIEW_V71_PLANNING_v0.md",
  "support_dogfood_sources": [
    "docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.md",
    "docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.json"
  ],
  "admitted_released_basis": [
    "docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md",
    "docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md",
    "docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md",
    "artifacts/agent_harness/v196/evidence_inputs/v70_family_closeout_alignment_v196.json",
    "artifacts/agent_harness/v196/evidence_inputs/v70c_candidate_review_summary_handoff_evidence_v196.json",
    "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json",
    "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json"
  ],
  "consumed_record_shapes": [
    "repo_candidate_review_classification_summary@1",
    "repo_candidate_pre_ratification_handoff@1"
  ],
  "emitted_record_shapes_for_v71a": [
    "repo_candidate_ratification_request@1",
    "repo_ratification_authority_profile@1",
    "repo_ratification_request_scope_boundary@1"
  ],
  "required_ratification_request_postures_for_v71a": [
    "eligible_for_ratification_review",
    "requires_settlement_before_ratification",
    "deferred_to_future_family",
    "rejected_out_of_scope"
  ],
  "required_authority_actor_kinds_for_v71a": [
    "human_operator",
    "maintainer",
    "model_reviewer",
    "tool_validator",
    "external_reviewer"
  ],
  "required_authority_grant_source_kinds_for_v71a": [
    "repo_lock",
    "closeout_decision",
    "maintainer_record",
    "policy_doc",
    "support_doc",
    "transcript",
    "tool_output"
  ],
  "selected_v71b_ratification_record_for_v71a": false,
  "selected_v71c_amendment_scope_for_v71a": false,
  "selected_v72_integration_for_v71a": false,
  "selected_product_workbench_for_v71a": false,
  "selected_runtime_permission_or_dispatch_for_v71a": false
}
```

## Deferred

- `V71-B`: settlement, ratification / rejection / deferral records, and dissent
  preservation.
- `V71-C`: amendment-scope hardening and post-ratification handoff.
- `V72`: contained integration and release-posture review.
- `V73`: outcome review.
- `V74`: operator/product projection.
- `V75`: dispatch or multi-worker orchestration.

