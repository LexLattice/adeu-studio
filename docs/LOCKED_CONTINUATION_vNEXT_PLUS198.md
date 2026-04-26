# LOCKED_CONTINUATION_vNEXT_PLUS198

## Status

Bounded starter lock draft for `V71-B` (settlement records, ratification /
rejection / deferral records, and dissent preservation).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative `V71-B`
implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `V71`
- slice: `V71-B`
- branch-local execution target: `arc/v71-r2`

## Purpose

Freeze the bounded `V71-B` starter slice so the repo can record settlement,
ratification / rejection / deferral, and dissent posture over released `V71-A`
request, authority-profile, and request-scope rows.

`vNext+198` authorizes docs plus the next implementation path over the existing
repo-owned `adeu_repo_description` package. It does not authorize amendment
scope, post-ratification handoff, `V72` contained integration, commit / merge /
release authority, `V73` outcome review, `V74` operator or product projection,
`V75` dispatch, runtime permission, or external contest participation.

`V71-B` may decide a ratification posture for a source-bound candidate and
review horizon. It must keep that decision separate from implementation,
integration, product, release, runtime, and dispatch authority.

## Instantiated Here

- `V71-B` instantiates one bounded settlement / ratification-record starter
  seam:
  - existing repo-owned package only:
    - `adeu_repo_description`
  - consumed released basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS197.md`
    - `docs/ASSESSMENT_vNEXT_PLUS197_EDGES.md`
    - `artifacts/agent_harness/v197/evidence_inputs/v71a_candidate_ratification_request_evidence_v197.json`
    - shipped `V71-A` request, authority-profile, and request-scope surfaces
    - `apps/api/fixtures/repo_description/vnext_plus197/repo_candidate_ratification_request_v197_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus197/repo_ratification_authority_profile_v197_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus197/repo_ratification_request_scope_boundary_v197_reference.json`
  - consumed support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v61.md`
    - `docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/arc_series_mapping/REVIEW_GPTPRO_CANDIDATE_RATIFICATION_REVIEW_V71_PLANNING_v0.md`
  - emitted starter record shapes:
    - `repo_candidate_ratification_record@1`
    - `repo_review_settlement_record@1`
    - `repo_ratification_dissent_register@1`
  - consumed `V71-A` record shapes:
    - `repo_candidate_ratification_request@1`
    - `repo_ratification_authority_profile@1`
    - `repo_ratification_request_scope_boundary@1`
  - required decision postures:
    - `ratified`
    - `rejected`
    - `deferred`
    - `out_of_scope`
  - required ratification horizons:
    - `source_bound_candidate_validity`
    - `review_conflict_settlement`
    - `authority_boundary_acceptance`
    - `future_family_routing`
    - `integration_review_readiness`
    - `utility_projection_acceptance`
  - required allowed next review surfaces:
    - `v72_contained_integration_review`
    - `future_family_review`
    - `deferred_no_selection`
  - required settlement postures:
    - `settled_for_candidate_horizon`
    - `partially_settled_with_dissent`
    - `blocked_by_unresolved_conflict`
    - `blocked_by_unresolved_gap`
    - `requires_more_evidence`
    - `requires_human_review`
    - `future_family_only`
  - required review relation kinds:
    - `conflict`
    - `complementarity`
    - `orthogonal`
    - `duplicate`
    - `unclear_relation`
  - required review signal postures:
    - `warning_only`
    - `gating_blocker`
    - `settlement_required`
    - `evidence_required`
    - `human_review_required`
    - `future_family_only`
  - required dissent postures:
    - `no_dissent_recorded`
    - `dissent_carried_forward`
    - `minority_review_preserved`
    - `unresolved_blocker`
    - `not_applicable`
  - required dissent search postures:
    - `searched_none_found`
    - `not_searched`
    - `not_applicable`
    - `dissent_present`
    - `unknown`
  - one explicit authority-profile law:
    - every ratifying authority profile must allow the exact ratification
      horizon it is used to ratify
  - one explicit outcome/routing law:
    - `decision_posture`, `ratification_horizon`, and
      `allowed_next_review_surface` remain distinct fields
  - one explicit dissent law:
    - `no_dissent_recorded` is not proof of absence unless paired with
      `searched_none_found`
  - one explicit non-integration law:
    - ratification records may route a candidate to later review, but cannot
      become implementation tickets, merge/release permission, product
      authorization, runtime permission, or dispatch authority

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `repo_candidate_ratification_record@1`
  - `repo_review_settlement_record@1`
  - `repo_ratification_dissent_register@1`
- deterministic reference and reject fixtures for the bounded `V71-B` starter
  family only
- validators that prove:
  - ratification records reference known `V71-A` request rows
  - settlement records reference known `V71-A` request rows
  - dissent rows reference known requests and settlements where applicable
  - blocked requests cannot be ratified without settlement
  - unresolved blocking conflicts cannot be treated as settled
  - unresolved blocking gaps require deferral or carry-forward
  - every ratifying authority profile permits the exact ratification horizon
    used by the record
  - conflict and complementarity remain representable without forcing every
    relation into a blocking conflict posture
  - dissent is preserved when settlement is partial or unresolved
  - `no_dissent_recorded` requires searched coverage before it can mean no
    dissent was found
  - product wedge rows cannot be ratified for integration review
  - ratification records cannot authorize implementation, merge, release,
    product, runtime, dispatch, or external contest authority
  - settlement rows cannot directly select `V72`, `V74`, or `V75` work
- no amendment-scope boundary, post-ratification handoff, contained
  integration, product projection, commit/release authority, runtime permission,
  external contest participation, or dispatch widening lands in this slice.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS198.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+198",
  "target_path": "V71-B",
  "slice": "V71-B",
  "family": "V71",
  "branch_local_execution_target": "arc/v71-r2",
  "target_scope": "one_bounded_candidate_ratification_settlement_dissent_starter_slice",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS197.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS197_EDGES.md"
  ],
  "family_selector_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v61.md",
  "family_architecture_doc": "docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md",
  "slice_support_mapping_doc": "docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71B_IMPLEMENTATION_MAPPING_v0.md",
  "consumed_record_shapes": [
    "repo_candidate_ratification_request@1",
    "repo_ratification_authority_profile@1",
    "repo_ratification_request_scope_boundary@1"
  ],
  "emitted_record_shapes_for_v71b": [
    "repo_candidate_ratification_record@1",
    "repo_review_settlement_record@1",
    "repo_ratification_dissent_register@1"
  ],
  "selected_v71c_amendment_scope_or_handoff_for_v71b": false,
  "selected_v72_integration_for_v71b": false,
  "selected_product_workbench_for_v71b": false,
  "selected_release_authority_for_v71b": false,
  "selected_runtime_permission_or_dispatch_for_v71b": false
}
```

## Deferred

- `V71-C`: amendment-scope hardening and post-ratification handoff.
- `V72`: contained integration and release-posture review.
- `V73`: outcome review.
- `V74`: operator/product projection.
- `V75`: dispatch or multi-worker orchestration.
