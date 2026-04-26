# Draft ADEU Candidate Ratification Review V71A Implementation Mapping v0

Status: support note for the planned `V71-A` starter implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the
starter `V71-A` slice should create a bounded ratification request,
authority-profile, and scope-boundary schema backbone without turning request
intake into ratification.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v61.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71C_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V71-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not the same thing as the active-slice canonical
starter bundle.

When `V71-A` is implemented, the expected active-slice starter bundle is:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS197.md`
- `docs/ASSESSMENT_vNEXT_PLUS197_EDGES.md`

That future lock should select only the narrow starter slice described here.

## Carry Forward

- `docs/DRAFT_NEXT_ARC_OPTIONS_v61.md` as the current `V71` selector draft
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
  as closed review-classification-family evidence
- released `V70-C` summary and pre-ratification handoff fixtures as the first
  ratification request input
- `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.md`
  as support-layer evidence that V68/V69/V70 compose without authority
  laundering
- released `V68` / `V69` surfaces as source and authority-layer precedent

If an expected carry-forward source is missing when the active lock is drafted,
the starter fixture should represent that absence with an explicit source row
and source-presence posture. It should not reconstruct request state from prose
memory.

## Starter Surfaces

Candidate new `V71-A` surfaces:

- `repo_candidate_ratification_request@1`
- `repo_ratification_authority_profile@1`
- `repo_ratification_request_scope_boundary@1`

Those surfaces should remain bounded to:

- one explicit source set over released `V70-C` rows;
- one ratification source register;
- one ratification request register;
- one authority profile register;
- one scope boundary register;
- one hand-curated reference fixture;
- reject fixtures for source-free requests, self-ratification, authority
  laundering, product-wedge routing, and downstream authority leakage.

They should decide only:

- how ratification requests are represented;
- how authority actor posture is represented;
- how requested ratification horizon is represented;
- how scope boundaries and forbidden downstream roles are represented;
- how `ready_for_v71_review`, `blocked_by_conflict`, and
  `deferred_to_future_family` handoffs enter or do not enter `V71` review.

They should keep out of scope:

- final ratification records;
- settlement records;
- dissent registers;
- amendment scope;
- post-ratification handoff;
- implementation scheduling;
- product workbench;
- dispatch or execution widening.

## Starter Source Binding

`V71-A` reference fixtures should carry at least:

- `ratification_request_id`
- `authority_profile_id`
- `request_scope_boundary_id`
- `snapshot_id`
- `source_set_id`
- `coverage_horizon`
- `candidate_input_refs`
- `ratification_source_rows`
- `request_rows`
- `authority_profile_rows`
- `request_scope_boundary_rows`
- `non_implementation_summary`

Request rows should include:

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

Authority profile rows should include:

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

Request scope boundary rows should include:

- `request_scope_boundary_ref`
- `candidate_ref`
- `ratification_source_refs`
- `request_refs`
- `allowed_ratification_actions`
- `forbidden_downstream_roles`
- `allowed_next_review_surfaces`
- `non_implementation_guardrail`

## Starter Validation Split

Local model validators should validate one payload only:

- schema shape;
- frozen enums;
- sorted unique row identities;
- no absolute repo paths;
- no free-text authority layers;
- no request row with empty source handoff refs;
- no request row with empty ratification source refs;
- no request row with dangling summary or handoff refs;
- no authority profile with empty authority source refs;
- no authority profile with empty forbidden downstream roles;
- no model, tool, support, or transcript source granted ratification authority
  without explicit lock-level source;
- no scope boundary that allows implementation, integration, release, product,
  runtime, or dispatch;
- no final ratification outcome inside `V71-A`.

Bundle validators should validate cross-artifact relationships:

- request candidates come from released `V70-C` handoff rows;
- request rows reference known `V70-C` summary and handoff refs;
- blocked handoffs map to settlement-required request posture;
- ready handoffs may become eligible request posture only when no blockers
  remain;
- future-family handoffs remain future-family review and do not become `V71`
  ratification requests;
- authority profiles and scope boundaries referenced by requests exist;
- every request, authority profile, and scope boundary resolves through
  ratification source rows;
- no request emits implementation, release, product, runtime, or dispatch
  authority.

## Starter Constants

Expected constants:

- `REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA = "repo_candidate_ratification_request@1"`
- `REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA = "repo_ratification_authority_profile@1"`
- `REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA = "repo_ratification_request_scope_boundary@1"`

The repo-native field name should be `schema`, not `schema_id`.

## Mandatory Reject Cases

`V71-A` should reject:

- ratification request for unknown candidate;
- ratification request sourced only from prose memory;
- ratification request with no `V70-C` handoff refs;
- ratification request with dangling summary refs;
- blocked handoff marked eligible without settlement requirement;
- product wedge routed to `V71` ratification review;
- model reviewer granted self-ratification authority;
- tool validator treated as ratification proof;
- support doc marked as ratification authority;
- transcript content treated as truth or ratification authority;
- authority profile with empty forbidden downstream roles;
- scope boundary permitting implementation, integration, release, product,
  runtime, or dispatch;
- `V71-A` request row carrying final ratification, rejection, or adoption
  outcome.

## First Reference Fixture Intent

The first reference fixture should be a post-`V70` seed, not a final exhaustive
ratification ledger.

Required coverage:

- at least one `ready_for_v71_review` handoff admitted as eligible request;
- at least one `blocked_by_conflict` handoff admitted as settlement-required
  request;
- at least one `future_family_review` handoff preserved as non-`V71`
  deferral;
- at least one authority profile with ratification authority bound to an
  explicit repo source;
- at least one model/tool/support source profile that is review-only or
  evidence-only, not ratifying;
- at least one scope boundary with non-empty forbidden downstream roles;
- no candidate ratified, adopted, integrated, released, productized, or
  dispatched.

Recommended first fixture names:

- `repo_candidate_ratification_request_v197_reference.json`
- `repo_ratification_authority_profile_v197_reference.json`
- `repo_ratification_request_scope_boundary_v197_reference.json`
- `repo_candidate_ratification_v197_reject_missing_v70c_handoff_ref.json`
- `repo_candidate_ratification_v197_reject_dangling_summary_ref.json`
- `repo_candidate_ratification_v197_reject_blocked_handoff_marked_eligible.json`
- `repo_candidate_ratification_v197_reject_product_wedge_to_v71.json`
- `repo_candidate_ratification_v197_reject_model_self_ratification.json`
- `repo_candidate_ratification_v197_reject_tool_pass_as_ratification.json`
- `repo_candidate_ratification_v197_reject_support_doc_as_ratification_authority.json`
- `repo_candidate_ratification_v197_reject_scope_allows_release.json`
- `repo_candidate_ratification_v197_reject_v71a_records_final_ratification.json`
