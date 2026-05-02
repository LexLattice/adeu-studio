# Draft ADEU External Branch Activation Review V80-C Implementation Mapping v0

Status: support / slice implementation mapping for planned `V80-C`.

Authority layer: support.

This note does not authorize implementation by itself. It specifies the likely
closeout slice that a future lock may select only after `V80-A` and `V80-B`
have shipped and lean-closed on `main`.

## Slice Intent

`V80-C` should add summary, post-review handoff, and family closeout alignment
records over released `V80-A` and `V80-B` substrate:

- `repo_external_branch_readiness_summary@1`
- `repo_post_external_branch_review_handoff@1`
- `repo_external_branch_review_family_closeout_alignment@1`

The slice may summarize whether an external branch review package is ready,
warning-ready, blocked, deferred, future-family-only, or out of scope. It must
not activate external branches, submit externally, invoke external tools,
transfer data, claim external result truth, productize, release, or select
`V81`.

## Expected Files

Implementation files:

- `packages/adeu_repo_description/src/adeu_repo_description/external_branch_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Schema files:

- `packages/adeu_repo_description/schema/repo_external_branch_readiness_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_external_branch_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_review_family_closeout_alignment.v1.json`

Schema mirrors:

- `spec/repo_external_branch_readiness_summary.schema.json`
- `spec/repo_post_external_branch_review_handoff.schema.json`
- `spec/repo_external_branch_review_family_closeout_alignment.schema.json`

Tests:

- `packages/adeu_repo_description/tests/test_external_branch_review_v80c.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Fixtures:

- `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_readiness_summary_v226_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus226/repo_post_external_branch_review_handoff_v226_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_review_family_closeout_alignment_v226_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_v226_reject_*.json`

## Source Basis

Required concrete source rows should cover:

- released `V80-A` request / source / guardrail fixtures;
- released `V80-B` data / tool / submission / provenance / exception fixtures;
- `V80-B` closeout evidence when available;
- `V79-C` closeout and family alignment as lineage evidence.

## Minimum Row Vocabulary

Minimum external branch readiness summary row fields:

- `external_branch_summary_ref`
- `candidate_ref`
- `external_branch_review_request_refs`
- `data_boundary_refs`
- `external_tool_boundary_refs`
- `submission_authority_review_refs`
- `result_provenance_contract_refs`
- `exception_refs`
- `authority_refs`
- `summary_posture`
- `ready_basis_posture`
- `carried_blocker_refs`
- `external_activation_posture`
- `external_submission_posture`
- `external_tool_invocation_posture`
- `data_transfer_posture`
- `result_truth_posture`
- `non_activation_guardrail_refs`
- `limitation_note`

Minimum post-external-branch-review handoff row fields:

- `handoff_ref`
- `candidate_ref`
- `external_branch_summary_refs`
- `data_boundary_refs`
- `external_tool_boundary_refs`
- `submission_authority_review_refs`
- `result_provenance_contract_refs`
- `carried_exception_refs`
- `handoff_target`
- `handoff_external_authority_horizon`
- `handoff_subject_horizon`
- `handoff_posture`
- `handoff_external_activation_status`
- `required_later_authority_refs`
- `external_activation_posture`
- `external_submission_posture`
- `external_tool_invocation_posture`
- `data_transfer_posture`
- `result_truth_posture`
- `non_activation_guardrail_refs`
- `limitation_note`

Minimum family closeout alignment fields:

- `family`
- `closed_by_arc`
- `closed_slice_ladder`
- `consumed_source_families`
- `shipped_record_shapes`
- `external_branch_boundary`
- `unselected_future_surfaces`
- `future_family_authority`
- `limitation_note`

## Summary And Handoff Postures

Minimum summary posture:

- `external_branch_review_ready`
- `external_branch_review_ready_with_nonblocking_warnings`
- `blocked_by_missing_v43_branch_posture`
- `blocked_by_missing_data_boundary`
- `blocked_by_missing_tool_boundary`
- `blocked_by_missing_submission_authority`
- `blocked_by_missing_result_provenance`
- `blocked_by_missing_withdrawal_posture`
- `blocked_by_product_authority_gap`
- `blocked_by_runtime_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum handoff target:

- `future_external_branch_activation_authority_review`
- `future_external_participation_or_submission_review`
- `future_external_result_review`
- `future_product_review`
- `future_runtime_execution_review`
- `future_cross_corpus_governance_review`
- `future_family_review`
- `deferred_no_selection`

Minimum handoff external authority horizon:

- `branch_posture_review`
- `data_boundary_review`
- `external_tool_access_review`
- `submission_authority_review`
- `result_provenance_review`
- `withdrawal_authority_review`
- `external_participation_review`

Minimum handoff posture:

- `ready_for_later_review`
- `ready_with_nonblocking_warnings`
- `blocked_by_required_later_authority`
- `blocked_by_v43_branch_posture_gap`
- `blocked_by_data_boundary_gap`
- `blocked_by_tool_boundary_gap`
- `blocked_by_submission_authority_gap`
- `blocked_by_result_provenance_gap`
- `blocked_by_withdrawal_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum ready basis posture:

- `ready_no_blockers`
- `ready_with_nonblocking_warnings`
- `not_ready_blockers_remain`
- `settlement_or_authority_review_requested_for_blockers`
- `future_family_only`
- `rejected_out_of_scope`

Every summary and handoff row must carry no-external-activation,
no-external-submission, no-external-tool-invocation, no-data-transfer, and
no-result-truth posture.

## Validation Rules

Validators should enforce:

- summaries reference known `V80-A` request refs;
- ready summaries reference known `V80-B` data, tool, submission, provenance,
  and exception rows;
- ready summaries cannot hide blocking exceptions;
- warning-ready summaries may carry warning refs but not blocking refs;
- if `carried_blocker_refs` is non-empty, handoff posture must not be
  `ready_for_later_review` unless `ready_basis_posture =
  settlement_or_authority_review_requested_for_blockers`;
- handoffs fail closed if required summary / boundary refs are absent;
- future external branch activation review handoffs require data-boundary,
  tool-boundary, submission-authority, result-provenance, withdrawal, and
  later-authority refs;
- product handoffs require product authority refs and cannot become external
  activation readiness;
- runtime execution handoffs require runtime authority refs and cannot become
  external activation readiness;
- family closeout alignment closes `V80` without selecting `V81`.

## Mandatory Reject Fixtures

- summary with unknown `V80-A` request ref;
- ready summary without concrete `V43` / external branch posture;
- ready summary without data boundary refs;
- ready summary without result provenance refs;
- warning-ready summary carrying blocking exception refs;
- handoff that activates an external branch;
- handoff that submits externally;
- handoff that invokes an external tool;
- external activation handoff without later authority refs;
- product pressure routed to external branch activation review;
- runtime execution pressure routed to external branch activation review;
- closeout claiming external activation, external submission, external result
  truth, product authorization, PR / commit / merge / release, benchmark
  truth, model selection, living-memory authority, recursive policy amendment,
  or `V81` selection.

## Non-Selection

`V80-C` may close `V80` and carry future pressure, but it does not select
`V81` or any later family. It does not activate external branches, submit
externally, invoke external tools, transfer data, claim external result truth,
run commands, assign workers, dispatch, productize, release, create
living-memory authority, or amend recursive policy.
