# Draft ADEU External Branch Activation Review V80-B Implementation Mapping v0

Status: support / slice implementation mapping for planned `V80-B`.

Authority layer: support.

This note does not authorize implementation by itself. It specifies the likely
second slice that a future lock may select only after `V80-A` has shipped and
lean-closed on `main`.

## Slice Intent

`V80-B` should add external boundary, submission-authority, result-provenance,
and exception records over released `V80-A` external branch review requests:

- `repo_external_data_boundary@1`
- `repo_external_tool_boundary@1`
- `repo_external_submission_authority_review@1`
- `repo_external_result_provenance_contract@1`
- `repo_external_branch_exception_register@1`

The slice may describe bounded external data, tool, submission, result, and
withdrawal requirements. It must not ingest or export external data, invoke
external tools, submit to external systems, claim external result truth,
activate external branches, productize, release, or select a later family.

## Expected Files

Implementation files:

- `packages/adeu_repo_description/src/adeu_repo_description/external_branch_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Schema files:

- `packages/adeu_repo_description/schema/repo_external_data_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_external_tool_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_external_submission_authority_review.v1.json`
- `packages/adeu_repo_description/schema/repo_external_result_provenance_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_exception_register.v1.json`

Schema mirrors:

- `spec/repo_external_data_boundary.schema.json`
- `spec/repo_external_tool_boundary.schema.json`
- `spec/repo_external_submission_authority_review.schema.json`
- `spec/repo_external_result_provenance_contract.schema.json`
- `spec/repo_external_branch_exception_register.schema.json`

Tests:

- `packages/adeu_repo_description/tests/test_external_branch_review_v80b.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Fixtures:

- `apps/api/fixtures/repo_description/vnext_plus225/repo_external_data_boundary_v225_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus225/repo_external_tool_boundary_v225_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus225/repo_external_submission_authority_review_v225_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus225/repo_external_result_provenance_contract_v225_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus225/repo_external_branch_exception_register_v225_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus225/repo_external_branch_v225_reject_*.json`

## Source Basis

Required concrete source rows should cover:

- released `V80-A` external branch review request fixture;
- released `V80-A` source index fixture;
- released `V80-A` non-activation guardrail fixture;
- `V80-A` closeout evidence when available;
- relevant `V79-C` summary / handoff / closeout refs as upstream review
  substrate.

Globs remain discovery context only. External data, tool, and endpoint refs
must be concrete source rows, explicit absence rows, or explicitly blocked
placeholders.

## Minimum Row Vocabulary

Minimum external data boundary row fields:

- `data_boundary_ref`
- `candidate_ref`
- `source_refs`
- `external_branch_review_request_refs`
- `non_activation_guardrail_refs`
- `external_data_kind`
- `data_source_refs`
- `allowed_data_review_actions`
- `forbidden_data_actions`
- `data_transfer_posture`
- `data_boundary_posture`
- `limitation_note`

Minimum external tool boundary row fields:

- `external_tool_boundary_ref`
- `candidate_ref`
- `source_refs`
- `external_branch_review_request_refs`
- `non_activation_guardrail_refs`
- `tool_id`
- `tool_target_refs`
- `tool_endpoint_refs`
- `endpoint_ref_posture`
- `allowed_tool_review_actions`
- `forbidden_tool_actions`
- `external_tool_invocation_posture`
- `tool_boundary_posture`
- `limitation_note`

Minimum external submission authority review row fields:

- `submission_authority_review_ref`
- `candidate_ref`
- `source_refs`
- `external_branch_review_request_refs`
- `data_boundary_refs`
- `external_tool_boundary_refs`
- `authority_refs`
- `submission_target_refs`
- `submission_authority_posture`
- `external_submission_posture`
- `limitation_note`

Minimum external result provenance contract row fields:

- `result_provenance_contract_ref`
- `candidate_ref`
- `source_refs`
- `external_branch_review_request_refs`
- `data_boundary_refs`
- `external_tool_boundary_refs`
- `submission_authority_review_refs`
- `expected_result_source_refs`
- `result_capture_requirement_refs`
- `withdrawal_requirement_refs`
- `result_truth_posture`
- `withdrawal_posture`
- `limitation_note`

Minimum exception row fields:

- `exception_ref`
- `candidate_ref`
- `source_refs`
- `exception_kind`
- `exception_posture`
- `blocking_surface_refs`
- `required_next_surface`
- `limitation_note`

Minimum data transfer posture:

- `no_external_data_transfer_performed_by_v80`
- `data_transfer_requires_later_family`
- `data_transfer_forbidden_by_this_family`

Minimum external tool invocation posture:

- `no_external_tool_invocation_performed_by_v80`
- `external_tool_invocation_requires_later_family`
- `external_tool_invocation_forbidden_by_this_family`

Minimum endpoint ref posture:

- `endpoint_identifier_only`
- `endpoint_access_requires_later_authority`
- `endpoint_access_forbidden_by_this_family`
- `endpoint_absent_or_unknown`

Minimum external submission posture:

- `no_external_submission_performed_by_v80`
- `submission_requires_later_family`
- `submission_forbidden_by_this_family`

Minimum result truth posture:

- `external_result_truth_not_claimed`
- `result_truth_requires_later_review`
- `result_truth_forbidden_by_this_family`

## Validation Rules

Validators should enforce:

- all rows reference known `V80-A` request refs;
- all rows reference known source and non-activation guardrail rows;
- every reference row carries no-activation, no-submission, no-data-transfer,
  no-external-tool-invocation, or no-result-truth posture as applicable;
- data boundaries cannot perform data ingestion, export, or transfer;
- external tool boundaries cannot invoke tools;
- submission authority review cannot perform submission;
- result provenance contracts cannot claim external result truth;
- withdrawal requirements cannot perform withdrawal;
- concrete endpoint refs cannot become permission to mutate external systems;
- endpoint refs carry non-authorizing endpoint posture;
- blocking exceptions cannot be marked resolved by `V80-B`;
- product, runtime, release, and external authority gaps remain blockers or
  future-family-only.

## Mandatory Reject Fixtures

- data boundary with unknown `V80-A` request ref;
- data boundary that transfers external data;
- external tool boundary that invokes a tool;
- external endpoint string treated as access permission;
- submission authority review that submits;
- result provenance contract claiming external result truth;
- withdrawal requirement treated as withdrawal action;
- blocking exception resolved by prose;
- product or runtime pressure converted into external activation readiness;
- local command output treated as external result evidence;
- historical `V43` planning context treated as current authority.

## Non-Selection

`V80-B` does not select `V80-C`, external activation, external submission,
external tool invocation, data transfer, endpoint mutation, external result
truth, withdrawal action, command execution, target mutation, worker
assignment, dispatch execution, product authorization, release, benchmark
truth, model selection, living-memory authority, recursive policy amendment,
or any later family.
