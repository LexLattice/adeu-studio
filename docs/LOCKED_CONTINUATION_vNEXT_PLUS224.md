# LOCKED_CONTINUATION_vNEXT_PLUS224

## Status

Bounded starter lock draft for `V80-A` (external branch review request,
external branch source index, and external branch non-activation guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`V80-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `V80`
- slice: `V80-A`
- branch-local execution target: `arc/v80-r1`

## Purpose

Freeze the bounded `V80-A` starter slice so the repo can translate released
`V79-C` controlled execution review summary / post-review handoff / closeout
substrate into source-bound external branch activation review requests without
activating an external branch, entering `V43` contest participation,
submitting externally, invoking external tools, transferring data, or claiming
external result truth.

`vNext+224` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_repo_description` package. It does not authorize
`V80-B`, `V80-C`, data boundary rows, tool boundary rows, submission authority
rows, result provenance contracts, withdrawal contracts, exception registers,
summaries, handoffs, external activation, external submission, external tool
invocation, endpoint mutation, data transfer, command execution, dispatch,
product authorization, PR creation, commit, merge, release, benchmark truth,
global model selection, living-memory authority, recursive policy amendment,
or selection of `V81`.

The active `V80-A` implementation may add its own schema, model, validator,
fixture, and test files under this lock. That implementation work is distinct
from external branch activation. `V80-A` may make external branch review
pressure visible; it must not record that an external branch may activate, an
external submission may occur, an external endpoint may be accessed, or any
downstream product / runtime / release action is authorized.

## Instantiated Here

- `V80-A` instantiates one bounded external branch review starter seam:
  - existing repo-owned package only:
    - `adeu_repo_description`
  - consumed released basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS223.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS223.md`
    - `docs/ASSESSMENT_vNEXT_PLUS223_EDGES.md`
    - `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79_FAMILY_CLOSEOUT_v0.md`
    - `artifacts/agent_harness/v223/evidence_inputs/v79_family_closeout_alignment_v223.json`
    - `artifacts/agent_harness/v223/evidence_inputs/v79c_controlled_execution_review_closeout_evidence_v223.json`
    - `apps/api/fixtures/repo_description/vnext_plus223/repo_controlled_execution_review_summary_v223_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus223/repo_post_controlled_execution_review_handoff_v223_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus223/repo_controlled_execution_review_family_closeout_alignment_v223_reference.json`
  - consumed support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v70.md`
    - `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
    - `docs/ARCHITECTURE_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.md`
    - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.json`
  - branch-history context, not activation authority by itself:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`
  - emitted starter record shapes:
    - `repo_external_branch_review_request@1`
    - `repo_external_branch_source_index@1`
    - `repo_external_branch_non_activation_guardrail@1`

## Required Starter Vocabulary

Minimum external branch source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `external_branch_source_role`
- `source_horizon`
- `limitation_note`

Minimum external branch source role:

- `v79_controlled_execution_summary_source`
- `v79_post_controlled_execution_review_handoff_source`
- `v79_family_closeout_source`
- `v79_combined_dogfood_context`
- `post_v74_roadmap_context`
- `v43_branch_posture_source`
- `v43_branch_posture_absence_marker`
- `external_objective_source`
- `support_process_context`
- `absence_marker`

Rows with `v79_combined_dogfood_context`, `post_v74_roadmap_context`, or
`support_process_context` may contextualize external branch review. They must
not be the only eligibility sources for `eligible_for_external_branch_review`.

Rows with `external_objective_source` may support request existence and
`request_recorded_objective_only`; they must not by themselves support
`eligible_for_external_branch_review`.

Minimum external branch review request fields:

- `external_branch_review_request_ref`
- `candidate_ref`
- `source_refs`
- `v79_summary_refs`
- `v79_handoff_refs`
- `v79_closeout_refs`
- `branch_family_ref`
- `branch_posture_currentness`
- `external_objective_kind`
- `branch_review_posture`
- `requested_data_boundary_horizon`
- `requested_tool_boundary_horizon`
- `requested_submission_authority_horizon`
- `required_result_provenance_posture`
- `required_withdrawal_posture`
- `required_authority_refs`
- `guardrail_refs`
- `external_activation_posture`
- `external_submission_posture`
- `external_tool_invocation_posture`
- `execution_posture`
- `odeu_lanes`
- `limitation_note`

Minimum branch posture currentness:

- `current_branch_posture`
- `historical_branch_planning_context`
- `explicit_absence_marker`
- `stale_or_superseded`
- `unknown_needs_review`

Minimum branch review posture:

- `request_recorded_objective_only`
- `eligible_for_external_branch_review`
- `blocked_by_missing_source`
- `blocked_by_missing_v43_branch_posture`
- `blocked_by_missing_external_objective`
- `blocked_by_product_authority_gap`
- `blocked_by_runtime_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

`eligible_for_external_branch_review` requires:

- released `V79-C` summary, handoff, or family-closeout source role;
- current `v43_branch_posture_source`;
- `branch_posture_currentness = current_branch_posture`.

Historical `V43` planning context and external objective sources cannot create
eligibility by themselves.

Minimum external activation posture:

- `no_external_branch_activation_performed_by_v80`
- `external_activation_requires_later_family`
- `external_activation_forbidden_by_this_family`

Minimum external submission posture:

- `no_external_submission_performed_by_v80`
- `submission_requires_later_family`
- `submission_forbidden_by_this_family`

Minimum external tool invocation posture:

- `no_external_tool_invocation_performed_by_v80`
- `external_tool_invocation_requires_later_family`
- `external_tool_invocation_forbidden_by_this_family`

Reference rows should carry:

- `external_activation_posture =
  no_external_branch_activation_performed_by_v80`
- `external_submission_posture = no_external_submission_performed_by_v80`
- `external_tool_invocation_posture =
  no_external_tool_invocation_performed_by_v80`
- `execution_posture = no_execution_performed_by_v80`

Minimum non-activation guardrail fields:

- `guardrail_ref`
- `candidate_ref`
- `source_refs`
- `external_branch_review_request_refs`
- `forbidden_external_actions`
- `forbidden_downstream_authority`
- `guardrail_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `repo_external_branch_review_request@1`
  - `repo_external_branch_source_index@1`
  - `repo_external_branch_non_activation_guardrail@1`
- deterministic reference and reject fixtures for the bounded `V80-A` starter
  family only;
- a hand-curated reference fixture seeded from released `V79-C` fixture
  material and the `V68` through `V79` dogfood support source;
- validators that prove:
  - external branch review requests reference known `V79-C` rows or explicit
    absence rows;
  - context-only sources cannot make a request eligible;
  - external objective source rows can support request existence but not
    eligibility without current `V43` branch posture;
  - historical `DRAFT_NEXT_ARC_OPTIONS_v43.md` context cannot become current
    activation authority;
  - `eligible_for_external_branch_review` requires current branch posture;
  - product and runtime pressure remain blocked or out of scope;
  - controlled execution handoffs cannot become external execution authority;
  - data-boundary, tool-boundary, submission-authority, result-provenance,
    withdrawal, and exception refs are absent from `V80-A` request rows;
  - external URLs or endpoint strings cannot become access permission;
  - local command output and local tool results cannot become external result
    evidence;
  - guardrails have non-empty forbidden external action and downstream
    authority lists;
  - `V80-A` cannot emit `V80-B` or `V80-C` surfaces;
- focused tests for the new `V80-A` surfaces and export-schema parity;
- no external activation, `V43` contest participation, external submission,
  external tool invocation, endpoint mutation, data transfer, external result
  truth, command execution, tool invocation, target mutation, worker
  assignment, dispatch execution, product authorization, PR creation, commit,
  merge, release, benchmark truth, model selection, living-memory authority,
  recursive policy amendment, or `V81` selection lands in this slice.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS224.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+224",
  "target_path": "V80-A",
  "slice": "V80-A",
  "family": "V80",
  "branch_local_execution_target": "arc/v80-r1",
  "target_scope": "one_bounded_external_branch_review_request_source_guardrail_starter_slice",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "api_surfaces": [],
  "cli_or_validation_entrypoints_for_v80a": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS223.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS223.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS223_EDGES.md"
  ],
  "selected_record_shapes": [
    "repo_external_branch_review_request@1",
    "repo_external_branch_source_index@1",
    "repo_external_branch_non_activation_guardrail@1"
  ],
  "forbidden_record_shapes": [
    "repo_external_data_boundary@1",
    "repo_external_tool_boundary@1",
    "repo_external_submission_authority_review@1",
    "repo_external_result_provenance_contract@1",
    "repo_external_branch_exception_register@1",
    "repo_external_branch_readiness_summary@1",
    "repo_post_external_branch_review_handoff@1",
    "repo_external_branch_review_family_closeout_alignment@1"
  ],
  "non_authorized_surfaces": [
    "external_branch_activation",
    "v43_contest_participation",
    "external_submission",
    "external_tool_invocation",
    "external_endpoint_mutation",
    "external_data_transfer",
    "external_result_truth",
    "command_execution",
    "tool_invocation",
    "target_mutation",
    "worker_assignment",
    "dispatch_execution",
    "product_authorization",
    "pr_creation",
    "commit",
    "merge",
    "release",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v81_selection"
  ]
}
```
