# LOCKED_CONTINUATION_vNEXT_PLUS218

## Status

Bounded starter lock draft for `V78-A` (runtime execution authority request,
runtime authority source index, and runtime authority non-action guardrail).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`V78-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `V78`
- slice: `V78-A`
- branch-local execution target: `arc/v78-r1`

## Purpose

Freeze the bounded `V78-A` starter slice so the repo can translate released
`V77-C` runtime authority posture / summary / handoff / closeout substrate
into source-bound runtime execution authority requests without granting
authority, invoking tools, or executing commands.

`vNext+218` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_repo_description` package. It does not authorize
runtime execution authority decisions, tool-use permission envelopes,
command-scope authorization boundaries, runtime authority exception registers,
readiness summaries, pre-execution-authority-review handoffs, command
execution, tool invocation, worker assignment, dispatch execution, product
authorization, external branch activation, PR creation, commit, merge, release,
benchmark truth, global model selection, living-memory authority, recursive
policy amendment, or selection of a later family.

The active `V78-A` implementation may add its own schema, model, validator,
fixture, and test files under this lock. That implementation work is distinct
from command execution, tool invocation, runtime dispatch, product UI,
external branch work, release work, living graph memory, or recursive policy
amendment. `V78-A` may make runtime authority pressure visible; it must not
record that a command may run, a tool may be invoked, execution authority has
been granted, or any downstream product / runtime / release / external action
is authorized.

## Instantiated Here

- `V78-A` instantiates one bounded runtime execution authority starter seam:
  - existing repo-owned package only:
    - `adeu_repo_description`
  - consumed released basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS217.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS217.md`
    - `docs/ASSESSMENT_vNEXT_PLUS217_EDGES.md`
    - `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77_FAMILY_CLOSEOUT_v0.md`
    - `artifacts/agent_harness/v217/evidence_inputs/v77_family_closeout_alignment_v217.json`
    - `artifacts/agent_harness/v217/evidence_inputs/v77c_runtime_permission_closeout_evidence_v217.json`
    - `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_authority_posture_v217_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_review_summary_v217_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus217/repo_post_runtime_permission_review_handoff_v217_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_family_closeout_alignment_v217_reference.json`
  - consumed support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v68.md`
    - `docs/ARCHITECTURE_ADEU_RUNTIME_EXECUTION_AUTHORITY_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.md`
    - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.json`
  - emitted starter record shapes:
    - `repo_runtime_execution_authority_request@1`
    - `repo_runtime_authority_source_index@1`
    - `repo_runtime_authority_non_action_guardrail@1`

## Required Starter Vocabulary

Minimum runtime authority source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `runtime_authority_source_role`
- `source_horizon`
- `limitation_note`

Minimum runtime authority source role:

- `v77_authority_posture_source`
- `v77_runtime_summary_source`
- `v77_post_runtime_permission_review_handoff_source`
- `v77_family_closeout_source`
- `v77_command_preflight_context`
- `v77_effect_envelope_context`
- `v77_telemetry_requirement_context`
- `v77_rollback_contract_context`
- `combined_dogfood_source`
- `support_context`
- `absence_marker`

Support context rows may contextualize runtime authority review. They must not
be the only eligibility sources for
`eligible_for_runtime_execution_authority_review`.

Minimum runtime execution authority request fields:

- `authority_request_ref`
- `candidate_ref`
- `source_refs`
- `v77_authority_posture_refs`
- `v77_summary_refs`
- `v77_handoff_refs`
- `v77_closeout_refs`
- `requested_authority_horizon`
- `authority_request_posture`
- `requested_tool_use_refs`
- `requested_command_scope_refs`
- `required_authority_source_refs`
- `authority_requirement_rows`
- `target_boundary_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `guardrail_refs`
- `execution_posture`
- `tool_invocation_posture`
- `odeu_lanes`
- `limitation_note`

Minimum authority request posture:

- `eligible_for_runtime_execution_authority_review`
- `blocked_by_missing_source`
- `blocked_by_missing_authority_source`
- `blocked_by_product_authority_gap`
- `blocked_by_external_branch_gap`
- `blocked_by_unbounded_command_scope`
- `blocked_by_missing_telemetry_requirement`
- `blocked_by_missing_rollback_requirement`
- `future_family_only`
- `rejected_out_of_scope`

Minimum embedded authority requirement row fields:

- `authority_requirement_ref`
- `candidate_ref`
- `authority_kind`
- `required_for_horizon`
- `source_refs`
- `source_presence_posture`
- `authority_gap_posture`
- `limitation_note`

Minimum authority kind:

- `maintainer_authority`
- `policy_authority`
- `runtime_execution_review_authority`
- `tool_use_review_authority`
- `product_authorization`
- `external_branch_activation`
- `release_authority`
- `recursive_policy_authority`

Minimum execution posture:

- `no_execution_performed_by_v78`
- `execution_requires_later_family`
- `execution_forbidden_by_this_family`

Starter reference rows must use `execution_posture =
no_execution_performed_by_v78`.

Minimum non-action guardrail fields:

- `guardrail_ref`
- `candidate_ref`
- `authority_request_refs`
- `forbidden_runtime_actions`
- `forbidden_downstream_authority`
- `execution_posture`
- `tool_invocation_posture`
- `authority_gap_refs`
- `source_refs`
- `limitation_note`

Minimum tool invocation posture:

- `no_tool_invocation_performed_by_v78`
- `tool_invocation_requires_later_family`
- `tool_invocation_forbidden_by_this_family`

Reference rows should carry:

- `execution_posture = no_execution_performed_by_v78`
- `tool_invocation_posture = no_tool_invocation_performed_by_v78`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `repo_runtime_execution_authority_request@1`
  - `repo_runtime_authority_source_index@1`
  - `repo_runtime_authority_non_action_guardrail@1`
- deterministic reference and reject fixtures for the bounded `V78-A` starter
  family only;
- a hand-curated reference fixture seeded from released `V77-C` fixture
  material and the `V68` through `V77` dogfood support source;
- validators that prove:
  - runtime authority requests reference known `V77-C` rows or explicit
    absence rows;
  - support context cannot be the only eligibility source;
  - required authority is represented through typed authority requirement rows;
  - product pressure remains product-blocked or future-product-review-routed;
  - external branch pressure remains blocked or future-family-only unless
    concrete `V43` posture exists;
  - command preflight cannot become command execution;
  - tool-use request cannot become tool invocation;
  - local command output or a passing tool result cannot become authority
    evidence;
  - target refs cannot become command-scope authorization;
  - guardrails have non-empty forbidden runtime and downstream authority lists;
  - `V78-A` cannot emit `V78-B` or `V78-C` surfaces;
- focused tests for the new `V78-A` surfaces and export-schema parity;
- no command execution, tool invocation, worker assignment, dispatch
  execution, product authorization, external branch activation, PR creation,
  commit, merge, release, benchmark truth, model selection, living-memory
  authority, or recursive policy amendment lands in this slice.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+218",
  "target_path": "V78-A",
  "slice": "V78-A",
  "family": "V78",
  "branch_local_execution_target": "arc/v78-r1",
  "target_scope": "one_bounded_runtime_execution_authority_request_source_guardrail_starter_slice",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "api_surfaces": [],
  "cli_or_validation_entrypoints_for_v78a": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS217.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS217.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS217_EDGES.md"
  ],
  "selected_record_shapes": [
    "repo_runtime_execution_authority_request@1",
    "repo_runtime_authority_source_index@1",
    "repo_runtime_authority_non_action_guardrail@1"
  ],
  "consumed_record_shapes": [
    "repo_runtime_permission_authority_posture@1",
    "repo_runtime_permission_review_summary@1",
    "repo_post_runtime_permission_review_handoff@1",
    "repo_runtime_permission_family_closeout_alignment@1"
  ],
  "must_not_select": [
    "V78-B",
    "V78-C",
    "runtime_execution_authority_decision",
    "tool_use_permission_envelope",
    "command_scope_authorization_boundary",
    "runtime_authority_exception_register",
    "runtime_authority_readiness_summary",
    "pre_execution_authority_review_handoff",
    "command_execution",
    "tool_invocation",
    "worker_assignment",
    "dispatch_execution",
    "product_authorization",
    "external_branch_activation",
    "pr_creation",
    "commit",
    "merge",
    "release",
    "benchmark_truth",
    "global_model_selection",
    "living_memory_authority",
    "recursive_policy_amendment"
  ]
}
```

## Expected Verification

- for this docs-only starter bundle:
  - `make arc-start-check ARC=218`
- before any Python implementation PR:
  - `make check`
