# LOCKED_CONTINUATION_vNEXT_PLUS219

## Status

Bounded starter lock draft for `V78-B` (runtime execution authority decision,
tool-use permission envelope, command-scope authorization boundary, and
runtime authority exception register).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`V78-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `V78`
- slice: `V78-B`
- branch-local execution target: `arc/v78-r2`

## Purpose

Freeze the bounded `V78-B` starter slice so the repo can translate released
`V78-A` runtime execution authority request, source-index, and non-action
guardrail substrate into runtime execution authority decision, tool-use
permission envelope, command-scope authorization boundary, and runtime
authority exception records without executing commands, invoking tools, or
granting live runtime permission.

`vNext+219` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_repo_description` package. It does not authorize
`V78-C`, readiness summaries, pre-execution-authority-review handoffs, family
closeout alignment, command execution, tool invocation, worker assignment,
dispatch execution, product authorization, external branch activation, PR
creation, commit, merge, release, benchmark truth, global model selection,
living-memory authority, recursive policy amendment, or selection of a later
family.

The active `V78-B` implementation may add its own schema, model, validator,
fixture, and test files under this lock. That implementation work is distinct
from executing a command or invoking a tool. `V78-B` may make later-review-only
authority decisions and permission envelopes machine-checkable; it must not
record that a command ran, a tool was invoked, execution authorization exists
inside `V78`, or any downstream product / runtime / release / external action
is authorized.

## Instantiated Here

- `V78-B` instantiates one bounded runtime execution authority decision /
  permission-envelope review starter seam:
  - existing repo-owned package only:
    - `adeu_repo_description`
  - consumed released basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS218.md`
    - `docs/ASSESSMENT_vNEXT_PLUS218_EDGES.md`
    - `artifacts/agent_harness/v218/evidence_inputs/v78a_runtime_execution_authority_closeout_evidence_v218.json`
    - `artifacts/agent_harness/v218/evidence_inputs/metric_key_continuity_assertion_v218.json`
    - `artifacts/agent_harness/v218/evidence_inputs/runtime_observability_comparison_v218.json`
    - released `V78-A` runtime execution authority request, runtime authority
      source index, and runtime authority non-action guardrail surfaces
  - consumed support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v68.md`
    - `docs/ARCHITECTURE_ADEU_RUNTIME_EXECUTION_AUTHORITY_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted starter record shapes:
    - `repo_runtime_execution_authority_decision@1`
    - `repo_tool_use_permission_envelope@1`
    - `repo_command_scope_authorization_boundary@1`
    - `repo_runtime_authority_exception_register@1`
  - consumed `V78-A` record shapes:
    - `repo_runtime_execution_authority_request@1`
    - `repo_runtime_authority_source_index@1`
    - `repo_runtime_authority_non_action_guardrail@1`

## Required Starter Vocabulary

Minimum runtime execution authority decision fields:

- `authority_decision_ref`
- `authority_request_refs`
- `candidate_ref`
- `decision_posture`
- `decision_horizon`
- `authorized_surface_kind`
- `authority_grant_horizon`
- `authority_source_refs`
- `authority_actor_refs`
- `tool_use_permission_refs`
- `command_scope_boundary_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `exception_refs`
- `execution_posture`
- `execution_authorization_posture`
- `non_action_guardrail_refs`
- `limitation_note`

Minimum decision posture:

- `review_authority_granted_for_bounded_execution_surface`
- `review_authority_denied`
- `review_authority_deferred`
- `review_authority_blocked_by_missing_source`
- `review_authority_blocked_by_missing_scope`
- `review_authority_blocked_by_missing_telemetry`
- `review_authority_blocked_by_missing_rollback`
- `review_authority_future_family_only`
- `review_authority_rejected_out_of_scope`

Minimum authorized surface kind:

- `later_execution_review_surface`
- `later_tool_invocation_review_surface`
- `later_telemetry_review_surface`
- `later_rollback_review_surface`
- `future_family_review_surface`

Minimum execution authorization posture:

- `execution_not_authorized_by_v78`
- `execution_requires_later_family`
- `execution_forbidden_by_this_family`

Reference rows must use `execution_authorization_posture =
execution_not_authorized_by_v78` and `execution_posture =
no_execution_performed_by_v78`.

Minimum tool-use permission envelope fields:

- `tool_permission_ref`
- `authority_request_refs`
- `candidate_ref`
- `tool_id`
- `tool_target_horizon`
- `tool_target_refs`
- `permission_posture`
- `permission_scope_boundary_refs`
- `authority_source_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `exception_refs`
- `tool_invocation_posture`
- `limitation_note`

Minimum permission posture:

- `tool_use_permission_granted_for_later_execution_review`
- `tool_use_permission_denied`
- `tool_use_permission_deferred`
- `tool_use_permission_blocked_by_missing_authority`
- `tool_use_permission_future_family_only`
- `tool_use_not_applicable`

Tool-use permission envelopes must be horizon-bound and target-bound. Global
tool permission must reject. Tool applicability from earlier families is not
tool-use permission, and no `V78-B` row may invoke a tool.

Minimum command-scope authorization boundary fields:

- `command_scope_ref`
- `authority_request_refs`
- `candidate_ref`
- `command_intent_kind`
- `target_resolution_kind`
- `target_refs`
- `authorized_scope_posture`
- `allowed_effect_surface_refs`
- `forbidden_effect_surface_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `authority_source_refs`
- `exception_refs`
- `execution_posture`
- `limitation_note`

Minimum authorized scope posture:

- `bounded_scope_authorized_for_later_execution_review`
- `scope_denied`
- `scope_deferred`
- `scope_blocked_by_missing_target`
- `scope_blocked_by_unbounded_target`
- `scope_blocked_by_missing_telemetry`
- `scope_blocked_by_missing_rollback`
- `scope_future_family_only`

Bounded scope must cite concrete target refs. Globs are discovery context only
and must reject as scope authorization. Command-scope authorization is not
command execution, and target scope is not permission to mutate target state
inside `V78`.

Minimum runtime authority exception register fields:

- `exception_ref`
- `candidate_ref`
- `authority_request_refs`
- `exception_kind`
- `exception_posture`
- `blocking_surface_refs`
- `source_refs`
- `required_next_surface`
- `limitation_note`

Minimum exception kind:

- `missing_authority_source`
- `missing_command_scope`
- `unbounded_target`
- `missing_telemetry_requirement`
- `missing_rollback_requirement`
- `tool_permission_gap`
- `product_authority_gap`
- `external_branch_authority_gap`
- `release_authority_gap`
- `command_output_without_prior_authority`
- `unknown_needs_review`

Exceptions may be blocking, warning-only, carried-forward, not applicable, or
future-family-only. They must not be resolved by prose or by command output.

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `repo_runtime_execution_authority_decision@1`
  - `repo_tool_use_permission_envelope@1`
  - `repo_command_scope_authorization_boundary@1`
  - `repo_runtime_authority_exception_register@1`
- deterministic reference and reject fixtures for the bounded `V78-B` starter
  family only;
- a hand-curated reference fixture seeded from released `V78-A` fixture
  material;
- validators that prove:
  - decision, tool-permission, command-scope, and exception rows reference
    known `V78-A` authority request and guardrail rows;
  - grant-like decision posture requires concrete authority sources and
    later-review-only horizons;
  - authority decisions cannot imply command execution or tool invocation;
  - tool-use permission is target-bound, horizon-bound, and not global;
  - tool applicability cannot become tool-use permission;
  - command-scope boundaries cannot use globs as concrete targets;
  - target scope cannot become permission to mutate targets inside `V78`;
  - product or external pressure cannot be granted as runtime execution
    authority;
  - local command output and passing tool results cannot become authority
    evidence;
  - exception rows cannot be resolved by prose only;
  - `V78-B` cannot emit `V78-C` readiness, handoff, or closeout surfaces;
- focused tests for the new `V78-B` surfaces and export-schema parity;
- no command execution, tool invocation, worker assignment, dispatch
  execution, product authorization, external branch activation, PR creation,
  commit, merge, release, benchmark truth, model selection, living-memory
  authority, or recursive policy amendment lands in this slice.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS219.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+219",
  "target_path": "V78-B",
  "slice": "V78-B",
  "family": "V78",
  "branch_local_execution_target": "arc/v78-r2",
  "target_scope": "one_bounded_runtime_execution_authority_decision_permission_scope_exception_starter_slice",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "api_surfaces": [],
  "cli_or_validation_entrypoints_for_v78b": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS218.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS218_EDGES.md"
  ],
  "selected_record_shapes": [
    "repo_runtime_execution_authority_decision@1",
    "repo_tool_use_permission_envelope@1",
    "repo_command_scope_authorization_boundary@1",
    "repo_runtime_authority_exception_register@1"
  ],
  "consumed_record_shapes": [
    "repo_runtime_execution_authority_request@1",
    "repo_runtime_authority_source_index@1",
    "repo_runtime_authority_non_action_guardrail@1"
  ],
  "must_not_select": [
    "V78-C",
    "runtime_authority_readiness_summary",
    "pre_execution_authority_review_handoff",
    "runtime_execution_authority_family_closeout_alignment",
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
    "recursive_policy_amendment",
    "later_family_selection"
  ],
  "local_gate": "make arc-start-check ARC=219"
}
```
