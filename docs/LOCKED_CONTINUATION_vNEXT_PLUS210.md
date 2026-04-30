# LOCKED_CONTINUATION_vNEXT_PLUS210

## Status

Bounded starter lock draft for `V75-B` (worker role capacity profile,
multi-worker assignment plan, worker IO contract, worker tool-applicability
matrix, and dispatch exception register).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative `V75-B`
implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `V75`
- slice: `V75-B`
- branch-local execution target: `arc/v75-r2`

## Purpose

Freeze the bounded `V75-B` starter slice so the repo can describe worker role
capacity, assignment planning, worker IO contracts, target-bound tool
applicability, and dispatch exceptions over released `V75-A` dispatch-review
request / source-index / non-execution guardrail rows without executing
dispatch.

`vNext+210` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_repo_description` package. It does not authorize
`V75-C` reconciliation or post-dispatch-review handoff, worker assignment,
command execution, runtime permission, product authorization, external contest
participation, PR creation, commit, merge, release, benchmark truth, model
selection, living-memory authority, or recursive policy amendment.

The active `V75-B` implementation may add its own schema, model, validator,
fixture, and test files under this lock. That implementation work is distinct
from runtime dispatch, worker execution, product workbench, external branch, or
release work. `V75-B` may plan roles, assignments, IO, tools, and exceptions;
it must not record that a worker was assigned, a command may run, a PR may be
opened, a product may be authorized, an external contest may be entered, or a
recursive policy amendment may be adopted.

## Instantiated Here

- `V75-B` instantiates one bounded dispatch orchestration-planning starter seam:
  - existing repo-owned package only:
    - `adeu_repo_description`
  - consumed released basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS209.md`
    - `docs/ASSESSMENT_vNEXT_PLUS209_EDGES.md`
    - `artifacts/agent_harness/v209/evidence_inputs/v75a_dispatch_review_evidence_v209.json`
    - released `V75-A` dispatch-review request, dispatch source index, and
      dispatch non-execution guardrail surfaces
    - `apps/api/fixtures/repo_description/vnext_plus209/repo_dispatch_review_request_v209_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus209/repo_dispatch_source_index_v209_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus209/repo_dispatch_non_execution_guardrail_v209_reference.json`
  - consumed support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v65.md`
    - `docs/ARCHITECTURE_ADEU_DISPATCH_REVIEW_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/arc_series_mapping/REVIEW_GPTPRO_DISPATCH_REVIEW_V75_PLANNING_v0.md`
  - emitted starter record shapes:
    - `repo_worker_role_capacity_profile@1`
    - `repo_multi_worker_assignment_plan@1`
    - `repo_worker_io_contract@1`
    - `repo_worker_tool_applicability_matrix@1`
    - `repo_dispatch_exception_register@1`
  - consumed `V75-A` record shapes:
    - `repo_dispatch_review_request@1`
    - `repo_dispatch_source_index@1`
    - `repo_dispatch_non_execution_guardrail@1`

## Required Starter Vocabulary

Minimum worker role kinds:

- `source_index_worker`
- `evidence_review_worker`
- `adversarial_review_worker`
- `schema_validation_worker`
- `tool_run_worker`
- `reconciliation_worker`
- `operator_projection_worker`
- `external_branch_review_worker`

Minimum tool-use posture:

- `applicability_record_only`
- `tool_use_requires_later_runtime_permission`
- `tool_use_not_authorized_by_v75`

Minimum assignment plan posture:

- `plan_ready_for_review`
- `blocked_by_missing_role_profile`
- `blocked_by_missing_io_contract`
- `blocked_by_tool_applicability_gap`
- `blocked_by_unresolved_exception`
- `blocked_by_later_authority`
- `future_family_only`
- `rejected_out_of_scope`

Minimum assignment execution posture:

- `no_execution_authorized`
- `review_plan_only`
- `blocked_pending_later_authority`

Reference rows must use `assignment_execution_posture =
no_execution_authorized`.

Minimum output authority posture:

- `output_for_review_only`
- `output_requires_reconciliation`
- `output_requires_adversarial_review`
- `output_requires_human_ratification`
- `output_not_truth`

Minimum tool applicability posture:

- `applicable_for_target_horizon`
- `blocked_by_missing_source`
- `blocked_by_missing_tool_evidence`
- `not_applicable_for_target_horizon`
- `requires_negative_control`
- `requires_human_review`
- `unknown_needs_review`

Minimum dispatch exception kind:

- `missing_dispatch_source`
- `unresolved_projection_exception`
- `missing_role_profile`
- `missing_io_contract`
- `tool_applicability_gap`
- `required_later_authority_missing`
- `product_authority_gap`
- `runtime_authority_gap`
- `external_branch_boundary_gap`
- `worker_output_truth_gap`
- `unknown_needs_review`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `repo_worker_role_capacity_profile@1`
  - `repo_multi_worker_assignment_plan@1`
  - `repo_worker_io_contract@1`
  - `repo_worker_tool_applicability_matrix@1`
  - `repo_dispatch_exception_register@1`
- deterministic reference and reject fixtures for the bounded `V75-B` starter
  family only
- a hand-curated reference fixture seeded from released `V75-A` request,
  source-index, and guardrail fixture material
- validators that prove:
  - assignment plans reference released `V75-A` dispatch request rows
  - assignment plans reference released `V75-A` non-execution guardrails
  - worker role profiles have forbidden action kinds
  - `allowed_tool_ids` cannot become tool-run permission
  - worker IO outputs remain review-only and non-truth
  - tool applicability is target-bound and horizon-bound
  - assignment plans have `assignment_execution_posture =
    no_execution_authorized`
  - upstream exceptions are carried into a native exception register or marked
    not applicable with source evidence
  - external branch review worker plans remain blocked or future-family-only
    unless `V43` branch posture source refs are present
  - no row creates command execution, PR creation, commit, merge, release,
    product authorization, runtime permission, external contest participation,
    benchmark truth, model selection, living-memory authority, or recursive
    policy amendment
- tests that prove:
  - assignment plan without released `V75-A` request refs is rejected
  - assignment plan treated as execution is rejected
  - role profile treated as permission is rejected
  - worker IO output treated as truth is rejected
  - tool applicability treated as global scope is rejected
  - plan missing upstream exception refs is rejected when upstream exceptions
    exist
  - plan missing required later authority refs is rejected
  - external branch worker planning without `V43` branch posture is rejected
  - exception row marked resolved by `V75-B` is rejected
- no `V75-C`, reconciliation plan, post-dispatch-review handoff, worker
  assignment, command execution, runtime permission, product authorization,
  PR creation, commit, merge, release, external contest participation,
  benchmark truth, model selection, living-memory authority, or recursive
  policy amendment lands in this slice.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS210.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+210",
  "target_path": "V75-B",
  "slice": "V75-B",
  "family": "V75",
  "branch_local_execution_target": "arc/v75-r2",
  "target_scope": "one_bounded_worker_role_assignment_io_tool_exception_planning_starter_slice",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "api_surfaces": [],
  "cli_or_validation_entrypoints_for_v75b": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS209.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS209_EDGES.md"
  ],
  "consumed_record_shapes": [
    "repo_dispatch_review_request@1",
    "repo_dispatch_source_index@1",
    "repo_dispatch_non_execution_guardrail@1"
  ],
  "selected_record_shapes": [
    "repo_worker_role_capacity_profile@1",
    "repo_multi_worker_assignment_plan@1",
    "repo_worker_io_contract@1",
    "repo_worker_tool_applicability_matrix@1",
    "repo_dispatch_exception_register@1"
  ],
  "deferred_record_shapes": [
    "repo_worker_output_reconciliation_plan@1",
    "repo_dispatch_reconciliation_contract@1",
    "repo_post_dispatch_review_handoff@1",
    "repo_dispatch_review_family_closeout_alignment@1"
  ],
  "forbidden_authority_claims": [
    "worker_assignment",
    "command_execution",
    "runtime_permission",
    "product_authorization",
    "external_contest_participation",
    "pr_creation",
    "commit",
    "merge",
    "release",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment"
  ],
  "required_local_gate": "make check",
  "docs_only_start_gate": "make arc-start-check ARC=210"
}
```

## Recommended Implementation Scope

- `packages/adeu_repo_description/src/adeu_repo_description/dispatch_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- package-local and mirrored schemas for the five selected `V75-B` surfaces
- `packages/adeu_repo_description/tests/test_dispatch_review_v75b.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus210/` reference and reject
  fixtures
