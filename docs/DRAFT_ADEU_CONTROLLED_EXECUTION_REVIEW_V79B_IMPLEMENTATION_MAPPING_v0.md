# Draft ADEU Controlled Execution Review V79-B Implementation Mapping v0

Status: support / slice implementation mapping for planned `V79-B`.

Authority layer: support.

This note does not authorize implementation by itself. It specifies the likely
second slice that a future lock may select only after `V79-A` has shipped and
lean-closed on `main`.

## Slice Intent

`V79-B` should add run-plan and invocation-plan review records over released
`V79-A` controlled-execution review requests:

- `repo_execution_run_plan@1`
- `repo_tool_invocation_plan@1`
- `repo_execution_effect_monitoring_contract@1`
- `repo_controlled_execution_exception_register@1`

The slice may describe bounded run plans and tool-invocation plans. It must
not run commands, invoke tools, assign workers, dispatch, mutate targets,
accept effects, observe telemetry, verify rollback, productize, activate
external branches, release, or select a later family.

## Expected Files

Implementation files:

- `packages/adeu_repo_description/src/adeu_repo_description/controlled_execution_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Schema files:

- `packages/adeu_repo_description/schema/repo_execution_run_plan.v1.json`
- `packages/adeu_repo_description/schema/repo_tool_invocation_plan.v1.json`
- `packages/adeu_repo_description/schema/repo_execution_effect_monitoring_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_controlled_execution_exception_register.v1.json`

Schema mirrors:

- `spec/repo_execution_run_plan.schema.json`
- `spec/repo_tool_invocation_plan.schema.json`
- `spec/repo_execution_effect_monitoring_contract.schema.json`
- `spec/repo_controlled_execution_exception_register.schema.json`

Tests:

- `packages/adeu_repo_description/tests/test_controlled_execution_review_v79b.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Fixtures:

- `apps/api/fixtures/repo_description/vnext_plus222/repo_execution_run_plan_v222_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus222/repo_tool_invocation_plan_v222_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus222/repo_execution_effect_monitoring_contract_v222_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus222/repo_controlled_execution_exception_register_v222_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus222/repo_controlled_execution_v222_reject_*.json`

## Source Basis

Required concrete source rows should cover:

- released `V79-A` controlled execution review request fixture;
- released `V79-A` source index fixture;
- released `V79-A` non-execution guardrail fixture;
- `V79-A` closeout evidence when available;
- relevant `V78-B` command-scope, tool-permission, and exception refs as
  upstream review substrate.

Globs remain discovery context only. A run plan must use concrete target refs
or explicit no-target / blocked posture.

## Minimum Row Vocabulary

Minimum run plan row fields:

- `run_plan_ref`
- `candidate_ref`
- `source_refs`
- `execution_review_request_refs`
- `non_execution_guardrail_refs`
- `command_intent_kind`
- `target_boundary_refs`
- `target_resolution_kind`
- `authority_refs`
- `tool_invocation_plan_refs`
- `effect_monitoring_contract_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `operator_confirmation_requirement_refs`
- `exception_refs`
- `run_plan_posture`
- `plan_completeness_posture`
- `run_execution_status`
- `execution_posture`
- `limitation_note`

Minimum tool-invocation plan row fields:

- `tool_invocation_plan_ref`
- `candidate_ref`
- `source_refs`
- `execution_review_request_refs`
- `non_execution_guardrail_refs`
- `tool_id`
- `tool_target_refs`
- `tool_target_horizon`
- `permission_refs`
- `authority_refs`
- `effect_monitoring_contract_refs`
- `exception_refs`
- `tool_invocation_plan_posture`
- `plan_completeness_posture`
- `tool_invocation_status`
- `tool_invocation_posture`
- `limitation_note`

Minimum effect-monitoring contract row fields:

- `effect_monitoring_contract_ref`
- `candidate_ref`
- `source_refs`
- `run_plan_refs`
- `tool_invocation_plan_refs`
- `non_execution_guardrail_refs`
- `expected_effect_surface_refs`
- `forbidden_effect_surface_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `operator_confirmation_requirement_refs`
- `monitoring_posture`
- `effect_observation_posture`
- `limitation_note`

Minimum operator confirmation requirement row fields:

- `confirmation_requirement_ref`
- `candidate_ref`
- `required_confirmation_kind`
- `source_refs`
- `authority_refs`
- `confirmation_posture`
- `non_authorization_guardrail`
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

Minimum plan completeness posture:

- `incomplete_for_review`
- `complete_for_review_only`
- `blocked_by_missing_source`
- `blocked_by_missing_authority`
- `blocked_by_missing_target_boundary`
- `blocked_by_missing_monitoring`
- `blocked_by_missing_rollback`
- `future_family_only`

Minimum run execution status:

- `no_run_performed_by_v79`
- `run_requires_later_family`
- `run_forbidden_by_this_family`

Minimum tool invocation status:

- `no_tool_invocation_performed_by_v79`
- `invocation_requires_later_family`
- `invocation_forbidden_by_this_family`

## Validation Rules

Validators should enforce:

- all rows reference known `V79-A` request refs;
- run plans, tool plans, and monitoring contracts reference known source,
  authority, and non-execution guardrail rows;
- every reference row carries no-execution or no-tool-invocation posture;
- `complete_for_review_only` means complete for review only, not ready to run;
- run plans carry `run_execution_status = no_run_performed_by_v79`;
- tool-invocation plans carry
  `tool_invocation_status = no_tool_invocation_performed_by_v79`;
- `target_resolution_kind = bounded_package_surface_with_child_refs` requires
  concrete child refs;
- no glob target can become a concrete run boundary;
- effect-monitoring contracts cannot claim observed effects unless a prior
  authorized source artifact is cited;
- telemetry requirements cannot become telemetry success;
- rollback requirements cannot become rollback verification;
- operator confirmation requirement rows cannot become operator authorization;
- blocking exceptions cannot be marked resolved by `V79-B`;
- product and external authority gaps remain blockers or future-family-only.

## Mandatory Reject Fixtures

- run plan with unknown `V79-A` request ref;
- run plan that executes a command;
- run plan using a glob as concrete target boundary;
- command-scope boundary treated as target mutation authority;
- tool-invocation plan that invokes a tool;
- tool plan with global tool permission;
- monitoring contract claiming observed effect without prior authorized source;
- telemetry requirement treated as telemetry success;
- rollback requirement treated as rollback verification;
- operator confirmation requirement treated as operator authorization;
- blocking exception resolved by prose;
- product or external branch pressure converted into execution readiness;
- local command output treated as authority.

## Non-Selection

`V79-B` does not select `V79-C`, command execution, tool invocation, target
mutation, accepted effects, observed telemetry, verified rollback, worker
assignment, dispatch execution, product authorization, external branch
activation, PR creation, commit, merge, release, benchmark truth, model
selection, living-memory authority, recursive policy amendment, or any later
family.
